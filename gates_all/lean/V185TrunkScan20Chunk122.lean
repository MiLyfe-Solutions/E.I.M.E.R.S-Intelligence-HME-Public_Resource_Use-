import V185TrunkScan20Chunk121

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_740896 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 3]
def baseStart_740896 : Nat := 118140960795 + 740896 * 2 ^ 59
def prefixEnd_740896 : Nat := 4983230072969 + 3 ^ 40 * 740896 * 2
def baseEnd_740896 : Nat := 338165122661011977504611

theorem tailTrace_740896 : CollatzResearch.WordTrace tailWord_740896 prefixEnd_740896 338165122661011977504611 := by
  unfold tailWord_740896
  simp only [CollatzResearch.WordTrace]
  refine ⟨13511348561933900903973271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18015131415911867871964361 13511348561933900903973271)
  ·
    refine ⟨20267022842900851355959907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13511348561933900903973271 20267022842900851355959907)
    ·
      refine ⟨30400534264351277033939861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20267022842900851355959907 30400534264351277033939861)
      ·
        refine ⟨1425025043641466110965931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30400534264351277033939861 1425025043641466110965931)
        ·
          refine ⟨2137537565462199166448897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1425025043641466110965931 2137537565462199166448897)
          ·
            refine ⟨1603153174096649374836673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2137537565462199166448897 1603153174096649374836673)
            ·
              refine ⟨1202364880572487031127505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603153174096649374836673 1202364880572487031127505)
              ·
                refine ⟨901773660429365273345629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1202364880572487031127505 901773660429365273345629)
                ·
                  refine ⟨338165122661011977504611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901773660429365273345629 338165122661011977504611)
                  ·
                    rfl

theorem cell20_740896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_740896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740896 prefixEnd_740896 := by exact prefixLift 740896
  have htrace : WordTrace (prefixWord ++ tailWord_740896) baseStart_740896 baseEnd_740896 := by
    simpa [prefixWord, tailWord_740896, baseEnd_740896] using wordTrace_append hprefix tailTrace_740896
  have hstable : (prefixWord ++ tailWord_740896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740896).length < 2 ^ (prefixWord ++ tailWord_740896).sum := by decide
  have hdescent : baseEnd_740896 < baseStart_740896 := by decide
  rcases family_descends (prefixWord ++ tailWord_740896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740899 : List Nat := [1, 1, 1, 4, 5, 2, 2, 2, 2]
def baseStart_740899 : Nat := 118140960795 + 740899 * 2 ^ 59
def prefixEnd_740899 : Nat := 4983230072969 + 3 ^ 40 * 740899 * 2
def baseEnd_740899 : Nat := 338166491942757300404599

theorem tailTrace_740899 : CollatzResearch.WordTrace tailWord_740899 prefixEnd_740899 338166491942757300404599 := by
  unfold tailWord_740899
  simp only [CollatzResearch.WordTrace]
  refine ⟨27022806542856933320305751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18015204361904622213537167 27022806542856933320305751)
  ·
    refine ⟨40534209814285399980458627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27022806542856933320305751 40534209814285399980458627)
    ·
      refine ⟨60801314721428099970687941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40534209814285399980458627 60801314721428099970687941)
      ·
        refine ⟨11400246510267768744503989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60801314721428099970687941 11400246510267768744503989)
        ·
          refine ⟨1068773110337603319797249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11400246510267768744503989 1068773110337603319797249)
          ·
            refine ⟨801579832753202489847937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068773110337603319797249 801579832753202489847937)
            ·
              refine ⟨601184874564901867385953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801579832753202489847937 601184874564901867385953)
              ·
                refine ⟨450888655923676400539465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601184874564901867385953 450888655923676400539465)
                ·
                  refine ⟨338166491942757300404599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450888655923676400539465 338166491942757300404599)
                  ·
                    rfl

theorem cell20_740899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 2].length) (baseStart_740899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740899 prefixEnd_740899 := by exact prefixLift 740899
  have htrace : WordTrace (prefixWord ++ tailWord_740899) baseStart_740899 baseEnd_740899 := by
    simpa [prefixWord, tailWord_740899, baseEnd_740899] using wordTrace_append hprefix tailTrace_740899
  have hstable : (prefixWord ++ tailWord_740899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740899).length < 2 ^ (prefixWord ++ tailWord_740899).sum := by decide
  have hdescent : baseEnd_740899 < baseStart_740899 := by decide
  rcases family_descends (prefixWord ++ tailWord_740899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740910 : List Nat := [4, 1, 3, 1, 2, 1, 3, 5]
def baseStart_740910 : Nat := 118140960795 + 740910 * 2 ^ 59
def prefixEnd_740910 : Nat := 4983230072969 + 3 ^ 40 * 740910 * 2
def baseEnd_740910 : Nat := 112723837547496717012629

theorem tailTrace_740910 : CollatzResearch.WordTrace tailWord_740910 prefixEnd_740910 112723837547496717012629 := by
  unfold tailWord_740910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377900968227135274869523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18015471830544721465970789 3377900968227135274869523)
  ·
    refine ⟨5066851452340702912304285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3377900968227135274869523 5066851452340702912304285)
    ·
      refine ⟨1900069294627763592114107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5066851452340702912304285 1900069294627763592114107)
      ·
        refine ⟨2850103941941645388171161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900069294627763592114107 2850103941941645388171161)
        ·
          refine ⟨2137577956456234041128371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2850103941941645388171161 2137577956456234041128371)
          ·
            refine ⟨3206366934684351061692557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137577956456234041128371 3206366934684351061692557)
            ·
              refine ⟨1202387600506631648134709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3206366934684351061692557 1202387600506631648134709)
              ·
                refine ⟨112723837547496717012629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1202387600506631648134709 112723837547496717012629)
                ·
                  rfl

theorem cell20_740910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_740910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740910 prefixEnd_740910 := by exact prefixLift 740910
  have htrace : WordTrace (prefixWord ++ tailWord_740910) baseStart_740910 baseEnd_740910 := by
    simpa [prefixWord, tailWord_740910, baseEnd_740910] using wordTrace_append hprefix tailTrace_740910
  have hstable : (prefixWord ++ tailWord_740910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740910).length < 2 ^ (prefixWord ++ tailWord_740910).sum := by decide
  have hdescent : baseEnd_740910 < baseStart_740910 := by decide
  rcases family_descends (prefixWord ++ tailWord_740910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740917 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 3]
def baseStart_740917 : Nat := 118140960795 + 740917 * 2 ^ 59
def prefixEnd_740917 : Nat := 4983230072969 + 3 ^ 40 * 740917 * 2
def baseEnd_740917 : Nat := 338174707633229237804525

theorem tailTrace_740917 : CollatzResearch.WordTrace tailWord_740917 prefixEnd_740917 338174707633229237804525 := by
  unfold tailWord_740917
  simp only [CollatzResearch.WordTrace]
  refine ⟨27023463056791722394461005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18015642037861148262974003 27023463056791722394461005)
  ·
    refine ⟨10133798646296895897922877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27023463056791722394461005 10133798646296895897922877)
    ·
      refine ⟨3800174492361335961721079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10133798646296895897922877 3800174492361335961721079)
      ·
        refine ⟨5700261738542003942581619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3800174492361335961721079 5700261738542003942581619)
        ·
          refine ⟨8550392607813005913872429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5700261738542003942581619 8550392607813005913872429)
          ·
            refine ⟨3206397227929877217702161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8550392607813005913872429 3206397227929877217702161)
            ·
              refine ⟨2404797920947407913276621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3206397227929877217702161 2404797920947407913276621)
              ·
                refine ⟨901799220355277967478733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2404797920947407913276621 901799220355277967478733)
                ·
                  refine ⟨338174707633229237804525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901799220355277967478733 338174707633229237804525)
                  ·
                    rfl

theorem cell20_740917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_740917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740917 prefixEnd_740917 := by exact prefixLift 740917
  have htrace : WordTrace (prefixWord ++ tailWord_740917) baseStart_740917 baseEnd_740917 := by
    simpa [prefixWord, tailWord_740917, baseEnd_740917] using wordTrace_append hprefix tailTrace_740917
  have hstable : (prefixWord ++ tailWord_740917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740917).length < 2 ^ (prefixWord ++ tailWord_740917).sum := by decide
  have hdescent : baseEnd_740917 < baseStart_740917 := by decide
  rcases family_descends (prefixWord ++ tailWord_740917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740938 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_740938 : Nat := 118140960795 + 740938 * 2 ^ 59
def prefixEnd_740938 : Nat := 4983230072969 + 3 ^ 40 * 740938 * 2
def baseEnd_740938 : Nat := 338184292605446498104439

theorem tailTrace_740938 : CollatzResearch.WordTrace tailWord_740938 prefixEnd_740938 338184292605446498104439 := by
  unfold tailWord_740938
  simp only [CollatzResearch.WordTrace]
  refine ⟨6756057247428910745243867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18016152659810428653983645 6756057247428910745243867)
  ·
    refine ⟨10134085871143366117865801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6756057247428910745243867 10134085871143366117865801)
    ·
      refine ⟨7600564403357524588399351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10134085871143366117865801 7600564403357524588399351)
      ·
        refine ⟨11400846605036286882599027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7600564403357524588399351 11400846605036286882599027)
        ·
          refine ⟨17101269907554430323898541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11400846605036286882599027 17101269907554430323898541)
          ·
            refine ⟨6412976215332911371461953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17101269907554430323898541 6412976215332911371461953)
            ·
              refine ⟨4809732161499683528596465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6412976215332911371461953 4809732161499683528596465)
              ·
                refine ⟨3607299121124762646447349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4809732161499683528596465 3607299121124762646447349)
                ·
                  refine ⟨338184292605446498104439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3607299121124762646447349 338184292605446498104439)
                  ·
                    rfl

theorem cell20_740938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_740938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740938 prefixEnd_740938 := by exact prefixLift 740938
  have htrace : WordTrace (prefixWord ++ tailWord_740938) baseStart_740938 baseEnd_740938 := by
    simpa [prefixWord, tailWord_740938, baseEnd_740938] using wordTrace_append hprefix tailTrace_740938
  have hstable : (prefixWord ++ tailWord_740938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740938).length < 2 ^ (prefixWord ++ tailWord_740938).sum := by decide
  have hdescent : baseEnd_740938 < baseStart_740938 := by decide
  rcases family_descends (prefixWord ++ tailWord_740938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740945 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_740945 : Nat := 118140960795 + 740945 * 2 ^ 59
def prefixEnd_740945 : Nat := 4983230072969 + 3 ^ 40 * 740945 * 2
def baseEnd_740945 : Nat := 338187487596185584871077

theorem tailTrace_740945 : CollatzResearch.WordTrace tailWord_740945 prefixEnd_740945 338187487596185584871077 := by
  unfold tailWord_740945
  simp only [CollatzResearch.WordTrace]
  refine ⟨27024484300690283176480289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18016322867126855450986859 27024484300690283176480289)
  ·
    refine ⟨20268363225517712382360217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27024484300690283176480289 20268363225517712382360217)
    ·
      refine ⟨15201272419138284286770163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20268363225517712382360217 15201272419138284286770163)
      ·
        refine ⟨22801908628707426430155245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15201272419138284286770163 22801908628707426430155245)
        ·
          refine ⟨8550715735765284911308217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22801908628707426430155245 8550715735765284911308217)
          ·
            refine ⟨6413036801823963683481163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8550715735765284911308217 6413036801823963683481163)
            ·
              refine ⟨9619555202735945525221745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6413036801823963683481163 9619555202735945525221745)
              ·
                refine ⟨7214666402051959143916309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9619555202735945525221745 7214666402051959143916309)
                ·
                  refine ⟨338187487596185584871077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7214666402051959143916309 338187487596185584871077)
                  ·
                    rfl

theorem cell20_740945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_740945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740945 prefixEnd_740945 := by exact prefixLift 740945
  have htrace : WordTrace (prefixWord ++ tailWord_740945) baseStart_740945 baseEnd_740945 := by
    simpa [prefixWord, tailWord_740945, baseEnd_740945] using wordTrace_append hprefix tailTrace_740945
  have hstable : (prefixWord ++ tailWord_740945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740945).length < 2 ^ (prefixWord ++ tailWord_740945).sum := by decide
  have hdescent : baseEnd_740945 < baseStart_740945 := by decide
  rcases family_descends (prefixWord ++ tailWord_740945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741058 : List Nat := [3, 5, 1, 2, 2, 7]
def baseStart_741058 : Nat := 118140960795 + 741058 * 2 ^ 59
def prefixEnd_741058 : Nat := 4983230072969 + 3 ^ 40 * 741058 * 2
def baseEnd_741058 : Nat := 12527372736120719040887

theorem tailTrace_741058 : CollatzResearch.WordTrace tailWord_741058 prefixEnd_741058 12527372736120719040887 := by
  unfold tailWord_741058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6757151437320225868835957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18019070499520602316895885 6757151437320225868835957)
  ·
    refine ⟨633482947248771175203371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6757151437320225868835957 633482947248771175203371)
    ·
      refine ⟨950224420873156762805057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633482947248771175203371 950224420873156762805057)
      ·
        refine ⟨712668315654867572103793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 950224420873156762805057 712668315654867572103793)
        ·
          refine ⟨534501236741150679077845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712668315654867572103793 534501236741150679077845)
          ·
            refine ⟨12527372736120719040887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 534501236741150679077845 12527372736120719040887)
            ·
              rfl

theorem cell20_741058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 7].length) (baseStart_741058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741058 prefixEnd_741058 := by exact prefixLift 741058
  have htrace : WordTrace (prefixWord ++ tailWord_741058) baseStart_741058 baseEnd_741058 := by
    simpa [prefixWord, tailWord_741058, baseEnd_741058] using wordTrace_append hprefix tailTrace_741058
  have hstable : (prefixWord ++ tailWord_741058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741058).length < 2 ^ (prefixWord ++ tailWord_741058).sum := by decide
  have hdescent : baseEnd_741058 < baseStart_741058 := by decide
  rcases family_descends (prefixWord ++ tailWord_741058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741066 : List Nat := [3, 1, 2, 1, 13]
def baseStart_741066 : Nat := 118140960795 + 741066 * 2 ^ 59
def prefixEnd_741066 : Nat := 4983230072969 + 3 ^ 40 * 741066 * 2
def baseEnd_741066 : Nat := 4175835991274653602929

theorem tailTrace_741066 : CollatzResearch.WordTrace tailWord_741066 prefixEnd_741066 4175835991274653602929 := by
  unfold tailWord_741066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6757224383312980210408763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18019265022167947227756701 6757224383312980210408763)
  ·
    refine ⟨10135836574969470315613145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6757224383312980210408763 10135836574969470315613145)
    ·
      refine ⟨7601877431227102736709859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10135836574969470315613145 7601877431227102736709859)
      ·
        refine ⟨11402816146840654105064789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7601877431227102736709859 11402816146840654105064789)
        ·
          refine ⟨4175835991274653602929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11402816146840654105064789 4175835991274653602929)
          ·
            rfl

theorem cell20_741066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 13].length) (baseStart_741066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741066 prefixEnd_741066 := by exact prefixLift 741066
  have htrace : WordTrace (prefixWord ++ tailWord_741066) baseStart_741066 baseEnd_741066 := by
    simpa [prefixWord, tailWord_741066, baseEnd_741066] using wordTrace_append hprefix tailTrace_741066
  have hstable : (prefixWord ++ tailWord_741066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741066).length < 2 ^ (prefixWord ++ tailWord_741066).sum := by decide
  have hdescent : baseEnd_741066 < baseStart_741066 := by decide
  rcases family_descends (prefixWord ++ tailWord_741066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741068 : List Nat := [2, 2, 1, 5, 3, 1, 2, 2, 2]
def baseStart_741068 : Nat := 118140960795 + 741068 * 2 ^ 59
def prefixEnd_741068 : Nat := 4983230072969 + 3 ^ 40 * 741068 * 2
def baseEnd_741068 : Nat := 338243628147743823770575

theorem tailTrace_741068 : CollatzResearch.WordTrace tailWord_741068 prefixEnd_741068 338243628147743823770575 := by
  unfold tailWord_741068
  simp only [CollatzResearch.WordTrace]
  refine ⟨13514485239622337591603929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18019313652829783455471905 13514485239622337591603929)
  ·
    refine ⟨10135863929716753193702947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13514485239622337591603929 10135863929716753193702947)
    ·
      refine ⟨15203795894575129790554421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10135863929716753193702947 15203795894575129790554421)
      ·
        refine ⟨1425355865116418417864477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15203795894575129790554421 1425355865116418417864477)
        ·
          refine ⟨534508449418656906699179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1425355865116418417864477 534508449418656906699179)
          ·
            refine ⟨801762674127985360048769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534508449418656906699179 801762674127985360048769)
            ·
              refine ⟨601322005595989020036577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801762674127985360048769 601322005595989020036577)
              ·
                refine ⟨450991504196991765027433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601322005595989020036577 450991504196991765027433)
                ·
                  refine ⟨338243628147743823770575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450991504196991765027433 338243628147743823770575)
                  ·
                    rfl

theorem cell20_741068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_741068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741068 prefixEnd_741068 := by exact prefixLift 741068
  have htrace : WordTrace (prefixWord ++ tailWord_741068) baseStart_741068 baseEnd_741068 := by
    simpa [prefixWord, tailWord_741068, baseEnd_741068] using wordTrace_append hprefix tailTrace_741068
  have hstable : (prefixWord ++ tailWord_741068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741068).length < 2 ^ (prefixWord ++ tailWord_741068).sum := by decide
  have hdescent : baseEnd_741068 < baseStart_741068 := by decide
  rcases family_descends (prefixWord ++ tailWord_741068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741110 : List Nat := [5, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_741110 : Nat := 118140960795 + 741110 * 2 ^ 59
def prefixEnd_741110 : Nat := 4983230072969 + 3 ^ 40 * 741110 * 2
def baseEnd_741110 : Nat := 338262798092178344370403

theorem tailTrace_741110 : CollatzResearch.WordTrace tailWord_741110 prefixEnd_741110 338262798092178344370403 := by
  unfold tailWord_741110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689406396568282272264799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18020334896728344237491189 1689406396568282272264799)
  ·
    refine ⟨2534109594852423408397199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1689406396568282272264799 2534109594852423408397199)
    ·
      refine ⟨3801164392278635112595799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2534109594852423408397199 3801164392278635112595799)
      ·
        refine ⟨5701746588417952668893699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801164392278635112595799 5701746588417952668893699)
        ·
          refine ⟨8552619882626929003340549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701746588417952668893699 8552619882626929003340549)
          ·
            refine ⟨1603616227992549188126353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8552619882626929003340549 1603616227992549188126353)
            ·
              refine ⟨1202712170994411891094765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603616227992549188126353 1202712170994411891094765)
              ·
                refine ⟨451017064122904459160537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1202712170994411891094765 451017064122904459160537)
                ·
                  refine ⟨338262798092178344370403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451017064122904459160537 338262798092178344370403)
                  ·
                    rfl

theorem cell20_741110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_741110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741110 prefixEnd_741110 := by exact prefixLift 741110
  have htrace : WordTrace (prefixWord ++ tailWord_741110) baseStart_741110 baseEnd_741110 := by
    simpa [prefixWord, tailWord_741110, baseEnd_741110] using wordTrace_append hprefix tailTrace_741110
  have hstable : (prefixWord ++ tailWord_741110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741110).length < 2 ^ (prefixWord ++ tailWord_741110).sum := by decide
  have hdescent : baseEnd_741110 < baseStart_741110 := by decide
  rcases family_descends (prefixWord ++ tailWord_741110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741124 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 3]
def baseStart_741124 : Nat := 118140960795 + 741124 * 2 ^ 59
def prefixEnd_741124 : Nat := 4983230072969 + 3 ^ 40 * 741124 * 2
def baseEnd_741124 : Nat := 338269188073656517903679

theorem tailTrace_741124 : CollatzResearch.WordTrace tailWord_741124 prefixEnd_741124 338269188073656517903679 := by
  unfold tailWord_741124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13515506483520898373623213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18020675311361197831497617 13515506483520898373623213)
  ·
    refine ⟨5068314931320336890108705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13515506483520898373623213 5068314931320336890108705)
    ·
      refine ⟨3801236198490252667581529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5068314931320336890108705 3801236198490252667581529)
      ·
        refine ⟨2850927148867689500686147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3801236198490252667581529 2850927148867689500686147)
        ·
          refine ⟨4276390723301534251029221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850927148867689500686147 4276390723301534251029221)
          ·
            refine ⟨801823260619037672067979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4276390723301534251029221 801823260619037672067979)
            ·
              refine ⟨1202734890928556508101969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801823260619037672067979 1202734890928556508101969)
              ·
                refine ⟨902051168196417381076477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1202734890928556508101969 902051168196417381076477)
                ·
                  refine ⟨338269188073656517903679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902051168196417381076477 338269188073656517903679)
                  ·
                    rfl

theorem cell20_741124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_741124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741124 prefixEnd_741124 := by exact prefixLift 741124
  have htrace : WordTrace (prefixWord ++ tailWord_741124) baseStart_741124 baseEnd_741124 := by
    simpa [prefixWord, tailWord_741124, baseEnd_741124] using wordTrace_append hprefix tailTrace_741124
  have hstable : (prefixWord ++ tailWord_741124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741124).length < 2 ^ (prefixWord ++ tailWord_741124).sum := by decide
  have hdescent : baseEnd_741124 < baseStart_741124 := by decide
  rcases family_descends (prefixWord ++ tailWord_741124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741128 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_741128 : Nat := 118140960795 + 741128 * 2 ^ 59
def prefixEnd_741128 : Nat := 4983230072969 + 3 ^ 40 * 741128 * 2
def baseEnd_741128 : Nat := 338271013782650281770329

theorem tailTrace_741128 : CollatzResearch.WordTrace tailWord_741128 prefixEnd_741128 338271013782650281770329 := by
  unfold tailWord_741128
  simp only [CollatzResearch.WordTrace]
  refine ⟨13515579429513652715196019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18020772572684870286928025 13515579429513652715196019)
  ·
    refine ⟨20273369144270479072794029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13515579429513652715196019 20273369144270479072794029)
    ·
      refine ⟨7602513429101429652297761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20273369144270479072794029 7602513429101429652297761)
      ·
        refine ⟨5701885071826072239223321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7602513429101429652297761 5701885071826072239223321)
        ·
          refine ⟨4276413803869554179417491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5701885071826072239223321 4276413803869554179417491)
          ·
            refine ⟨6414620705804331269126237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4276413803869554179417491 6414620705804331269126237)
            ·
              refine ⟨2405482764676624225922339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6414620705804331269126237 2405482764676624225922339)
              ·
                refine ⟨3608224147014936338883509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405482764676624225922339 3608224147014936338883509)
                ·
                  refine ⟨338271013782650281770329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3608224147014936338883509 338271013782650281770329)
                  ·
                    rfl

theorem cell20_741128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_741128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741128 prefixEnd_741128 := by exact prefixLift 741128
  have htrace : WordTrace (prefixWord ++ tailWord_741128) baseStart_741128 baseEnd_741128 := by
    simpa [prefixWord, tailWord_741128, baseEnd_741128] using wordTrace_append hprefix tailTrace_741128
  have hstable : (prefixWord ++ tailWord_741128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741128).length < 2 ^ (prefixWord ++ tailWord_741128).sum := by decide
  have hdescent : baseEnd_741128 < baseStart_741128 := by decide
  rcases family_descends (prefixWord ++ tailWord_741128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741169 : List Nat := [1, 2, 2, 3, 2, 2, 3, 3, 2]
def baseStart_741169 : Nat := 118140960795 + 741169 * 2 ^ 59
def prefixEnd_741169 : Nat := 4983230072969 + 3 ^ 40 * 741169 * 2
def baseEnd_741169 : Nat := 338289727299836361403495

theorem tailTrace_741169 : CollatzResearch.WordTrace tailWord_741169 prefixEnd_741169 338289727299836361403495 := by
  unfold tailWord_741169
  simp only [CollatzResearch.WordTrace]
  refine ⟨27032654251878769432634561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18021769501252512955089707 27032654251878769432634561)
  ·
    refine ⟨20274490688909077074475921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27032654251878769432634561 20274490688909077074475921)
    ·
      refine ⟨15205868016681807805856941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20274490688909077074475921 15205868016681807805856941)
      ·
        refine ⟨5702200506255677927196353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15205868016681807805856941 5702200506255677927196353)
        ·
          refine ⟨4276650379691758445397265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5702200506255677927196353 4276650379691758445397265)
          ·
            refine ⟨3207487784768818834047949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4276650379691758445397265 3207487784768818834047949)
            ·
              refine ⟨1202807919288307062767981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3207487784768818834047949 1202807919288307062767981)
              ·
                refine ⟨451052969733115148537993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1202807919288307062767981 451052969733115148537993)
                ·
                  refine ⟨338289727299836361403495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451052969733115148537993 338289727299836361403495)
                  ·
                    rfl

theorem cell20_741169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 2].length) (baseStart_741169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741169 prefixEnd_741169 := by exact prefixLift 741169
  have htrace : WordTrace (prefixWord ++ tailWord_741169) baseStart_741169 baseEnd_741169 := by
    simpa [prefixWord, tailWord_741169, baseEnd_741169] using wordTrace_append hprefix tailTrace_741169
  have hstable : (prefixWord ++ tailWord_741169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741169).length < 2 ^ (prefixWord ++ tailWord_741169).sum := by decide
  have hdescent : baseEnd_741169 < baseStart_741169 := by decide
  rcases family_descends (prefixWord ++ tailWord_741169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741180 : List Nat := [2, 2, 2, 2, 1, 1, 10]
def baseStart_741180 : Nat := 118140960795 + 741180 * 2 ^ 59
def prefixEnd_741180 : Nat := 4983230072969 + 3 ^ 40 * 741180 * 2
def baseEnd_741180 : Nat := 37588305333285468004087

theorem tailTrace_741180 : CollatzResearch.WordTrace tailWord_741180 prefixEnd_741180 37588305333285468004087 := by
  unfold tailWord_741180
  simp only [CollatzResearch.WordTrace]
  refine ⟨13516527727419459155642497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18022036969892612207523329 13516527727419459155642497)
  ·
    refine ⟨10137395795564594366731873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13516527727419459155642497 10137395795564594366731873)
    ·
      refine ⟨7603046846673445775048905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10137395795564594366731873 7603046846673445775048905)
      ·
        refine ⟨5702285135005084331286679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7603046846673445775048905 5702285135005084331286679)
        ·
          refine ⟨8553427702507626496930019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5702285135005084331286679 8553427702507626496930019)
          ·
            refine ⟨12830141553761439745395029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8553427702507626496930019 12830141553761439745395029)
            ·
              refine ⟨37588305333285468004087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12830141553761439745395029 37588305333285468004087)
              ·
                rfl

theorem cell20_741180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 10].length) (baseStart_741180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741180 prefixEnd_741180 := by exact prefixLift 741180
  have htrace : WordTrace (prefixWord ++ tailWord_741180) baseStart_741180 baseEnd_741180 := by
    simpa [prefixWord, tailWord_741180, baseEnd_741180] using wordTrace_append hprefix tailTrace_741180
  have hstable : (prefixWord ++ tailWord_741180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741180).length < 2 ^ (prefixWord ++ tailWord_741180).sum := by decide
  have hdescent : baseEnd_741180 < baseStart_741180 := by decide
  rcases family_descends (prefixWord ++ tailWord_741180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741225 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_741225 : Nat := 118140960795 + 741225 * 2 ^ 59
def prefixEnd_741225 : Nat := 4983230072969 + 3 ^ 40 * 741225 * 2
def baseEnd_741225 : Nat := 338315287225749055536599

theorem tailTrace_741225 : CollatzResearch.WordTrace tailWord_741225 prefixEnd_741225 338315287225749055536599 := by
  unfold tailWord_741225
  simp only [CollatzResearch.WordTrace]
  refine ⟨27034696739675890996673129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18023131159783927331115419 27034696739675890996673129)
  ·
    refine ⟨20276022554756918247504847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27034696739675890996673129 20276022554756918247504847)
    ·
      refine ⟨30414033832135377371257271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20276022554756918247504847 30414033832135377371257271)
      ·
        refine ⟨45621050748203066056885907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30414033832135377371257271 45621050748203066056885907)
        ·
          refine ⟨68431576122304599085328861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45621050748203066056885907 68431576122304599085328861)
          ·
            refine ⟨25661841045864224656998323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68431576122304599085328861 25661841045864224656998323)
            ·
              refine ⟨38492761568796336985497485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25661841045864224656998323 38492761568796336985497485)
              ·
                refine ⟨14434785588298626369561557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38492761568796336985497485 14434785588298626369561557)
                ·
                  refine ⟨338315287225749055536599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14434785588298626369561557 338315287225749055536599)
                  ·
                    rfl

theorem cell20_741225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_741225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741225 prefixEnd_741225 := by exact prefixLift 741225
  have htrace : WordTrace (prefixWord ++ tailWord_741225) baseStart_741225 baseEnd_741225 := by
    simpa [prefixWord, tailWord_741225, baseEnd_741225] using wordTrace_append hprefix tailTrace_741225
  have hstable : (prefixWord ++ tailWord_741225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741225).length < 2 ^ (prefixWord ++ tailWord_741225).sum := by decide
  have hdescent : baseEnd_741225 < baseStart_741225 := by decide
  rcases family_descends (prefixWord ++ tailWord_741225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741242 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_741242 : Nat := 118140960795 + 741242 * 2 ^ 59
def prefixEnd_741242 : Nat := 4983230072969 + 3 ^ 40 * 741242 * 2
def baseEnd_741242 : Nat := 338323046488972551969863

theorem tailTrace_741242 : CollatzResearch.WordTrace tailWord_741242 prefixEnd_741242 338323046488972551969863 := by
  unfold tailWord_741242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6758829195153575725010495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18023544520409535266694653 6758829195153575725010495)
  ·
    refine ⟨10138243792730363587515743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6758829195153575725010495 10138243792730363587515743)
    ·
      refine ⟨15207365689095545381273615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10138243792730363587515743 15207365689095545381273615)
      ·
        refine ⟨22811048533643318071910423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15207365689095545381273615 22811048533643318071910423)
        ·
          refine ⟨34216572800464977107865635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22811048533643318071910423 34216572800464977107865635)
          ·
            refine ⟨51324859200697465661798453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34216572800464977107865635 51324859200697465661798453)
            ·
              refine ⟨4811705550065387405793605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51324859200697465661798453 4811705550065387405793605)
              ·
                refine ⟨902194790637260138586301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4811705550065387405793605 902194790637260138586301)
                ·
                  refine ⟨338323046488972551969863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902194790637260138586301 338323046488972551969863)
                  ·
                    rfl

theorem cell20_741242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_741242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741242 prefixEnd_741242 := by exact prefixLift 741242
  have htrace : WordTrace (prefixWord ++ tailWord_741242) baseStart_741242 baseEnd_741242 := by
    simpa [prefixWord, tailWord_741242, baseEnd_741242] using wordTrace_append hprefix tailTrace_741242
  have hstable : (prefixWord ++ tailWord_741242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741242).length < 2 ^ (prefixWord ++ tailWord_741242).sum := by decide
  have hdescent : baseEnd_741242 < baseStart_741242 := by decide
  rcases family_descends (prefixWord ++ tailWord_741242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741266 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_741266 : Nat := 118140960795 + 741266 * 2 ^ 59
def prefixEnd_741266 : Nat := 4983230072969 + 3 ^ 40 * 741266 * 2
def baseEnd_741266 : Nat := 338334000742935135169765

theorem tailTrace_741266 : CollatzResearch.WordTrace tailWord_741266 prefixEnd_741266 338334000742935135169765 := by
  unfold tailWord_741266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6759048033131838749728913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18024128088351569999277101 6759048033131838749728913)
  ·
    refine ⟨5069286024848879062296685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6759048033131838749728913 5069286024848879062296685)
    ·
      refine ⟨1900982259318329648361257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5069286024848879062296685 1900982259318329648361257)
      ·
        refine ⟨1425736694488747236270943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1900982259318329648361257 1425736694488747236270943)
        ·
          refine ⟨2138605041733120854406415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1425736694488747236270943 2138605041733120854406415)
          ·
            refine ⟨3207907562599681281609623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138605041733120854406415 3207907562599681281609623)
            ·
              refine ⟨4811861343899521922414435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207907562599681281609623 4811861343899521922414435)
              ·
                refine ⟨7217792015849282883621653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4811861343899521922414435 7217792015849282883621653)
                ·
                  refine ⟨338334000742935135169765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7217792015849282883621653 338334000742935135169765)
                  ·
                    rfl

theorem cell20_741266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_741266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741266 prefixEnd_741266 := by exact prefixLift 741266
  have htrace : WordTrace (prefixWord ++ tailWord_741266) baseStart_741266 baseEnd_741266 := by
    simpa [prefixWord, tailWord_741266, baseEnd_741266] using wordTrace_append hprefix tailTrace_741266
  have hstable : (prefixWord ++ tailWord_741266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741266).length < 2 ^ (prefixWord ++ tailWord_741266).sum := by decide
  have hdescent : baseEnd_741266 < baseStart_741266 := by decide
  rcases family_descends (prefixWord ++ tailWord_741266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741297 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 3]
def baseStart_741297 : Nat := 118140960795 + 741297 * 2 ^ 59
def prefixEnd_741297 : Nat := 4983230072969 + 3 ^ 40 * 741297 * 2
def baseEnd_741297 : Nat := 338348149987636805136305

theorem tailTrace_741297 : CollatzResearch.WordTrace tailWord_741297 prefixEnd_741297 338348149987636805136305 := by
  unfold tailWord_741297
  simp only [CollatzResearch.WordTrace]
  refine ⟨27037322795415047293294145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18024881863610031528862763 27037322795415047293294145)
  ·
    refine ⟨20277992096561285469970609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27037322795415047293294145 20277992096561285469970609)
    ·
      refine ⟨15208494072420964102477957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20277992096561285469970609 15208494072420964102477957)
      ·
        refine ⟨2851592638578930769214617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15208494072420964102477957 2851592638578930769214617)
        ·
          refine ⟨2138694478934198076910963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2851592638578930769214617 2138694478934198076910963)
          ·
            refine ⟨3208041718401297115366445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138694478934198076910963 3208041718401297115366445)
            ·
              refine ⟨1203015644400486418262417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3208041718401297115366445 1203015644400486418262417)
              ·
                refine ⟨902261733300364813696813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203015644400486418262417 902261733300364813696813)
                ·
                  refine ⟨338348149987636805136305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902261733300364813696813 338348149987636805136305)
                  ·
                    rfl

theorem cell20_741297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_741297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741297 prefixEnd_741297 := by exact prefixLift 741297
  have htrace : WordTrace (prefixWord ++ tailWord_741297) baseStart_741297 baseEnd_741297 := by
    simpa [prefixWord, tailWord_741297, baseEnd_741297] using wordTrace_append hprefix tailTrace_741297
  have hstable : (prefixWord ++ tailWord_741297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741297).length < 2 ^ (prefixWord ++ tailWord_741297).sum := by decide
  have hdescent : baseEnd_741297 < baseStart_741297 := by decide
  rcases family_descends (prefixWord ++ tailWord_741297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741300 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 4]
def baseStart_741300 : Nat := 118140960795 + 741300 * 2 ^ 59
def prefixEnd_741300 : Nat := 4983230072969 + 3 ^ 40 * 741300 * 2
def baseEnd_741300 : Nat := 338349519269382128036293

theorem tailTrace_741300 : CollatzResearch.WordTrace tailWord_741300 prefixEnd_741300 338349519269382128036293 := by
  unfold tailWord_741300
  simp only [CollatzResearch.WordTrace]
  refine ⟨13518716107202089402826677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18024954809602785870435569 13518716107202089402826677)
  ·
    refine ⟨1267379635050195881515001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13518716107202089402826677 1267379635050195881515001)
    ·
      refine ⟨950534726287646911136251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1267379635050195881515001 950534726287646911136251)
      ·
        refine ⟨1425802089431470366704377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950534726287646911136251 1425802089431470366704377)
        ·
          refine ⟨1069351567073602775028283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1425802089431470366704377 1069351567073602775028283)
          ·
            refine ⟨1604027350610404162542425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069351567073602775028283 1604027350610404162542425)
            ·
              refine ⟨1203020512957803121906819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604027350610404162542425 1203020512957803121906819)
              ·
                refine ⟨1804530769436704682860229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203020512957803121906819 1804530769436704682860229)
                ·
                  refine ⟨338349519269382128036293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1804530769436704682860229 338349519269382128036293)
                  ·
                    rfl

theorem cell20_741300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_741300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741300 prefixEnd_741300 := by exact prefixLift 741300
  have htrace : WordTrace (prefixWord ++ tailWord_741300) baseStart_741300 baseEnd_741300 := by
    simpa [prefixWord, tailWord_741300, baseEnd_741300] using wordTrace_append hprefix tailTrace_741300
  have hstable : (prefixWord ++ tailWord_741300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741300).length < 2 ^ (prefixWord ++ tailWord_741300).sum := by decide
  have hdescent : baseEnd_741300 < baseStart_741300 := by decide
  rcases family_descends (prefixWord ++ tailWord_741300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741304 : List Nat := [2, 1, 2, 1, 2, 3, 1, 6, 2]
def baseStart_741304 : Nat := 118140960795 + 741304 * 2 ^ 59
def prefixEnd_741304 : Nat := 4983230072969 + 3 ^ 40 * 741304 * 2
def baseEnd_741304 : Nat := 338351344978375891902943

theorem tailTrace_741304 : CollatzResearch.WordTrace tailWord_741304 prefixEnd_741304 338351344978375891902943 := by
  unfold tailWord_741304
  simp only [CollatzResearch.WordTrace]
  refine ⟨13518789053194843744399483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18025052070926458325865977 13518789053194843744399483)
  ·
    refine ⟨20278183579792265616599225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13518789053194843744399483 20278183579792265616599225)
    ·
      refine ⟨15208637684844199212449419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20278183579792265616599225 15208637684844199212449419)
      ·
        refine ⟨22812956527266298818674129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15208637684844199212449419 22812956527266298818674129)
        ·
          refine ⟨17109717395449724114005597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22812956527266298818674129 17109717395449724114005597)
          ·
            refine ⟨6416144023293646542752099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17109717395449724114005597 6416144023293646542752099)
            ·
              refine ⟨9624216034940469814128149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6416144023293646542752099 9624216034940469814128149)
              ·
                refine ⟨451135126637834522537257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9624216034940469814128149 451135126637834522537257)
                ·
                  refine ⟨338351344978375891902943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451135126637834522537257 338351344978375891902943)
                  ·
                    rfl

theorem cell20_741304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 2].length) (baseStart_741304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741304 prefixEnd_741304 := by exact prefixLift 741304
  have htrace : WordTrace (prefixWord ++ tailWord_741304) baseStart_741304 baseEnd_741304 := by
    simpa [prefixWord, tailWord_741304, baseEnd_741304] using wordTrace_append hprefix tailTrace_741304
  have hstable : (prefixWord ++ tailWord_741304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741304).length < 2 ^ (prefixWord ++ tailWord_741304).sum := by decide
  have hdescent : baseEnd_741304 < baseStart_741304 := by decide
  rcases family_descends (prefixWord ++ tailWord_741304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741334 : List Nat := [5, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_741334 : Nat := 118140960795 + 741334 * 2 ^ 59
def prefixEnd_741334 : Nat := 4983230072969 + 3 ^ 40 * 741334 * 2
def baseEnd_741334 : Nat := 338365037795829120902821

theorem tailTrace_741334 : CollatzResearch.WordTrace tailWord_741334 prefixEnd_741334 338365037795829120902821 := by
  unfold tailWord_741334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689917018517562663274441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18025781530854001741594037 1689917018517562663274441)
  ·
    refine ⟨1267437763888171997455831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1689917018517562663274441 1267437763888171997455831)
    ·
      refine ⟨1901156645832257996183747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1267437763888171997455831 1901156645832257996183747)
      ·
        refine ⟨2851734968748386994275621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901156645832257996183747 2851734968748386994275621)
        ·
          refine ⟨534700306640322561426679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2851734968748386994275621 534700306640322561426679)
          ·
            refine ⟨802050459960483842140019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534700306640322561426679 802050459960483842140019)
            ·
              refine ⟨1203075689940725763210029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802050459960483842140019 1203075689940725763210029)
              ·
                refine ⟨451153383727772161203761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1203075689940725763210029 451153383727772161203761)
                ·
                  refine ⟨338365037795829120902821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451153383727772161203761 338365037795829120902821)
                  ·
                    rfl

theorem cell20_741334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_741334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741334 prefixEnd_741334 := by exact prefixLift 741334
  have htrace : WordTrace (prefixWord ++ tailWord_741334) baseStart_741334 baseEnd_741334 := by
    simpa [prefixWord, tailWord_741334, baseEnd_741334] using wordTrace_append hprefix tailTrace_741334
  have hstable : (prefixWord ++ tailWord_741334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741334).length < 2 ^ (prefixWord ++ tailWord_741334).sum := by decide
  have hdescent : baseEnd_741334 < baseStart_741334 := by decide
  rcases family_descends (prefixWord ++ tailWord_741334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741338 : List Nat := [3, 1, 1, 2, 5, 2, 1, 3, 2]
def baseStart_741338 : Nat := 118140960795 + 741338 * 2 ^ 59
def prefixEnd_741338 : Nat := 4983230072969 + 3 ^ 40 * 741338 * 2
def baseEnd_741338 : Nat := 338366863504822884769471

theorem tailTrace_741338 : CollatzResearch.WordTrace tailWord_741338 prefixEnd_741338 338366863504822884769471 := by
  unfold tailWord_741338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6759704547066627823884167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18025878792177674197024445 6759704547066627823884167)
  ·
    refine ⟨10139556820599941735826251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6759704547066627823884167 10139556820599941735826251)
    ·
      refine ⟨15209335230899912603739377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10139556820599941735826251 15209335230899912603739377)
      ·
        refine ⟨11407001423174934452804533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15209335230899912603739377 11407001423174934452804533)
        ·
          refine ⟨1069406383422650104950425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11407001423174934452804533 1069406383422650104950425)
          ·
            refine ⟨802054787566987578712819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1069406383422650104950425 802054787566987578712819)
            ·
              refine ⟨1203082181350481368069229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802054787566987578712819 1203082181350481368069229)
              ·
                refine ⟨451155818006430513025961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1203082181350481368069229 451155818006430513025961)
                ·
                  refine ⟨338366863504822884769471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451155818006430513025961 338366863504822884769471)
                  ·
                    rfl

theorem cell20_741338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_741338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741338 prefixEnd_741338 := by exact prefixLift 741338
  have htrace : WordTrace (prefixWord ++ tailWord_741338) baseStart_741338 baseEnd_741338 := by
    simpa [prefixWord, tailWord_741338, baseEnd_741338] using wordTrace_append hprefix tailTrace_741338
  have hstable : (prefixWord ++ tailWord_741338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741338).length < 2 ^ (prefixWord ++ tailWord_741338).sum := by decide
  have hdescent : baseEnd_741338 < baseStart_741338 := by decide
  rcases family_descends (prefixWord ++ tailWord_741338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741359 : List Nat := [1, 1, 2, 1, 4, 2, 5, 2, 2]
def baseStart_741359 : Nat := 118140960795 + 741359 * 2 ^ 59
def prefixEnd_741359 : Nat := 4983230072969 + 3 ^ 40 * 741359 * 2
def baseEnd_741359 : Nat := 338376448477040145069385

theorem tailTrace_741359 : CollatzResearch.WordTrace tailWord_741359 prefixEnd_741359 338376448477040145069385 := by
  unfold tailWord_741359
  simp only [CollatzResearch.WordTrace]
  refine ⟨27039584121190431882051131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18026389414126954588034087 27039584121190431882051131)
  ·
    refine ⟨40559376181785647823076697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27039584121190431882051131 40559376181785647823076697)
    ·
      refine ⟨30419532136339235867307523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40559376181785647823076697 30419532136339235867307523)
      ·
        refine ⟨45629298204508853800961285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30419532136339235867307523 45629298204508853800961285)
        ·
          refine ⟨8555493413345410087680241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45629298204508853800961285 8555493413345410087680241)
          ·
            refine ⟨6416620060009057565760181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8555493413345410087680241 6416620060009057565760181)
            ·
              refine ⟨601558130625849146790017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6416620060009057565760181 601558130625849146790017)
              ·
                refine ⟨451168597969386860092513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601558130625849146790017 451168597969386860092513)
                ·
                  refine ⟨338376448477040145069385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451168597969386860092513 338376448477040145069385)
                  ·
                    rfl

theorem cell20_741359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 2].length) (baseStart_741359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741359 prefixEnd_741359 := by exact prefixLift 741359
  have htrace : WordTrace (prefixWord ++ tailWord_741359) baseStart_741359 baseEnd_741359 := by
    simpa [prefixWord, tailWord_741359, baseEnd_741359] using wordTrace_append hprefix tailTrace_741359
  have hstable : (prefixWord ++ tailWord_741359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741359).length < 2 ^ (prefixWord ++ tailWord_741359).sum := by decide
  have hdescent : baseEnd_741359 < baseStart_741359 := by decide
  rcases family_descends (prefixWord ++ tailWord_741359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741366 : List Nat := [5, 1, 1, 1, 4, 1, 2, 5]
def baseStart_741366 : Nat := 118140960795 + 741366 * 2 ^ 59
def prefixEnd_741366 : Nat := 4983230072969 + 3 ^ 40 * 741366 * 2
def baseEnd_741366 : Nat := 112793214489259743945341

theorem tailTrace_741366 : CollatzResearch.WordTrace tailWord_741366 prefixEnd_741366 112793214489259743945341 := by
  unfold tailWord_741366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689989964510317004847247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18026559621443381385037301 1689989964510317004847247)
  ·
    refine ⟨2534984946765475507270871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1689989964510317004847247 2534984946765475507270871)
    ·
      refine ⟨3802477420148213260906307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2534984946765475507270871 3802477420148213260906307)
      ·
        refine ⟨5703716130222319891359461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3802477420148213260906307 5703716130222319891359461)
        ·
          refine ⟨1069446774416684979629899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5703716130222319891359461 1069446774416684979629899)
          ·
            refine ⟨1604170161625027469444849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069446774416684979629899 1604170161625027469444849)
            ·
              refine ⟨1203127621218770602083637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604170161625027469444849 1203127621218770602083637)
              ·
                refine ⟨112793214489259743945341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1203127621218770602083637 112793214489259743945341)
                ·
                  rfl

theorem cell20_741366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_741366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741366 prefixEnd_741366 := by exact prefixLift 741366
  have htrace : WordTrace (prefixWord ++ tailWord_741366) baseStart_741366 baseEnd_741366 := by
    simpa [prefixWord, tailWord_741366, baseEnd_741366] using wordTrace_append hprefix tailTrace_741366
  have hstable : (prefixWord ++ tailWord_741366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741366).length < 2 ^ (prefixWord ++ tailWord_741366).sum := by decide
  have hdescent : baseEnd_741366 < baseStart_741366 := by decide
  rcases family_descends (prefixWord ++ tailWord_741366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741373 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 3]
def baseStart_741373 : Nat := 118140960795 + 741373 * 2 ^ 59
def prefixEnd_741373 : Nat := 4983230072969 + 3 ^ 40 * 741373 * 2
def baseEnd_741373 : Nat := 338382838458518318602661

theorem tailTrace_741373 : CollatzResearch.WordTrace tailWord_741373 prefixEnd_741373 338382838458518318602661 := by
  unfold tailWord_741373
  simp only [CollatzResearch.WordTrace]
  refine ⟨27040094743139712273060773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18026729828759808182040515 27040094743139712273060773)
  ·
    refine ⟨5070017764338696051198895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27040094743139712273060773 5070017764338696051198895)
    ·
      refine ⟨7605026646508044076798343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5070017764338696051198895 7605026646508044076798343)
      ·
        refine ⟨11407539969762066115197515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7605026646508044076798343 11407539969762066115197515)
        ·
          refine ⟨17111309954643099172796273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11407539969762066115197515 17111309954643099172796273)
          ·
            refine ⟨12833482465982324379597205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17111309954643099172796273 12833482465982324379597205)
            ·
              refine ⟨601569490592921455293619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12833482465982324379597205 601569490592921455293619)
              ·
                refine ⟨902354235889382182940429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 601569490592921455293619 902354235889382182940429)
                ·
                  refine ⟨338382838458518318602661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902354235889382182940429 338382838458518318602661)
                  ·
                    rfl

theorem cell20_741373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_741373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741373 prefixEnd_741373 := by exact prefixLift 741373
  have htrace : WordTrace (prefixWord ++ tailWord_741373) baseStart_741373 baseEnd_741373 := by
    simpa [prefixWord, tailWord_741373, baseEnd_741373] using wordTrace_append hprefix tailTrace_741373
  have hstable : (prefixWord ++ tailWord_741373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741373).length < 2 ^ (prefixWord ++ tailWord_741373).sum := by decide
  have hdescent : baseEnd_741373 < baseStart_741373 := by decide
  rcases family_descends (prefixWord ++ tailWord_741373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741425 : List Nat := [1, 2, 2, 3, 1, 5, 1, 5]
def baseStart_741425 : Nat := 118140960795 + 741425 * 2 ^ 59
def prefixEnd_741425 : Nat := 4983230072969 + 3 ^ 40 * 741425 * 2
def baseEnd_741425 : Nat := 112802190891812416289705

theorem tailTrace_741425 : CollatzResearch.WordTrace tailWord_741425 prefixEnd_741425 112802190891812416289705 := by
  unfold tailWord_741425
  simp only [CollatzResearch.WordTrace]
  refine ⟨27041991338951325153953729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18027994225967550102635819 27041991338951325153953729)
  ·
    refine ⟨20281493504213493865465297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27041991338951325153953729 20281493504213493865465297)
    ·
      refine ⟨15211120128160120399098973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20281493504213493865465297 15211120128160120399098973)
      ·
        refine ⟨5704170048060045149662115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15211120128160120399098973 5704170048060045149662115)
        ·
          refine ⟨8556255072090067724493173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5704170048060045149662115 8556255072090067724493173)
          ·
            refine ⟨802148913008443849171235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8556255072090067724493173 802148913008443849171235)
            ·
              refine ⟨1203223369512665773756853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802148913008443849171235 1203223369512665773756853)
              ·
                refine ⟨112802190891812416289705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1203223369512665773756853 112802190891812416289705)
                ·
                  rfl

theorem cell20_741425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 5].length) (baseStart_741425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741425 prefixEnd_741425 := by exact prefixLift 741425
  have htrace : WordTrace (prefixWord ++ tailWord_741425) baseStart_741425 baseEnd_741425 := by
    simpa [prefixWord, tailWord_741425, baseEnd_741425] using wordTrace_append hprefix tailTrace_741425
  have hstable : (prefixWord ++ tailWord_741425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741425).length < 2 ^ (prefixWord ++ tailWord_741425).sum := by decide
  have hdescent : baseEnd_741425 < baseStart_741425 := by decide
  rcases family_descends (prefixWord ++ tailWord_741425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741477 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 4]
def baseStart_741477 : Nat := 118140960795 + 741477 * 2 ^ 59
def prefixEnd_741477 : Nat := 4983230072969 + 3 ^ 40 * 741477 * 2
def baseEnd_741477 : Nat := 338430306892356179135569

theorem tailTrace_741477 : CollatzResearch.WordTrace tailWord_741477 prefixEnd_741477 338430306892356179135569 := by
  unfold tailWord_741477
  simp only [CollatzResearch.WordTrace]
  refine ⟨27043887934762938034846685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18029258623175292023231123 27043887934762938034846685)
  ·
    refine ⟨10141457975536101763067507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27043887934762938034846685 10141457975536101763067507)
    ·
      refine ⟨15212186963304152644601261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10141457975536101763067507 15212186963304152644601261)
      ·
        refine ⟨5704570111239057241725473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15212186963304152644601261 5704570111239057241725473)
        ·
          refine ⟨4278427583429292931294105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5704570111239057241725473 4278427583429292931294105)
          ·
            refine ⟨3208820687571969698470579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278427583429292931294105 3208820687571969698470579)
            ·
              refine ⟨4813231031357954547705869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208820687571969698470579 4813231031357954547705869)
              ·
                refine ⟨1804961636759232955389701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4813231031357954547705869 1804961636759232955389701)
                ·
                  refine ⟨338430306892356179135569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1804961636759232955389701 338430306892356179135569)
                  ·
                    rfl

theorem cell20_741477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_741477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741477 prefixEnd_741477 := by exact prefixLift 741477
  have htrace : WordTrace (prefixWord ++ tailWord_741477) baseStart_741477 baseEnd_741477 := by
    simpa [prefixWord, tailWord_741477, baseEnd_741477] using wordTrace_append hprefix tailTrace_741477
  have hstable : (prefixWord ++ tailWord_741477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741477).length < 2 ^ (prefixWord ++ tailWord_741477).sum := by decide
  have hdescent : baseEnd_741477 < baseStart_741477 := by decide
  rcases family_descends (prefixWord ++ tailWord_741477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741487 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 3]
def baseStart_741487 : Nat := 118140960795 + 741487 * 2 ^ 59
def prefixEnd_741487 : Nat := 4983230072969 + 3 ^ 40 * 741487 * 2
def baseEnd_741487 : Nat := 338434871164840588802195

theorem tailTrace_741487 : CollatzResearch.WordTrace tailWord_741487 prefixEnd_741487 338434871164840588802195 := by
  unfold tailWord_741487
  simp only [CollatzResearch.WordTrace]
  refine ⟨27044252664726709742710715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18029501776484473161807143 27044252664726709742710715)
  ·
    refine ⟨40566378997090064614066073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27044252664726709742710715 40566378997090064614066073)
    ·
      refine ⟨30424784247817548460549555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40566378997090064614066073 30424784247817548460549555)
      ·
        refine ⟨45637176371726322690824333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30424784247817548460549555 45637176371726322690824333)
        ·
          refine ⟨17113941139397371009059125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45637176371726322690824333 17113941139397371009059125)
          ·
            refine ⟨1604431981818503532099293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17113941139397371009059125 1604431981818503532099293)
            ·
              refine ⟨601661993181938824537235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1604431981818503532099293 601661993181938824537235)
              ·
                refine ⟨902492989772908236805853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 601661993181938824537235 902492989772908236805853)
                ·
                  refine ⟨338434871164840588802195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902492989772908236805853 338434871164840588802195)
                  ·
                    rfl

theorem cell20_741487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 3].length) (baseStart_741487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741487 prefixEnd_741487 := by exact prefixLift 741487
  have htrace : WordTrace (prefixWord ++ tailWord_741487) baseStart_741487 baseEnd_741487 := by
    simpa [prefixWord, tailWord_741487, baseEnd_741487] using wordTrace_append hprefix tailTrace_741487
  have hstable : (prefixWord ++ tailWord_741487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741487).length < 2 ^ (prefixWord ++ tailWord_741487).sum := by decide
  have hdescent : baseEnd_741487 < baseStart_741487 := by decide
  rcases family_descends (prefixWord ++ tailWord_741487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741494 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_741494 : Nat := 118140960795 + 741494 * 2 ^ 59
def prefixEnd_741494 : Nat := 4983230072969 + 3 ^ 40 * 741494 * 2
def baseEnd_741494 : Nat := 338438066155579675568833

theorem tailTrace_741494 : CollatzResearch.WordTrace tailWord_741494 prefixEnd_741494 338438066155579675568833 := by
  unfold tailWord_741494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690281748481334371138471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18029671983800899958810357 1690281748481334371138471)
  ·
    refine ⟨2535422622722001556707707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1690281748481334371138471 2535422622722001556707707)
    ·
      refine ⟨3803133934083002335061561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2535422622722001556707707 3803133934083002335061561)
      ·
        refine ⟨2852350450562251751296171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3803133934083002335061561 2852350450562251751296171)
        ·
          refine ⟨4278525675843377626944257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852350450562251751296171 4278525675843377626944257)
          ·
            refine ⟨3208894256882533220208193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278525675843377626944257 3208894256882533220208193)
            ·
              refine ⟨2406670692661899915156145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3208894256882533220208193 2406670692661899915156145)
              ·
                refine ⟨1805003019496424936367109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406670692661899915156145 1805003019496424936367109)
                ·
                  refine ⟨338438066155579675568833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1805003019496424936367109 338438066155579675568833)
                  ·
                    rfl

theorem cell20_741494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_741494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741494 prefixEnd_741494 := by exact prefixLift 741494
  have htrace : WordTrace (prefixWord ++ tailWord_741494) baseStart_741494 baseEnd_741494 := by
    simpa [prefixWord, tailWord_741494, baseEnd_741494] using wordTrace_append hprefix tailTrace_741494
  have hstable : (prefixWord ++ tailWord_741494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741494).length < 2 ^ (prefixWord ++ tailWord_741494).sum := by decide
  have hdescent : baseEnd_741494 < baseStart_741494 := by decide
  rcases family_descends (prefixWord ++ tailWord_741494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741501 : List Nat := [1, 4, 1, 1, 3, 2, 4, 4]
def baseStart_741501 : Nat := 118140960795 + 741501 * 2 ^ 59
def prefixEnd_741501 : Nat := 4983230072969 + 3 ^ 40 * 741501 * 2
def baseEnd_741501 : Nat := 112813753715439587445157

theorem tailTrace_741501 : CollatzResearch.WordTrace tailWord_741501 prefixEnd_741501 112813753715439587445157 := by
  unfold tailWord_741501
  simp only [CollatzResearch.WordTrace]
  refine ⟨27044763286675990133720357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18029842191117326755813571 27044763286675990133720357)
  ·
    refine ⟨5070893116251748150072567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27044763286675990133720357 5070893116251748150072567)
    ·
      refine ⟨7606339674377622225108851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5070893116251748150072567 7606339674377622225108851)
      ·
        refine ⟨11409509511566433337663277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7606339674377622225108851 11409509511566433337663277)
        ·
          refine ⟨4278566066837412501623729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11409509511566433337663277 4278566066837412501623729)
          ·
            refine ⟨3208924550128059376217797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278566066837412501623729 3208924550128059376217797)
            ·
              refine ⟨601673353149011133040837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3208924550128059376217797 601673353149011133040837)
              ·
                refine ⟨112813753715439587445157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601673353149011133040837 112813753715439587445157)
                ·
                  rfl

theorem cell20_741501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 4].length) (baseStart_741501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741501 prefixEnd_741501 := by exact prefixLift 741501
  have htrace : WordTrace (prefixWord ++ tailWord_741501) baseStart_741501 baseEnd_741501 := by
    simpa [prefixWord, tailWord_741501, baseEnd_741501] using wordTrace_append hprefix tailTrace_741501
  have hstable : (prefixWord ++ tailWord_741501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741501).length < 2 ^ (prefixWord ++ tailWord_741501).sum := by decide
  have hdescent : baseEnd_741501 < baseStart_741501 := by decide
  rcases family_descends (prefixWord ++ tailWord_741501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741518 : List Nat := [4, 1, 1, 3, 4, 1, 6]
def baseStart_741518 : Nat := 118140960795 + 741518 * 2 ^ 59
def prefixEnd_741518 : Nat := 4983230072969 + 3 ^ 40 * 741518 * 2
def baseEnd_741518 : Nat := 37605446712171362085415

theorem tailTrace_741518 : CollatzResearch.WordTrace tailWord_741518 prefixEnd_741518 37605446712171362085415 := by
  unfold tailWord_741518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3380672915951800254636151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18030255551742934691392805 3380672915951800254636151)
  ·
    refine ⟨5071009373927700381954227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3380672915951800254636151 5071009373927700381954227)
    ·
      refine ⟨7606514060891550572931341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5071009373927700381954227 7606514060891550572931341)
      ·
        refine ⟨2852442772834331464849253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7606514060891550572931341 2852442772834331464849253)
        ·
          refine ⟨534833019906437149659235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2852442772834331464849253 534833019906437149659235)
          ·
            refine ⟨802249529859655724488853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534833019906437149659235 802249529859655724488853)
            ·
              refine ⟨37605446712171362085415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 802249529859655724488853 37605446712171362085415)
              ·
                rfl

theorem cell20_741518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 6].length) (baseStart_741518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741518 prefixEnd_741518 := by exact prefixLift 741518
  have htrace : WordTrace (prefixWord ++ tailWord_741518) baseStart_741518 baseEnd_741518 := by
    simpa [prefixWord, tailWord_741518, baseEnd_741518] using wordTrace_append hprefix tailTrace_741518
  have hstable : (prefixWord ++ tailWord_741518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741518).length < 2 ^ (prefixWord ++ tailWord_741518).sum := by decide
  have hdescent : baseEnd_741518 < baseStart_741518 := by decide
  rcases family_descends (prefixWord ++ tailWord_741518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741528 : List Nat := [2, 1, 2, 4, 3, 1, 3, 2, 2]
def baseStart_741528 : Nat := 118140960795 + 741528 * 2 ^ 59
def prefixEnd_741528 : Nat := 4983230072969 + 3 ^ 40 * 741528 * 2
def baseEnd_741528 : Nat := 338453584682026668435361

theorem tailTrace_741528 : CollatzResearch.WordTrace tailWord_741528 prefixEnd_741528 338453584682026668435361 := by
  unfold tailWord_741528
  simp only [CollatzResearch.WordTrace]
  refine ⟨13522874028789086872476619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18030498705052115829968825 13522874028789086872476619)
  ·
    refine ⟨20284311043183630308714929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13522874028789086872476619 20284311043183630308714929)
    ·
      refine ⟨15213233282387722731536197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20284311043183630308714929 15213233282387722731536197)
      ·
        refine ⟨2852481240447698012163037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15213233282387722731536197 2852481240447698012163037)
        ·
          refine ⟨1069680465167886754561139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2852481240447698012163037 1069680465167886754561139)
          ·
            refine ⟨1604520697751830131841709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069680465167886754561139 1604520697751830131841709)
            ·
              refine ⟨601695261656936299440641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1604520697751830131841709 601695261656936299440641)
              ·
                refine ⟨451271446242702224580481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601695261656936299440641 451271446242702224580481)
                ·
                  refine ⟨338453584682026668435361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451271446242702224580481 338453584682026668435361)
                  ·
                    rfl

theorem cell20_741528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 2].length) (baseStart_741528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741528 prefixEnd_741528 := by exact prefixLift 741528
  have htrace : WordTrace (prefixWord ++ tailWord_741528) baseStart_741528 baseEnd_741528 := by
    simpa [prefixWord, tailWord_741528, baseEnd_741528] using wordTrace_append hprefix tailTrace_741528
  have hstable : (prefixWord ++ tailWord_741528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741528).length < 2 ^ (prefixWord ++ tailWord_741528).sum := by decide
  have hdescent : baseEnd_741528 < baseStart_741528 := by decide
  rcases family_descends (prefixWord ++ tailWord_741528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741580 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 3]
def baseStart_741580 : Nat := 118140960795 + 741580 * 2 ^ 59
def prefixEnd_741580 : Nat := 4983230072969 + 3 ^ 40 * 741580 * 2
def baseEnd_741580 : Nat := 338477318898945598701815

theorem tailTrace_741580 : CollatzResearch.WordTrace tailWord_741580 prefixEnd_741580 338477318898945598701815 := by
  unfold tailWord_741580
  simp only [CollatzResearch.WordTrace]
  refine ⟨13523822326694893312923097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18031763102259857750564129 13523822326694893312923097)
  ·
    refine ⟨10142866745021169984692323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13523822326694893312923097 10142866745021169984692323)
    ·
      refine ⟨15214300117531754977038485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10142866745021169984692323 15214300117531754977038485)
      ·
        refine ⟨713170318009301014548679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15214300117531754977038485 713170318009301014548679)
        ·
          refine ⟨1069755477013951521823019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713170318009301014548679 1069755477013951521823019)
          ·
            refine ⟨1604633215520927282734529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069755477013951521823019 1604633215520927282734529)
            ·
              refine ⟨1203474911640695462050897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604633215520927282734529 1203474911640695462050897)
              ·
                refine ⟨902606183730521596538173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203474911640695462050897 902606183730521596538173)
                ·
                  refine ⟨338477318898945598701815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902606183730521596538173 338477318898945598701815)
                  ·
                    rfl

theorem cell20_741580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_741580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741580 prefixEnd_741580 := by exact prefixLift 741580
  have htrace : WordTrace (prefixWord ++ tailWord_741580) baseStart_741580 baseEnd_741580 := by
    simpa [prefixWord, tailWord_741580, baseEnd_741580] using wordTrace_append hprefix tailTrace_741580
  have hstable : (prefixWord ++ tailWord_741580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741580).length < 2 ^ (prefixWord ++ tailWord_741580).sum := by decide
  have hdescent : baseEnd_741580 < baseStart_741580 := by decide
  rcases family_descends (prefixWord ++ tailWord_741580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741615 : List Nat := [1, 1, 2, 1, 6, 2, 3, 4]
def baseStart_741615 : Nat := 118140960795 + 741615 * 2 ^ 59
def prefixEnd_741615 : Nat := 4983230072969 + 3 ^ 40 * 741615 * 2
def baseEnd_741615 : Nat := 112831097950880344178335

theorem tailTrace_741615 : CollatzResearch.WordTrace tailWord_741615 prefixEnd_741615 112831097950880344178335 := by
  unfold tailWord_741615
  simp only [CollatzResearch.WordTrace]
  refine ⟨27048921208262987603370299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18032614138841991735580199 27048921208262987603370299)
  ·
    refine ⟨40573381812394481405055449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27048921208262987603370299 40573381812394481405055449)
    ·
      refine ⟨30430036359295861053791587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40573381812394481405055449 30430036359295861053791587)
      ·
        refine ⟨45645054538943791580687381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30430036359295861053791587 45645054538943791580687381)
        ·
          refine ⟨2139611931512990230344721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45645054538943791580687381 2139611931512990230344721)
          ·
            refine ⟨1604708948634742672758541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2139611931512990230344721 1604708948634742672758541)
            ·
              refine ⟨601765855738028502284453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1604708948634742672758541 601765855738028502284453)
              ·
                refine ⟨112831097950880344178335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601765855738028502284453 112831097950880344178335)
                ·
                  rfl

theorem cell20_741615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 4].length) (baseStart_741615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741615 prefixEnd_741615 := by exact prefixLift 741615
  have htrace : WordTrace (prefixWord ++ tailWord_741615) baseStart_741615 baseEnd_741615 := by
    simpa [prefixWord, tailWord_741615, baseEnd_741615] using wordTrace_append hprefix tailTrace_741615
  have hstable : (prefixWord ++ tailWord_741615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741615).length < 2 ^ (prefixWord ++ tailWord_741615).sum := by decide
  have hdescent : baseEnd_741615 < baseStart_741615 := by decide
  rcases family_descends (prefixWord ++ tailWord_741615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741639 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 5]
def baseStart_741639 : Nat := 118140960795 + 741639 * 2 ^ 59
def prefixEnd_741639 : Nat := 4983230072969 + 3 ^ 40 * 741639 * 2
def baseEnd_741639 : Nat := 338504248106603615734907

theorem tailTrace_741639 : CollatzResearch.WordTrace tailWord_741639 prefixEnd_741639 338504248106603615734907 := by
  unfold tailWord_741639
  simp only [CollatzResearch.WordTrace]
  refine ⟨27049796560176039702243971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18033197706784026468162647 27049796560176039702243971)
  ·
    refine ⟨40574694840264059553365957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27049796560176039702243971 40574694840264059553365957)
    ·
      refine ⟨7607755282549511166256117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40574694840264059553365957 7607755282549511166256117)
      ·
        refine ⟨713227057739016671836511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7607755282549511166256117 713227057739016671836511)
        ·
          refine ⟨1069840586608525007754767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713227057739016671836511 1069840586608525007754767)
          ·
            refine ⟨1604760879912787511632151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069840586608525007754767 1604760879912787511632151)
            ·
              refine ⟨2407141319869181267448227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604760879912787511632151 2407141319869181267448227)
              ·
                refine ⟨3610711979803771901172341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407141319869181267448227 3610711979803771901172341)
                ·
                  refine ⟨338504248106603615734907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3610711979803771901172341 338504248106603615734907)
                  ·
                    rfl

theorem cell20_741639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 5].length) (baseStart_741639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741639 prefixEnd_741639 := by exact prefixLift 741639
  have htrace : WordTrace (prefixWord ++ tailWord_741639) baseStart_741639 baseEnd_741639 := by
    simpa [prefixWord, tailWord_741639, baseEnd_741639] using wordTrace_append hprefix tailTrace_741639
  have hstable : (prefixWord ++ tailWord_741639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741639).length < 2 ^ (prefixWord ++ tailWord_741639).sum := by decide
  have hdescent : baseEnd_741639 < baseStart_741639 := by decide
  rcases family_descends (prefixWord ++ tailWord_741639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741643 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 5]
def baseStart_741643 : Nat := 118140960795 + 741643 * 2 ^ 59
def prefixEnd_741643 : Nat := 4983230072969 + 3 ^ 40 * 741643 * 2
def baseEnd_741643 : Nat := 338506073815597379601557

theorem tailTrace_741643 : CollatzResearch.WordTrace tailWord_741643 prefixEnd_741643 338506073815597379601557 := by
  unfold tailWord_741643
  simp only [CollatzResearch.WordTrace]
  refine ⟨27049942452161548385389583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18033294968107698923593055 27049942452161548385389583)
  ·
    refine ⟨40574913678242322578084375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27049942452161548385389583 40574913678242322578084375)
    ·
      refine ⟨60862370517363483867126563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40574913678242322578084375 60862370517363483867126563)
      ·
        refine ⟨91293555776045225800689845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60862370517363483867126563 91293555776045225800689845)
        ·
          refine ⟨8558770854004239918814673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91293555776045225800689845 8558770854004239918814673)
          ·
            refine ⟨6419078140503179939111005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8558770854004239918814673 6419078140503179939111005)
            ·
              refine ⟨2407154302688692477166627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6419078140503179939111005 2407154302688692477166627)
              ·
                refine ⟨3610731454033038715749941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407154302688692477166627 3610731454033038715749941)
                ·
                  refine ⟨338506073815597379601557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3610731454033038715749941 338506073815597379601557)
                  ·
                    rfl

theorem cell20_741643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_741643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741643 prefixEnd_741643 := by exact prefixLift 741643
  have htrace : WordTrace (prefixWord ++ tailWord_741643) baseStart_741643 baseEnd_741643 := by
    simpa [prefixWord, tailWord_741643, baseEnd_741643] using wordTrace_append hprefix tailTrace_741643
  have hstable : (prefixWord ++ tailWord_741643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741643).length < 2 ^ (prefixWord ++ tailWord_741643).sum := by decide
  have hdescent : baseEnd_741643 < baseStart_741643 := by decide
  rcases family_descends (prefixWord ++ tailWord_741643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741646 : List Nat := [4, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_741646 : Nat := 118140960795 + 741646 * 2 ^ 59
def prefixEnd_741646 : Nat := 4983230072969 + 3 ^ 40 * 741646 * 2
def baseEnd_741646 : Nat := 338507443097342702501545

theorem tailTrace_741646 : CollatzResearch.WordTrace tailWord_741646 prefixEnd_741646 338507443097342702501545 := by
  unfold tailWord_741646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3381256483893834987218599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18033367914100453265165861 3381256483893834987218599)
  ·
    refine ⟨5071884725840752480827899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3381256483893834987218599 5071884725840752480827899)
    ·
      refine ⟨7607827088761128721241849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5071884725840752480827899 7607827088761128721241849)
      ·
        refine ⟨5705870316570846540931387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7607827088761128721241849 5705870316570846540931387)
        ·
          refine ⟨8558805474856269811397081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5705870316570846540931387 8558805474856269811397081)
          ·
            refine ⟨6419104106142202358547811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8558805474856269811397081 6419104106142202358547811)
            ·
              refine ⟨9628656159213303537821717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6419104106142202358547811 9628656159213303537821717)
              ·
                refine ⟨451343257463123603335393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9628656159213303537821717 451343257463123603335393)
                ·
                  refine ⟨338507443097342702501545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451343257463123603335393 338507443097342702501545)
                  ·
                    rfl

theorem cell20_741646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_741646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741646 prefixEnd_741646 := by exact prefixLift 741646
  have htrace : WordTrace (prefixWord ++ tailWord_741646) baseStart_741646 baseEnd_741646 := by
    simpa [prefixWord, tailWord_741646, baseEnd_741646] using wordTrace_append hprefix tailTrace_741646
  have hstable : (prefixWord ++ tailWord_741646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741646).length < 2 ^ (prefixWord ++ tailWord_741646).sum := by decide
  have hdescent : baseEnd_741646 < baseStart_741646 := by decide
  rcases family_descends (prefixWord ++ tailWord_741646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741688 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_741688 : Nat := 118140960795 + 741688 * 2 ^ 59
def prefixEnd_741688 : Nat := 4983230072969 + 3 ^ 40 * 741688 * 2
def baseEnd_741688 : Nat := 338526613041777223101373

theorem tailTrace_741688 : CollatzResearch.WordTrace tailWord_741688 prefixEnd_741688 338526613041777223101373 := by
  unfold tailWord_741688
  simp only [CollatzResearch.WordTrace]
  refine ⟨13525791868499260535388859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18034389157999014047185145 13525791868499260535388859)
  ·
    refine ⟨20288687802748890803083289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13525791868499260535388859 20288687802748890803083289)
    ·
      refine ⟨15216515852061668102312467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20288687802748890803083289 15216515852061668102312467)
      ·
        refine ⟨22824773778092502153468701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15216515852061668102312467 22824773778092502153468701)
        ·
          refine ⟨8559290166784688307550763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22824773778092502153468701 8559290166784688307550763)
          ·
            refine ⟨12838935250177032461326145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8559290166784688307550763 12838935250177032461326145)
            ·
              refine ⟨9629201437632774345994609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12838935250177032461326145 9629201437632774345994609)
              ·
                refine ⟨7221901078224580759495957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9629201437632774345994609 7221901078224580759495957)
                ·
                  refine ⟨338526613041777223101373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7221901078224580759495957 338526613041777223101373)
                  ·
                    rfl

theorem cell20_741688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_741688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741688 prefixEnd_741688 := by exact prefixLift 741688
  have htrace : WordTrace (prefixWord ++ tailWord_741688) baseStart_741688 baseEnd_741688 := by
    simpa [prefixWord, tailWord_741688, baseEnd_741688] using wordTrace_append hprefix tailTrace_741688
  have hstable : (prefixWord ++ tailWord_741688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741688).length < 2 ^ (prefixWord ++ tailWord_741688).sum := by decide
  have hdescent : baseEnd_741688 < baseStart_741688 := by decide
  rcases family_descends (prefixWord ++ tailWord_741688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741712 : List Nat := [2, 1, 1, 1, 1, 7, 2, 5]
def baseStart_741712 : Nat := 118140960795 + 741712 * 2 ^ 59
def prefixEnd_741712 : Nat := 4983230072969 + 3 ^ 40 * 741712 * 2
def baseEnd_741712 : Nat := 112845855765246602100425

theorem tailTrace_741712 : CollatzResearch.WordTrace tailWord_741712 prefixEnd_741712 112845855765246602100425 := by
  unfold tailWord_741712
  simp only [CollatzResearch.WordTrace]
  refine ⟨13526229544455786584825695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18034972725941048779767593 13526229544455786584825695)
  ·
    refine ⟨20289344316683679877238543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13526229544455786584825695 20289344316683679877238543)
    ·
      refine ⟨30434016475025519815857815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20289344316683679877238543 30434016475025519815857815)
      ·
        refine ⟨45651024712538279723786723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30434016475025519815857815 45651024712538279723786723)
        ·
          refine ⟨68476537068807419585680085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45651024712538279723786723 68476537068807419585680085)
          ·
            refine ⟨1604918837550173896539377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 68476537068807419585680085 1604918837550173896539377)
            ·
              refine ⟨1203689128162630422404533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604918837550173896539377 1203689128162630422404533)
              ·
                refine ⟨112845855765246602100425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1203689128162630422404533 112845855765246602100425)
                ·
                  rfl

theorem cell20_741712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_741712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741712 prefixEnd_741712 := by exact prefixLift 741712
  have htrace : WordTrace (prefixWord ++ tailWord_741712) baseStart_741712 baseEnd_741712 := by
    simpa [prefixWord, tailWord_741712, baseEnd_741712] using wordTrace_append hprefix tailTrace_741712
  have hstable : (prefixWord ++ tailWord_741712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741712).length < 2 ^ (prefixWord ++ tailWord_741712).sum := by decide
  have hdescent : baseEnd_741712 < baseStart_741712 := by decide
  rcases family_descends (prefixWord ++ tailWord_741712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741805 : List Nat := [1, 5, 2, 2, 2, 1, 7]
def baseStart_741805 : Nat := 118140960795 + 741805 * 2 ^ 59
def prefixEnd_741805 : Nat := 4983230072969 + 3 ^ 40 * 741805 * 2
def baseEnd_741805 : Nat := 37620001669982757355655

theorem tailTrace_741805 : CollatzResearch.WordTrace tailWord_741805 prefixEnd_741805 37620001669982757355655 := by
  unfold tailWord_741805
  simp only [CollatzResearch.WordTrace]
  refine ⟨27055851077574650052786869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18037234051716433368524579 27055851077574650052786869)
  ·
    refine ⟨2536486038522623442448769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27055851077574650052786869 2536486038522623442448769)
    ·
      refine ⟨1902364528891967581836577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2536486038522623442448769 1902364528891967581836577)
      ·
        refine ⟨1426773396668975686377433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1902364528891967581836577 1426773396668975686377433)
        ·
          refine ⟨1070080047501731764783075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1426773396668975686377433 1070080047501731764783075)
          ·
            refine ⟨1605120071252597647174613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070080047501731764783075 1605120071252597647174613)
            ·
              refine ⟨37620001669982757355655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1605120071252597647174613 37620001669982757355655)
              ·
                rfl

theorem cell20_741805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 7].length) (baseStart_741805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741805 prefixEnd_741805 := by exact prefixLift 741805
  have htrace : WordTrace (prefixWord ++ tailWord_741805) baseStart_741805 baseEnd_741805 := by
    simpa [prefixWord, tailWord_741805, baseEnd_741805] using wordTrace_append hprefix tailTrace_741805
  have hstable : (prefixWord ++ tailWord_741805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741805).length < 2 ^ (prefixWord ++ tailWord_741805).sum := by decide
  have hdescent : baseEnd_741805 < baseStart_741805 := by decide
  rcases family_descends (prefixWord ++ tailWord_741805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741833 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 3]
def baseStart_741833 : Nat := 118140960795 + 741833 * 2 ^ 59
def prefixEnd_741833 : Nat := 4983230072969 + 3 ^ 40 * 741833 * 2
def baseEnd_741833 : Nat := 338592794992801163267447

theorem tailTrace_741833 : CollatzResearch.WordTrace tailWord_741833 prefixEnd_741833 338592794992801163267447 := by
  unfold tailWord_741833
  simp only [CollatzResearch.WordTrace]
  refine ⟨27056872321473210834806153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18037914880982140556537435 27056872321473210834806153)
  ·
    refine ⟨20292654241104908126104615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27056872321473210834806153 20292654241104908126104615)
    ·
      refine ⟨30438981361657362189156923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20292654241104908126104615 30438981361657362189156923)
      ·
        refine ⟨45658472042486043283735385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30438981361657362189156923 45658472042486043283735385)
        ·
          refine ⟨34243854031864532462801539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45658472042486043283735385 34243854031864532462801539)
          ·
            refine ⟨51365781047796798694202309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34243854031864532462801539 51365781047796798694202309)
            ·
              refine ⟨9631083946461899755162933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51365781047796798694202309 9631083946461899755162933)
              ·
                refine ⟨902914119980803102046525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9631083946461899755162933 902914119980803102046525)
                ·
                  refine ⟨338592794992801163267447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902914119980803102046525 338592794992801163267447)
                  ·
                    rfl

theorem cell20_741833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_741833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741833 prefixEnd_741833 := by exact prefixLift 741833
  have htrace : WordTrace (prefixWord ++ tailWord_741833) baseStart_741833 baseEnd_741833 := by
    simpa [prefixWord, tailWord_741833, baseEnd_741833] using wordTrace_append hprefix tailTrace_741833
  have hstable : (prefixWord ++ tailWord_741833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741833).length < 2 ^ (prefixWord ++ tailWord_741833).sum := by decide
  have hdescent : baseEnd_741833 < baseStart_741833 := by decide
  rcases family_descends (prefixWord ++ tailWord_741833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741864 : List Nat := [2, 1, 4, 1, 1, 5, 6]
def baseStart_741864 : Nat := 118140960795 + 741864 * 2 ^ 59
def prefixEnd_741864 : Nat := 4983230072969 + 3 ^ 40 * 741864 * 2
def baseEnd_741864 : Nat := 37622993804166981470443

theorem tailTrace_741864 : CollatzResearch.WordTrace tailWord_741864 prefixEnd_741864 37622993804166981470443 := by
  unfold tailWord_741864
  simp only [CollatzResearch.WordTrace]
  refine ⟨13529001492180451564592323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18038668656240602086123097 13529001492180451564592323)
  ·
    refine ⟨20293502238270677346888485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13529001492180451564592323 20293502238270677346888485)
    ·
      refine ⟨3805031669675752002541591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20293502238270677346888485 3805031669675752002541591)
      ·
        refine ⟨5707547504513628003812387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3805031669675752002541591 5707547504513628003812387)
        ·
          refine ⟨8561321256770442005718581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5707547504513628003812387 8561321256770442005718581)
          ·
            refine ⟨802623867822228938036117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8561321256770442005718581 802623867822228938036117)
            ·
              refine ⟨37622993804166981470443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 802623867822228938036117 37622993804166981470443)
              ·
                rfl

theorem cell20_741864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 6].length) (baseStart_741864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741864 prefixEnd_741864 := by exact prefixLift 741864
  have htrace : WordTrace (prefixWord ++ tailWord_741864) baseStart_741864 baseEnd_741864 := by
    simpa [prefixWord, tailWord_741864, baseEnd_741864] using wordTrace_append hprefix tailTrace_741864
  have hstable : (prefixWord ++ tailWord_741864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741864).length < 2 ^ (prefixWord ++ tailWord_741864).sum := by decide
  have hdescent : baseEnd_741864 < baseStart_741864 := by decide
  rcases family_descends (prefixWord ++ tailWord_741864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741871 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 3]
def baseStart_741871 : Nat := 118140960795 + 741871 * 2 ^ 59
def prefixEnd_741871 : Nat := 4983230072969 + 3 ^ 40 * 741871 * 2
def baseEnd_741871 : Nat := 338610139228241920000625

theorem tailTrace_741871 : CollatzResearch.WordTrace tailWord_741871 prefixEnd_741871 338610139228241920000625 := by
  unfold tailWord_741871
  simp only [CollatzResearch.WordTrace]
  refine ⟨27058258295335543324689467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18038838863557028883126311 27058258295335543324689467)
  ·
    refine ⟨40587387443003314987034201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27058258295335543324689467 40587387443003314987034201)
    ·
      refine ⟨30440540582252486240275651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40587387443003314987034201 30440540582252486240275651)
      ·
        refine ⟨45660810873378729360413477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30440540582252486240275651 45660810873378729360413477)
        ·
          refine ⟨8561402038758511755077527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45660810873378729360413477 8561402038758511755077527)
          ·
            refine ⟨12842103058137767632616291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8561402038758511755077527 12842103058137767632616291)
            ·
              refine ⟨19263154587206651448924437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12842103058137767632616291 19263154587206651448924437)
              ·
                refine ⟨902960371275311786668333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19263154587206651448924437 902960371275311786668333)
                ·
                  refine ⟨338610139228241920000625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 902960371275311786668333 338610139228241920000625)
                  ·
                    rfl

theorem cell20_741871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 3].length) (baseStart_741871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741871 prefixEnd_741871 := by exact prefixLift 741871
  have htrace : WordTrace (prefixWord ++ tailWord_741871) baseStart_741871 baseEnd_741871 := by
    simpa [prefixWord, tailWord_741871, baseEnd_741871] using wordTrace_append hprefix tailTrace_741871
  have hstable : (prefixWord ++ tailWord_741871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741871).length < 2 ^ (prefixWord ++ tailWord_741871).sum := by decide
  have hdescent : baseEnd_741871 < baseStart_741871 := by decide
  rcases family_descends (prefixWord ++ tailWord_741871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741902 : List Nat := [4, 1, 1, 2, 3, 1, 2, 6]
def baseStart_741902 : Nat := 118140960795 + 741902 * 2 ^ 59
def prefixEnd_741902 : Nat := 4983230072969 + 3 ^ 40 * 741902 * 2
def baseEnd_741902 : Nat := 112874762824314529989055

theorem tailTrace_741902 : CollatzResearch.WordTrace tailWord_741902 prefixEnd_741902 112874762824314529989055 := by
  unfold tailWord_741902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382423619777904452383495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18039592638815490412711973 3382423619777904452383495)
  ·
    refine ⟨5073635429666856678575243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3382423619777904452383495 5073635429666856678575243)
    ·
      refine ⟨7610453144500285017862865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5073635429666856678575243 7610453144500285017862865)
      ·
        refine ⟨5707839858375213763397149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7610453144500285017862865 5707839858375213763397149)
        ·
          refine ⟨2140439946890705161273931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5707839858375213763397149 2140439946890705161273931)
          ·
            refine ⟨3210659920336057741910897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140439946890705161273931 3210659920336057741910897)
            ·
              refine ⟨2407994940252043306433173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3210659920336057741910897 2407994940252043306433173)
              ·
                refine ⟨112874762824314529989055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2407994940252043306433173 112874762824314529989055)
                ·
                  rfl

theorem cell20_741902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_741902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741902 prefixEnd_741902 := by exact prefixLift 741902
  have htrace : WordTrace (prefixWord ++ tailWord_741902) baseStart_741902 baseEnd_741902 := by
    simpa [prefixWord, tailWord_741902, baseEnd_741902] using wordTrace_append hprefix tailTrace_741902
  have hstable : (prefixWord ++ tailWord_741902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741902).length < 2 ^ (prefixWord ++ tailWord_741902).sum := by decide
  have hdescent : baseEnd_741902 < baseStart_741902 := by decide
  rcases family_descends (prefixWord ++ tailWord_741902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741923 : List Nat := [1, 1, 1, 4, 4, 9]
def baseStart_741923 : Nat := 118140960795 + 741923 * 2 ^ 59
def prefixEnd_741923 : Nat := 4983230072969 + 3 ^ 40 * 741923 * 2
def baseEnd_741923 : Nat := 12541995312783735195077

theorem tailTrace_741923 : CollatzResearch.WordTrace tailWord_741923 prefixEnd_741923 12541995312783735195077 := by
  unfold tailWord_741923
  simp only [CollatzResearch.WordTrace]
  refine ⟨27060154891147156205582423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18040103260764770803721615 27060154891147156205582423)
  ·
    refine ⟨40590232336720734308373635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27060154891147156205582423 40590232336720734308373635)
    ·
      refine ⟨60885348505081101462560453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40590232336720734308373635 60885348505081101462560453)
      ·
        refine ⟨11416002844702706524230085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60885348505081101462560453 11416002844702706524230085)
        ·
          refine ⟨2140500533381757473293141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11416002844702706524230085 2140500533381757473293141)
          ·
            refine ⟨12541995312783735195077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2140500533381757473293141 12541995312783735195077)
            ·
              rfl

theorem cell20_741923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 9].length) (baseStart_741923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741923 prefixEnd_741923 := by exact prefixLift 741923
  have htrace : WordTrace (prefixWord ++ tailWord_741923) baseStart_741923 baseEnd_741923 := by
    simpa [prefixWord, tailWord_741923, baseEnd_741923] using wordTrace_append hprefix tailTrace_741923
  have hstable : (prefixWord ++ tailWord_741923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741923).length < 2 ^ (prefixWord ++ tailWord_741923).sum := by decide
  have hdescent : baseEnd_741923 < baseStart_741923 := by decide
  rcases family_descends (prefixWord ++ tailWord_741923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741985 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 5]
def baseStart_741985 : Nat := 118140960795 + 741985 * 2 ^ 59
def prefixEnd_741985 : Nat := 4983230072969 + 3 ^ 40 * 741985 * 2
def baseEnd_741985 : Nat := 338662171934564190200159

theorem tailTrace_741985 : CollatzResearch.WordTrace tailWord_741985 prefixEnd_741985 338662171934564190200159 := by
  unfold tailWord_741985
  simp only [CollatzResearch.WordTrace]
  refine ⟨27062416216922540794339409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18041610811281693862892939 27062416216922540794339409)
  ·
    refine ⟨20296812162691905595754557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27062416216922540794339409 20296812162691905595754557)
    ·
      refine ⟨7611304561009464598407959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20296812162691905595754557 7611304561009464598407959)
      ·
        refine ⟨11416956841514196897611939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7611304561009464598407959 11416956841514196897611939)
        ·
          refine ⟨17125435262271295346417909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11416956841514196897611939 17125435262271295346417909)
          ·
            refine ⟨1605509555837933938726679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17125435262271295346417909 1605509555837933938726679)
            ·
              refine ⟨2408264333756900908090019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605509555837933938726679 2408264333756900908090019)
              ·
                refine ⟨3612396500635351362135029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408264333756900908090019 3612396500635351362135029)
                ·
                  refine ⟨338662171934564190200159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3612396500635351362135029 338662171934564190200159)
                  ·
                    rfl

theorem cell20_741985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_741985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_741985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_741985 prefixEnd_741985 := by exact prefixLift 741985
  have htrace : WordTrace (prefixWord ++ tailWord_741985) baseStart_741985 baseEnd_741985 := by
    simpa [prefixWord, tailWord_741985, baseEnd_741985] using wordTrace_append hprefix tailTrace_741985
  have hstable : (prefixWord ++ tailWord_741985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741985).length < 2 ^ (prefixWord ++ tailWord_741985).sum := by decide
  have hdescent : baseEnd_741985 < baseStart_741985 := by decide
  rcases family_descends (prefixWord ++ tailWord_741985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742016 : List Nat := [2, 1, 1, 2, 1, 5, 4, 4]
def baseStart_742016 : Nat := 118140960795 + 742016 * 2 ^ 59
def prefixEnd_742016 : Nat := 4983230072969 + 3 ^ 40 * 742016 * 2
def baseEnd_742016 : Nat := 112892107059755286722233

theorem tailTrace_742016 : CollatzResearch.WordTrace tailWord_742016 prefixEnd_742016 112892107059755286722233 := by
  unfold tailWord_742016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13531773439905116544358951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18042364586540155392478601 13531773439905116544358951)
  ·
    refine ⟨20297660159857674816538427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13531773439905116544358951 20297660159857674816538427)
    ·
      refine ⟨30446490239786512224807641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20297660159857674816538427 30446490239786512224807641)
      ·
        refine ⟨22834867679839884168605731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30446490239786512224807641 22834867679839884168605731)
        ·
          refine ⟨34252301519759826252908597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22834867679839884168605731 34252301519759826252908597)
          ·
            refine ⟨3211153267477483711210181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34252301519759826252908597 3211153267477483711210181)
            ·
              refine ⟨602091237652028195851909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3211153267477483711210181 602091237652028195851909)
              ·
                refine ⟨112892107059755286722233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 602091237652028195851909 112892107059755286722233)
                ·
                  rfl

theorem cell20_742016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_742016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742016 prefixEnd_742016 := by exact prefixLift 742016
  have htrace : WordTrace (prefixWord ++ tailWord_742016) baseStart_742016 baseEnd_742016 := by
    simpa [prefixWord, tailWord_742016, baseEnd_742016] using wordTrace_append hprefix tailTrace_742016
  have hstable : (prefixWord ++ tailWord_742016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742016).length < 2 ^ (prefixWord ++ tailWord_742016).sum := by decide
  have hdescent : baseEnd_742016 < baseStart_742016 := by decide
  rcases family_descends (prefixWord ++ tailWord_742016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742018 : List Nat := [3, 4, 3, 1, 1, 2, 1, 3, 2]
def baseStart_742018 : Nat := 118140960795 + 742018 * 2 ^ 59
def prefixEnd_742018 : Nat := 4983230072969 + 3 ^ 40 * 742018 * 2
def baseEnd_742018 : Nat := 338677234033762742100025

theorem tailTrace_742018 : CollatzResearch.WordTrace tailWord_742018 prefixEnd_742018 338677234033762742100025 := by
  unfold tailWord_742018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6765904956450746857572677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18042413217201991620193805 6765904956450746857572677)
  ·
    refine ⟨1268607179334515035794877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6765904956450746857572677 1268607179334515035794877)
    ·
      refine ⟨475727692250443138423079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1268607179334515035794877 475727692250443138423079)
      ·
        refine ⟨713591538375664707634619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475727692250443138423079 713591538375664707634619)
        ·
          refine ⟨1070387307563497061451929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713591538375664707634619 1070387307563497061451929)
          ·
            refine ⟨802790480672622796088947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070387307563497061451929 802790480672622796088947)
            ·
              refine ⟨1204185721008934194133421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802790480672622796088947 1204185721008934194133421)
              ·
                refine ⟨451569645378350322800033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1204185721008934194133421 451569645378350322800033)
                ·
                  refine ⟨338677234033762742100025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451569645378350322800033 338677234033762742100025)
                  ·
                    rfl

theorem cell20_742018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_742018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742018 prefixEnd_742018 := by exact prefixLift 742018
  have htrace : WordTrace (prefixWord ++ tailWord_742018) baseStart_742018 baseEnd_742018 := by
    simpa [prefixWord, tailWord_742018, baseEnd_742018] using wordTrace_append hprefix tailTrace_742018
  have hstable : (prefixWord ++ tailWord_742018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742018).length < 2 ^ (prefixWord ++ tailWord_742018).sum := by decide
  have hdescent : baseEnd_742018 < baseStart_742018 := by decide
  rcases family_descends (prefixWord ++ tailWord_742018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742098 : List Nat := [3, 2, 2, 2, 3, 2, 2, 2, 2]
def baseStart_742098 : Nat := 118140960795 + 742098 * 2 ^ 59
def prefixEnd_742098 : Nat := 4983230072969 + 3 ^ 40 * 742098 * 2
def baseEnd_742098 : Nat := 338713748213638019433031

theorem tailTrace_742098 : CollatzResearch.WordTrace tailWord_742098 prefixEnd_742098 338713748213638019433031 := by
  unfold tailWord_742098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6766634416378290273300737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18044358443675440728801965 6766634416378290273300737)
  ·
    refine ⟨5074975812283717704975553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6766634416378290273300737 5074975812283717704975553)
    ·
      refine ⟨3806231859212788278731665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5074975812283717704975553 3806231859212788278731665)
      ·
        refine ⟨2854673894409591209048749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3806231859212788278731665 2854673894409591209048749)
        ·
          refine ⟨1070502710403596703393281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2854673894409591209048749 1070502710403596703393281)
          ·
            refine ⟨802877032802697527544961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070502710403596703393281 802877032802697527544961)
            ·
              refine ⟨602157774602023145658721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802877032802697527544961 602157774602023145658721)
              ·
                refine ⟨451618330951517359244041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602157774602023145658721 451618330951517359244041)
                ·
                  refine ⟨338713748213638019433031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451618330951517359244041 338713748213638019433031)
                  ·
                    rfl

theorem cell20_742098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_742098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742098 prefixEnd_742098 := by exact prefixLift 742098
  have htrace : WordTrace (prefixWord ++ tailWord_742098) baseStart_742098 baseEnd_742098 := by
    simpa [prefixWord, tailWord_742098, baseEnd_742098] using wordTrace_append hprefix tailTrace_742098
  have hstable : (prefixWord ++ tailWord_742098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742098).length < 2 ^ (prefixWord ++ tailWord_742098).sum := by decide
  have hdescent : baseEnd_742098 < baseStart_742098 := by decide
  rcases family_descends (prefixWord ++ tailWord_742098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742106 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_742106 : Nat := 118140960795 + 742106 * 2 ^ 59
def prefixEnd_742106 : Nat := 4983230072969 + 3 ^ 40 * 742106 * 2
def baseEnd_742106 : Nat := 338717399631625547166331

theorem tailTrace_742106 : CollatzResearch.WordTrace tailWord_742106 prefixEnd_742106 338717399631625547166331 := by
  unfold tailWord_742106
  simp only [CollatzResearch.WordTrace]
  refine ⟨6766707362371044614873543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18044552966322785639662781 6766707362371044614873543)
  ·
    refine ⟨10150061043556566922310315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6766707362371044614873543 10150061043556566922310315)
    ·
      refine ⟨15225091565334850383465473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10150061043556566922310315 15225091565334850383465473)
      ·
        refine ⟨11418818674001137787599105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15225091565334850383465473 11418818674001137787599105)
        ·
          refine ⟨8564114005500853340699329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11418818674001137787599105 8564114005500853340699329)
          ·
            refine ⟨6423085504125640005524497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8564114005500853340699329 6423085504125640005524497)
            ·
              refine ⟨4817314128094230004143373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6423085504125640005524497 4817314128094230004143373)
              ·
                refine ⟨1806492798035336251553765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4817314128094230004143373 1806492798035336251553765)
                ·
                  refine ⟨338717399631625547166331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806492798035336251553765 338717399631625547166331)
                  ·
                    rfl

theorem cell20_742106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_742106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742106 prefixEnd_742106 := by exact prefixLift 742106
  have htrace : WordTrace (prefixWord ++ tailWord_742106) baseStart_742106 baseEnd_742106 := by
    simpa [prefixWord, tailWord_742106, baseEnd_742106] using wordTrace_append hprefix tailTrace_742106
  have hstable : (prefixWord ++ tailWord_742106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742106).length < 2 ^ (prefixWord ++ tailWord_742106).sum := by decide
  have hdescent : baseEnd_742106 < baseStart_742106 := by decide
  rcases family_descends (prefixWord ++ tailWord_742106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742140 : List Nat := [2, 2, 2, 1, 3, 3, 2, 3, 2]
def baseStart_742140 : Nat := 118140960795 + 742140 * 2 ^ 59
def prefixEnd_742140 : Nat := 4983230072969 + 3 ^ 40 * 742140 * 2
def baseEnd_742140 : Nat := 338732918158072540032859

theorem tailTrace_742140 : CollatzResearch.WordTrace tailWord_742140 prefixEnd_742140 338732918158072540032859 := by
  unfold tailWord_742140
  simp only [CollatzResearch.WordTrace]
  refine ⟨13534034765680501133115937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18045379687574001510821249 13534034765680501133115937)
  ·
    refine ⟨10150526074260375849836953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13534034765680501133115937 10150526074260375849836953)
    ·
      refine ⟨7612894555695281887377715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10150526074260375849836953 7612894555695281887377715)
      ·
        refine ⟨11419341833542922831066573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7612894555695281887377715 11419341833542922831066573)
        ·
          refine ⟨4282253187578596061649965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11419341833542922831066573 4282253187578596061649965)
          ·
            refine ⟨1605844945341973523118737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4282253187578596061649965 1605844945341973523118737)
            ·
              refine ⟨1204383709006480142339053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1605844945341973523118737 1204383709006480142339053)
              ·
                refine ⟨451643890877430053377145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1204383709006480142339053 451643890877430053377145)
                ·
                  refine ⟨338732918158072540032859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451643890877430053377145 338732918158072540032859)
                  ·
                    rfl

theorem cell20_742140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_742140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742140 prefixEnd_742140 := by exact prefixLift 742140
  have htrace : WordTrace (prefixWord ++ tailWord_742140) baseStart_742140 baseEnd_742140 := by
    simpa [prefixWord, tailWord_742140, baseEnd_742140] using wordTrace_append hprefix tailTrace_742140
  have hstable : (prefixWord ++ tailWord_742140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742140).length < 2 ^ (prefixWord ++ tailWord_742140).sum := by decide
  have hdescent : baseEnd_742140 < baseStart_742140 := by decide
  rcases family_descends (prefixWord ++ tailWord_742140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742161 : List Nat := [1, 2, 2, 1, 1, 3, 4, 4, 2]
def baseStart_742161 : Nat := 118140960795 + 742161 * 2 ^ 59
def prefixEnd_742161 : Nat := 4983230072969 + 3 ^ 40 * 742161 * 2
def baseEnd_742161 : Nat := 338742503130289800332773

theorem tailTrace_742161 : CollatzResearch.WordTrace tailWord_742161 prefixEnd_742161 338742503130289800332773 := by
  unfold tailWord_742161
  simp only [CollatzResearch.WordTrace]
  refine ⟨27068835464284922852746337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18045890309523281901830891 27068835464284922852746337)
  ·
    refine ⟨20301626598213692139559753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27068835464284922852746337 20301626598213692139559753)
    ·
      refine ⟨15226219948660269104669815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20301626598213692139559753 15226219948660269104669815)
      ·
        refine ⟨22839329922990403657004723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15226219948660269104669815 22839329922990403657004723)
        ·
          refine ⟨34258994884485605485507085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22839329922990403657004723 34258994884485605485507085)
          ·
            refine ⟨12847123081682102057065157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34258994884485605485507085 12847123081682102057065157)
            ·
              refine ⟨2408835577815394135699717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12847123081682102057065157 2408835577815394135699717)
              ·
                refine ⟨451656670840386400443697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2408835577815394135699717 451656670840386400443697)
                ·
                  refine ⟨338742503130289800332773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451656670840386400443697 338742503130289800332773)
                  ·
                    rfl

theorem cell20_742161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 2].length) (baseStart_742161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742161 prefixEnd_742161 := by exact prefixLift 742161
  have htrace : WordTrace (prefixWord ++ tailWord_742161) baseStart_742161 baseEnd_742161 := by
    simpa [prefixWord, tailWord_742161, baseEnd_742161] using wordTrace_append hprefix tailTrace_742161
  have hstable : (prefixWord ++ tailWord_742161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742161).length < 2 ^ (prefixWord ++ tailWord_742161).sum := by decide
  have hdescent : baseEnd_742161 < baseStart_742161 := by decide
  rcases family_descends (prefixWord ++ tailWord_742161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742212 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 4]
def baseStart_742212 : Nat := 118140960795 + 742212 * 2 ^ 59
def prefixEnd_742212 : Nat := 4983230072969 + 3 ^ 40 * 742212 * 2
def baseEnd_742212 : Nat := 338765780919960289632565

theorem tailTrace_742212 : CollatzResearch.WordTrace tailWord_742212 prefixEnd_742212 338765780919960289632565 := by
  unfold tailWord_742212
  simp only [CollatzResearch.WordTrace]
  refine ⟨13535347793550079281426445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18047130391400105708568593 13535347793550079281426445)
  ·
    refine ⟨5075755422581279730534917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13535347793550079281426445 5075755422581279730534917)
    ·
      refine ⟨951704141733989949475297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5075755422581279730534917 951704141733989949475297)
      ·
        refine ⟨713778106300492462106473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 951704141733989949475297 713778106300492462106473)
        ·
          refine ⟨535333579725369346579855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713778106300492462106473 535333579725369346579855)
          ·
            refine ⟨803000369588054019869783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535333579725369346579855 803000369588054019869783)
            ·
              refine ⟨1204500554382081029804675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803000369588054019869783 1204500554382081029804675)
              ·
                refine ⟨1806750831573121544707013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204500554382081029804675 1806750831573121544707013)
                ·
                  refine ⟨338765780919960289632565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1806750831573121544707013 338765780919960289632565)
                  ·
                    rfl

theorem cell20_742212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_742212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742212 prefixEnd_742212 := by exact prefixLift 742212
  have htrace : WordTrace (prefixWord ++ tailWord_742212) baseStart_742212 baseEnd_742212 := by
    simpa [prefixWord, tailWord_742212, baseEnd_742212] using wordTrace_append hprefix tailTrace_742212
  have hstable : (prefixWord ++ tailWord_742212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742212).length < 2 ^ (prefixWord ++ tailWord_742212).sum := by decide
  have hdescent : baseEnd_742212 < baseStart_742212 := by decide
  rcases family_descends (prefixWord ++ tailWord_742212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742216 : List Nat := [2, 1, 3, 1, 1, 3, 5, 2, 2]
def baseStart_742216 : Nat := 118140960795 + 742216 * 2 ^ 59
def prefixEnd_742216 : Nat := 4983230072969 + 3 ^ 40 * 742216 * 2
def baseEnd_742216 : Nat := 338767606628954053499215

theorem tailTrace_742216 : CollatzResearch.WordTrace tailWord_742216 prefixEnd_742216 338767606628954053499215 := by
  unfold tailWord_742216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13535420739542833622999251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18047227652723778163999001 13535420739542833622999251)
  ·
    refine ⟨20303131109314250434498877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13535420739542833622999251 20303131109314250434498877)
    ·
      refine ⟨7613674165992843912937079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20303131109314250434498877 7613674165992843912937079)
      ·
        refine ⟨11420511248989265869405619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7613674165992843912937079 11420511248989265869405619)
        ·
          refine ⟨17130766873483898804108429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11420511248989265869405619 17130766873483898804108429)
          ·
            refine ⟨6424037577556462051540661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17130766873483898804108429 6424037577556462051540661)
            ·
              refine ⟨602253522895918317331937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6424037577556462051540661 602253522895918317331937)
              ·
                refine ⟨451690142171938737998953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602253522895918317331937 451690142171938737998953)
                ·
                  refine ⟨338767606628954053499215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451690142171938737998953 338767606628954053499215)
                  ·
                    rfl

theorem cell20_742216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 2].length) (baseStart_742216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742216 prefixEnd_742216 := by exact prefixLift 742216
  have htrace : WordTrace (prefixWord ++ tailWord_742216) baseStart_742216 baseEnd_742216 := by
    simpa [prefixWord, tailWord_742216, baseEnd_742216] using wordTrace_append hprefix tailTrace_742216
  have hstable : (prefixWord ++ tailWord_742216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742216).length < 2 ^ (prefixWord ++ tailWord_742216).sum := by decide
  have hdescent : baseEnd_742216 < baseStart_742216 := by decide
  rcases family_descends (prefixWord ++ tailWord_742216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742275 : List Nat := [1, 1, 1, 3, 4, 1, 3, 4, 2]
def baseStart_742275 : Nat := 118140960795 + 742275 * 2 ^ 59
def prefixEnd_742275 : Nat := 4983230072969 + 3 ^ 40 * 742275 * 2
def baseEnd_742275 : Nat := 338794535836612070532307

theorem tailTrace_742275 : CollatzResearch.WordTrace tailWord_742275 prefixEnd_742275 338794535836612070532307 := by
  unfold tailWord_742275
  simp only [CollatzResearch.WordTrace]
  refine ⟨27072993385871920322396279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18048662257247946881597519 27072993385871920322396279)
  ·
    refine ⟨40609490078807880483594419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27072993385871920322396279 40609490078807880483594419)
    ·
      refine ⟨60914235118211820725391629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40609490078807880483594419 60914235118211820725391629)
      ·
        refine ⟨22842838169329432772021861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60914235118211820725391629 22842838169329432772021861)
        ·
          refine ⟨4283032156749268644754099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22842838169329432772021861 4283032156749268644754099)
          ·
            refine ⟨6424548235123902967131149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283032156749268644754099 6424548235123902967131149)
            ·
              refine ⟨2409205588171463612674181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6424548235123902967131149 2409205588171463612674181)
              ·
                refine ⟨451726047782149427376409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2409205588171463612674181 451726047782149427376409)
                ·
                  refine ⟨338794535836612070532307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451726047782149427376409 338794535836612070532307)
                  ·
                    rfl

theorem cell20_742275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 2].length) (baseStart_742275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742275 prefixEnd_742275 := by exact prefixLift 742275
  have htrace : WordTrace (prefixWord ++ tailWord_742275) baseStart_742275 baseEnd_742275 := by
    simpa [prefixWord, tailWord_742275, baseEnd_742275] using wordTrace_append hprefix tailTrace_742275
  have hstable : (prefixWord ++ tailWord_742275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742275).length < 2 ^ (prefixWord ++ tailWord_742275).sum := by decide
  have hdescent : baseEnd_742275 < baseStart_742275 := by decide
  rcases family_descends (prefixWord ++ tailWord_742275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742282 : List Nat := [3, 1, 2, 4, 1, 1, 3, 5]
def baseStart_742282 : Nat := 118140960795 + 742282 * 2 ^ 59
def prefixEnd_742282 : Nat := 4983230072969 + 3 ^ 40 * 742282 * 2
def baseEnd_742282 : Nat := 112932576942450385766315

theorem tailTrace_742282 : CollatzResearch.WordTrace tailWord_742282 prefixEnd_742282 112932576942450385766315 := by
  unfold tailWord_742282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6768312174211640129475275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18048832464564373678600733 6768312174211640129475275)
  ·
    refine ⟨10152468261317460194212913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6768312174211640129475275 10152468261317460194212913)
    ·
      refine ⟨7614351195988095145659685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10152468261317460194212913 7614351195988095145659685)
      ·
        refine ⟨1427690849247767839811191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7614351195988095145659685 1427690849247767839811191)
        ·
          refine ⟨2141536273871651759716787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427690849247767839811191 2141536273871651759716787)
          ·
            refine ⟨3212304410807477639575181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141536273871651759716787 3212304410807477639575181)
            ·
              refine ⟨1204614154052804114840693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3212304410807477639575181 1204614154052804114840693)
              ·
                refine ⟨112932576942450385766315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1204614154052804114840693 112932576942450385766315)
                ·
                  rfl

theorem cell20_742282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_742282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742282 prefixEnd_742282 := by exact prefixLift 742282
  have htrace : WordTrace (prefixWord ++ tailWord_742282) baseStart_742282 baseEnd_742282 := by
    simpa [prefixWord, tailWord_742282, baseEnd_742282] using wordTrace_append hprefix tailTrace_742282
  have hstable : (prefixWord ++ tailWord_742282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742282).length < 2 ^ (prefixWord ++ tailWord_742282).sum := by decide
  have hdescent : baseEnd_742282 < baseStart_742282 := by decide
  rcases family_descends (prefixWord ++ tailWord_742282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742313 : List Nat := [1, 2, 1, 1, 1, 1, 8, 3, 2]
def baseStart_742313 : Nat := 118140960795 + 742313 * 2 ^ 59
def prefixEnd_742313 : Nat := 4983230072969 + 3 ^ 40 * 742313 * 2
def baseEnd_742313 : Nat := 338811880072052827265485

theorem tailTrace_742313 : CollatzResearch.WordTrace tailWord_742313 prefixEnd_742313 338811880072052827265485 := by
  unfold tailWord_742313
  simp only [CollatzResearch.WordTrace]
  refine ⟨27074379359734252812279593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18049586239822835208186395 27074379359734252812279593)
  ·
    refine ⟨20305784519800689609209695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27074379359734252812279593 20305784519800689609209695)
    ·
      refine ⟨30458676779701034413814543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20305784519800689609209695 30458676779701034413814543)
      ·
        refine ⟨45688015169551551620721815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30458676779701034413814543 45688015169551551620721815)
        ·
          refine ⟨68532022754327327431082723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45688015169551551620721815 68532022754327327431082723)
          ·
            refine ⟨102798034131490991146624085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68532022754327327431082723 102798034131490991146624085)
            ·
              refine ⟨1204664462478410052499501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 102798034131490991146624085 1204664462478410052499501)
              ·
                refine ⟨451749173429403769687313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1204664462478410052499501 451749173429403769687313)
                ·
                  refine ⟨338811880072052827265485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451749173429403769687313 338811880072052827265485)
                  ·
                    rfl

theorem cell20_742313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 2].length) (baseStart_742313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742313 prefixEnd_742313 := by exact prefixLift 742313
  have htrace : WordTrace (prefixWord ++ tailWord_742313) baseStart_742313 baseEnd_742313 := by
    simpa [prefixWord, tailWord_742313, baseEnd_742313] using wordTrace_append hprefix tailTrace_742313
  have hstable : (prefixWord ++ tailWord_742313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742313).length < 2 ^ (prefixWord ++ tailWord_742313).sum := by decide
  have hdescent : baseEnd_742313 < baseStart_742313 := by decide
  rcases family_descends (prefixWord ++ tailWord_742313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742326 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_742326 : Nat := 118140960795 + 742326 * 2 ^ 59
def prefixEnd_742326 : Nat := 4983230072969 + 3 ^ 40 * 742326 * 2
def baseEnd_742326 : Nat := 338817813626282559832099

theorem tailTrace_742326 : CollatzResearch.WordTrace tailWord_742326 prefixEnd_742326 338817813626282559832099 := by
  unfold tailWord_742326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692178344292947252031427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18049902339124770688335221 1692178344292947252031427)
  ·
    refine ⟨2538267516439420878047141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1692178344292947252031427 2538267516439420878047141)
    ·
      refine ⟨475925159332391414633839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2538267516439420878047141 475925159332391414633839)
      ·
        refine ⟨713887738998587121950759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475925159332391414633839 713887738998587121950759)
        ·
          refine ⟨1070831608497880682926139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713887738998587121950759 1070831608497880682926139)
          ·
            refine ⟨1606247412746821024389209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070831608497880682926139 1606247412746821024389209)
            ·
              refine ⟨1204685559560115768291907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606247412746821024389209 1204685559560115768291907)
              ·
                refine ⟨1807028339340173652437861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204685559560115768291907 1807028339340173652437861)
                ·
                  refine ⟨338817813626282559832099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1807028339340173652437861 338817813626282559832099)
                  ·
                    rfl

theorem cell20_742326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_742326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742326 prefixEnd_742326 := by exact prefixLift 742326
  have htrace : WordTrace (prefixWord ++ tailWord_742326) baseStart_742326 baseEnd_742326 := by
    simpa [prefixWord, tailWord_742326, baseEnd_742326] using wordTrace_append hprefix tailTrace_742326
  have hstable : (prefixWord ++ tailWord_742326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742326).length < 2 ^ (prefixWord ++ tailWord_742326).sum := by decide
  have hdescent : baseEnd_742326 < baseStart_742326 := by decide
  rcases family_descends (prefixWord ++ tailWord_742326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742327 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 3]
def baseStart_742327 : Nat := 118140960795 + 742327 * 2 ^ 59
def prefixEnd_742327 : Nat := 4983230072969 + 3 ^ 40 * 742327 * 2
def baseEnd_742327 : Nat := 338818270053531000798761

theorem tailTrace_742327 : CollatzResearch.WordTrace tailWord_742327 prefixEnd_742327 338818270053531000798761 := by
  unfold tailWord_742327
  simp only [CollatzResearch.WordTrace]
  refine ⟨27074889981683533203289235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18049926654455688802192823 27074889981683533203289235)
  ·
    refine ⟨40612334972525299804933853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27074889981683533203289235 40612334972525299804933853)
    ·
      refine ⟨15229625614696987426850195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40612334972525299804933853 15229625614696987426850195)
      ·
        refine ⟨22844438422045481140275293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15229625614696987426850195 22844438422045481140275293)
        ·
          refine ⟨8566664408267055427603235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22844438422045481140275293 8566664408267055427603235)
          ·
            refine ⟨12849996612400583141404853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8566664408267055427603235 12849996612400583141404853)
            ·
              refine ⟨1204687182412554669506705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12849996612400583141404853 1204687182412554669506705)
              ·
                refine ⟨903515386809416002130029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1204687182412554669506705 903515386809416002130029)
                ·
                  refine ⟨338818270053531000798761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903515386809416002130029 338818270053531000798761)
                  ·
                    rfl

theorem cell20_742327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 3].length) (baseStart_742327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742327 prefixEnd_742327 := by exact prefixLift 742327
  have htrace : WordTrace (prefixWord ++ tailWord_742327) baseStart_742327 baseEnd_742327 := by
    simpa [prefixWord, tailWord_742327, baseEnd_742327] using wordTrace_append hprefix tailTrace_742327
  have hstable : (prefixWord ++ tailWord_742327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742327).length < 2 ^ (prefixWord ++ tailWord_742327).sum := by decide
  have hdescent : baseEnd_742327 < baseStart_742327 := by decide
  rcases family_descends (prefixWord ++ tailWord_742327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742340 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 3]
def baseStart_742340 : Nat := 118140960795 + 742340 * 2 ^ 59
def prefixEnd_742340 : Nat := 4983230072969 + 3 ^ 40 * 742340 * 2
def baseEnd_742340 : Nat := 338824203607760733365375

theorem tailTrace_742340 : CollatzResearch.WordTrace tailWord_742340 prefixEnd_742340 338824203607760733365375 := by
  unfold tailWord_742340
  simp only [CollatzResearch.WordTrace]
  refine ⟨13537682065318218211756237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18050242753757624282341649 13537682065318218211756237)
  ·
    refine ⟨5076630774494331829408589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13537682065318218211756237 5076630774494331829408589)
    ·
      refine ⟨1903736540435374436028221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5076630774494331829408589 1903736540435374436028221)
      ·
        refine ⟨713901202663265413510583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1903736540435374436028221 713901202663265413510583)
        ·
          refine ⟨1070851803994898120265875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713901202663265413510583 1070851803994898120265875)
          ·
            refine ⟨1606277705992347180398813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070851803994898120265875 1606277705992347180398813)
            ·
              refine ⟨602354139747130192649555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1606277705992347180398813 602354139747130192649555)
              ·
                refine ⟨903531209620695288974333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602354139747130192649555 903531209620695288974333)
                ·
                  refine ⟨338824203607760733365375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903531209620695288974333 338824203607760733365375)
                  ·
                    rfl

theorem cell20_742340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_742340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742340 prefixEnd_742340 := by exact prefixLift 742340
  have htrace : WordTrace (prefixWord ++ tailWord_742340) baseStart_742340 baseEnd_742340 := by
    simpa [prefixWord, tailWord_742340, baseEnd_742340] using wordTrace_append hprefix tailTrace_742340
  have hstable : (prefixWord ++ tailWord_742340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742340).length < 2 ^ (prefixWord ++ tailWord_742340).sum := by decide
  have hdescent : baseEnd_742340 < baseStart_742340 := by decide
  rcases family_descends (prefixWord ++ tailWord_742340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742365 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 5]
def baseStart_742365 : Nat := 118140960795 + 742365 * 2 ^ 59
def prefixEnd_742365 : Nat := 4983230072969 + 3 ^ 40 * 742365 * 2
def baseEnd_742365 : Nat := 338835614288971757531939

theorem tailTrace_742365 : CollatzResearch.WordTrace tailWord_742365 prefixEnd_742365 338835614288971757531939 := by
  unfold tailWord_742365
  simp only [CollatzResearch.WordTrace]
  refine ⟨27076275955545865693172549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18050850637030577128781699 27076275955545865693172549)
  ·
    refine ⟨5076801741664849817469853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27076275955545865693172549 5076801741664849817469853)
    ·
      refine ⟨1903800653124318681551195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5076801741664849817469853 1903800653124318681551195)
      ·
        refine ⟨2855700979686478022326793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1903800653124318681551195 2855700979686478022326793)
        ·
          refine ⟨2141775734764858516745095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2855700979686478022326793 2141775734764858516745095)
          ·
            refine ⟨3212663602147287775117643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141775734764858516745095 3212663602147287775117643)
            ·
              refine ⟨4818995403220931662676465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212663602147287775117643 4818995403220931662676465)
              ·
                refine ⟨3614246552415698747007349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4818995403220931662676465 3614246552415698747007349)
                ·
                  refine ⟨338835614288971757531939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3614246552415698747007349 338835614288971757531939)
                  ·
                    rfl

theorem cell20_742365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_742365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742365 prefixEnd_742365 := by exact prefixLift 742365
  have htrace : WordTrace (prefixWord ++ tailWord_742365) baseStart_742365 baseEnd_742365 := by
    simpa [prefixWord, tailWord_742365, baseEnd_742365] using wordTrace_append hprefix tailTrace_742365
  have hstable : (prefixWord ++ tailWord_742365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742365).length < 2 ^ (prefixWord ++ tailWord_742365).sum := by decide
  have hdescent : baseEnd_742365 < baseStart_742365 := by decide
  rcases family_descends (prefixWord ++ tailWord_742365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742465 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 4]
def baseStart_742465 : Nat := 118140960795 + 742465 * 2 ^ 59
def prefixEnd_742465 : Nat := 4983230072969 + 3 ^ 40 * 742465 * 2
def baseEnd_742465 : Nat := 338881257013815854198197

theorem tailTrace_742465 : CollatzResearch.WordTrace tailWord_742465 prefixEnd_742465 338881257013815854198197 := by
  unfold tailWord_742465
  simp only [CollatzResearch.WordTrace]
  refine ⟨27079923255183582771812849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18053282170122388514541899 27079923255183582771812849)
  ·
    refine ⟨20309942441387687078859637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27079923255183582771812849 20309942441387687078859637)
    ·
      refine ⟨1904057103880095663643091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20309942441387687078859637 1904057103880095663643091)
      ·
        refine ⟨2856085655820143495464637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1904057103880095663643091 2856085655820143495464637)
        ·
          refine ⟨1071032120932553810799239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2856085655820143495464637 1071032120932553810799239)
          ·
            refine ⟨1606548181398830716198859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071032120932553810799239 1606548181398830716198859)
            ·
              refine ⟨2409822272098246074298289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606548181398830716198859 2409822272098246074298289)
              ·
                refine ⟨1807366704073684555723717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2409822272098246074298289 1807366704073684555723717)
                ·
                  refine ⟨338881257013815854198197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1807366704073684555723717 338881257013815854198197)
                  ·
                    rfl

theorem cell20_742465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_742465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742465 prefixEnd_742465 := by exact prefixLift 742465
  have htrace : WordTrace (prefixWord ++ tailWord_742465) baseStart_742465 baseEnd_742465 := by
    simpa [prefixWord, tailWord_742465, baseEnd_742465] using wordTrace_append hprefix tailTrace_742465
  have hstable : (prefixWord ++ tailWord_742465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742465).length < 2 ^ (prefixWord ++ tailWord_742465).sum := by decide
  have hdescent : baseEnd_742465 < baseStart_742465 := by decide
  rcases family_descends (prefixWord ++ tailWord_742465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742469 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 6]
def baseStart_742469 : Nat := 118140960795 + 742469 * 2 ^ 59
def prefixEnd_742469 : Nat := 4983230072969 + 3 ^ 40 * 742469 * 2
def baseEnd_742469 : Nat := 338883082722809618064847

theorem tailTrace_742469 : CollatzResearch.WordTrace tailWord_742469 prefixEnd_742469 338883082722809618064847 := by
  unfold tailWord_742469
  simp only [CollatzResearch.WordTrace]
  refine ⟨27080069147169091454958461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18053379431446060969972307 27080069147169091454958461)
  ·
    refine ⟨10155025930188409295609423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27080069147169091454958461 10155025930188409295609423)
    ·
      refine ⟨15232538895282613943414135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10155025930188409295609423 15232538895282613943414135)
      ·
        refine ⟨22848808342923920915121203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15232538895282613943414135 22848808342923920915121203)
        ·
          refine ⟨34273212514385881372681805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22848808342923920915121203 34273212514385881372681805)
          ·
            refine ⟨12852454692894705514755677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34273212514385881372681805 12852454692894705514755677)
            ·
              refine ⟨4819670509835514568033379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12852454692894705514755677 4819670509835514568033379)
              ·
                refine ⟨7229505764753271852050069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819670509835514568033379 7229505764753271852050069)
                ·
                  refine ⟨338883082722809618064847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7229505764753271852050069 338883082722809618064847)
                  ·
                    rfl

theorem cell20_742469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_742469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742469 prefixEnd_742469 := by exact prefixLift 742469
  have htrace : WordTrace (prefixWord ++ tailWord_742469) baseStart_742469 baseEnd_742469 := by
    simpa [prefixWord, tailWord_742469, baseEnd_742469] using wordTrace_append hprefix tailTrace_742469
  have hstable : (prefixWord ++ tailWord_742469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742469).length < 2 ^ (prefixWord ++ tailWord_742469).sum := by decide
  have hdescent : baseEnd_742469 < baseStart_742469 := by decide
  rcases family_descends (prefixWord ++ tailWord_742469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742482 : List Nat := [3, 2, 2, 1, 3, 2, 2, 3, 2]
def baseStart_742482 : Nat := 118140960795 + 742482 * 2 ^ 59
def prefixEnd_742482 : Nat := 4983230072969 + 3 ^ 40 * 742482 * 2
def baseEnd_742482 : Nat := 338889016277039350631461

theorem tailTrace_742482 : CollatzResearch.WordTrace tailWord_742482 prefixEnd_742482 338889016277039350631461 := by
  unfold tailWord_742482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6770135824030498668795425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18053695530747996450121133 6770135824030498668795425)
  ·
    refine ⟨5077601868022874001596569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6770135824030498668795425 5077601868022874001596569)
    ·
      refine ⟨3808201401017155501197427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5077601868022874001596569 3808201401017155501197427)
      ·
        refine ⟨5712302101525733251796141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3808201401017155501197427 5712302101525733251796141)
        ·
          refine ⟨2142113288072149969423553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5712302101525733251796141 2142113288072149969423553)
          ·
            refine ⟨1606584966054112477067665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2142113288072149969423553 1606584966054112477067665)
            ·
              refine ⟨1204938724540584357800749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606584966054112477067665 1204938724540584357800749)
              ·
                refine ⟨451852021702719134175281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1204938724540584357800749 451852021702719134175281)
                ·
                  refine ⟨338889016277039350631461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451852021702719134175281 338889016277039350631461)
                  ·
                    rfl

theorem cell20_742482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_742482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742482 prefixEnd_742482 := by exact prefixLift 742482
  have htrace : WordTrace (prefixWord ++ tailWord_742482) baseStart_742482 baseEnd_742482 := by
    simpa [prefixWord, tailWord_742482, baseEnd_742482] using wordTrace_append hprefix tailTrace_742482
  have hstable : (prefixWord ++ tailWord_742482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742482).length < 2 ^ (prefixWord ++ tailWord_742482).sum := by decide
  have hdescent : baseEnd_742482 < baseStart_742482 := by decide
  rcases family_descends (prefixWord ++ tailWord_742482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742503 : List Nat := [1, 1, 5, 1, 1, 3, 2, 4, 2]
def baseStart_742503 : Nat := 118140960795 + 742503 * 2 ^ 59
def prefixEnd_742503 : Nat := 4983230072969 + 3 ^ 40 * 742503 * 2
def baseEnd_742503 : Nat := 338898601249256610931375

theorem tailTrace_742503 : CollatzResearch.WordTrace tailWord_742503 prefixEnd_742503 338898601249256610931375 := by
  unfold tailWord_742503
  simp only [CollatzResearch.WordTrace]
  refine ⟨27081309229045915261696163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18054206152697276841130775 27081309229045915261696163)
  ·
    refine ⟨40621963843568872892544245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27081309229045915261696163 40621963843568872892544245)
    ·
      refine ⟨3808309110334581833676023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40621963843568872892544245 3808309110334581833676023)
      ·
        refine ⟨5712463665501872750514035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3808309110334581833676023 5712463665501872750514035)
        ·
          refine ⟨8568695498252809125771053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5712463665501872750514035 8568695498252809125771053)
          ·
            refine ⟨3213260811844803422164145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8568695498252809125771053 3213260811844803422164145)
            ·
              refine ⟨2409945608883602566623109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3213260811844803422164145 2409945608883602566623109)
              ·
                refine ⟨451864801665675481241833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2409945608883602566623109 451864801665675481241833)
                ·
                  refine ⟨338898601249256610931375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451864801665675481241833 338898601249256610931375)
                  ·
                    rfl

theorem cell20_742503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 2].length) (baseStart_742503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742503 prefixEnd_742503 := by exact prefixLift 742503
  have htrace : WordTrace (prefixWord ++ tailWord_742503) baseStart_742503 baseEnd_742503 := by
    simpa [prefixWord, tailWord_742503, baseEnd_742503] using wordTrace_append hprefix tailTrace_742503
  have hstable : (prefixWord ++ tailWord_742503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742503).length < 2 ^ (prefixWord ++ tailWord_742503).sum := by decide
  have hdescent : baseEnd_742503 < baseStart_742503 := by decide
  rcases family_descends (prefixWord ++ tailWord_742503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742538 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_742538 : Nat := 118140960795 + 742538 * 2 ^ 59
def prefixEnd_742538 : Nat := 4983230072969 + 3 ^ 40 * 742538 * 2
def baseEnd_742538 : Nat := 338914576202952044764565

theorem tailTrace_742538 : CollatzResearch.WordTrace tailWord_742538 prefixEnd_742538 338914576202952044764565 := by
  unfold tailWord_742538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6770646445979779059805067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18055057189279410826146845 6770646445979779059805067)
  ·
    refine ⟨10155969668969668589707601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6770646445979779059805067 10155969668969668589707601)
    ·
      refine ⟨7616977251727251442280701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10155969668969668589707601 7616977251727251442280701)
      ·
        refine ⟨2856366469397719290855263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7616977251727251442280701 2856366469397719290855263)
        ·
          refine ⟨4284549704096578936282895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2856366469397719290855263 4284549704096578936282895)
          ·
            refine ⟨6426824556144868404424343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4284549704096578936282895 6426824556144868404424343)
            ·
              refine ⟨9640236834217302606636515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6426824556144868404424343 9640236834217302606636515)
              ·
                refine ⟨14460355251325953909954773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9640236834217302606636515 14460355251325953909954773)
                ·
                  refine ⟨338914576202952044764565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14460355251325953909954773 338914576202952044764565)
                  ·
                    rfl

theorem cell20_742538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_742538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742538 prefixEnd_742538 := by exact prefixLift 742538
  have htrace : WordTrace (prefixWord ++ tailWord_742538) baseStart_742538 baseEnd_742538 := by
    simpa [prefixWord, tailWord_742538, baseEnd_742538] using wordTrace_append hprefix tailTrace_742538
  have hstable : (prefixWord ++ tailWord_742538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742538).length < 2 ^ (prefixWord ++ tailWord_742538).sum := by decide
  have hdescent : baseEnd_742538 < baseStart_742538 := by decide
  rcases family_descends (prefixWord ++ tailWord_742538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742558 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_742558 : Nat := 118140960795 + 742558 * 2 ^ 59
def prefixEnd_742558 : Nat := 4983230072969 + 3 ^ 40 * 742558 * 2
def baseEnd_742558 : Nat := 338923704747920864097817

theorem tailTrace_742558 : CollatzResearch.WordTrace tailWord_742558 prefixEnd_742558 338923704747920864097817 := by
  unfold tailWord_742558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3385414405480832456868541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18055543495897773103298885 3385414405480832456868541)
  ·
    refine ⟨1269530402055312171325703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3385414405480832456868541 1269530402055312171325703)
    ·
      refine ⟨1904295603082968256988555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1269530402055312171325703 1904295603082968256988555)
      ·
        refine ⟨2856443404624452385482833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1904295603082968256988555 2856443404624452385482833)
        ·
          refine ⟨2142332553468339289112125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2856443404624452385482833 2142332553468339289112125)
          ·
            refine ⟨803374707550627233417047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2142332553468339289112125 803374707550627233417047)
            ·
              refine ⟨1205062061325940850125571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803374707550627233417047 1205062061325940850125571)
              ·
                refine ⟨1807593091988911275188357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205062061325940850125571 1807593091988911275188357)
                ·
                  refine ⟨338923704747920864097817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1807593091988911275188357 338923704747920864097817)
                  ·
                    rfl

theorem cell20_742558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_742558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742558 prefixEnd_742558 := by exact prefixLift 742558
  have htrace : WordTrace (prefixWord ++ tailWord_742558) baseStart_742558 baseEnd_742558 := by
    simpa [prefixWord, tailWord_742558, baseEnd_742558] using wordTrace_append hprefix tailTrace_742558
  have hstable : (prefixWord ++ tailWord_742558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742558).length < 2 ^ (prefixWord ++ tailWord_742558).sum := by decide
  have hdescent : baseEnd_742558 < baseStart_742558 := by decide
  rcases family_descends (prefixWord ++ tailWord_742558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742576 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 3]
def baseStart_742576 : Nat := 118140960795 + 742576 * 2 ^ 59
def prefixEnd_742576 : Nat := 4983230072969 + 3 ^ 40 * 742576 * 2
def baseEnd_742576 : Nat := 338931920438392801497743

theorem tailTrace_742576 : CollatzResearch.WordTrace tailWord_742576 prefixEnd_742576 338931920438392801497743 := by
  unfold tailWord_742576
  simp only [CollatzResearch.WordTrace]
  refine ⟨13541985878890724364551791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18055981171854299152735721 13541985878890724364551791)
  ·
    refine ⟨20312978818336086546827687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13541985878890724364551791 20312978818336086546827687)
    ·
      refine ⟨30469468227504129820241531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20312978818336086546827687 30469468227504129820241531)
      ·
        refine ⟨45704202341256194730362297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30469468227504129820241531 45704202341256194730362297)
        ·
          refine ⟨34278151755942146047771723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45704202341256194730362297 34278151755942146047771723)
          ·
            refine ⟨51417227633913219071657585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34278151755942146047771723 51417227633913219071657585)
            ·
              refine ⟨38562920725434914303743189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51417227633913219071657585 38562920725434914303743189)
              ·
                refine ⟨903818454502380803993981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38562920725434914303743189 903818454502380803993981)
                ·
                  refine ⟨338931920438392801497743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903818454502380803993981 338931920438392801497743)
                  ·
                    rfl

theorem cell20_742576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_742576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742576 prefixEnd_742576 := by exact prefixLift 742576
  have htrace : WordTrace (prefixWord ++ tailWord_742576) baseStart_742576 baseEnd_742576 := by
    simpa [prefixWord, tailWord_742576, baseEnd_742576] using wordTrace_append hprefix tailTrace_742576
  have hstable : (prefixWord ++ tailWord_742576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742576).length < 2 ^ (prefixWord ++ tailWord_742576).sum := by decide
  have hdescent : baseEnd_742576 < baseStart_742576 := by decide
  rcases family_descends (prefixWord ++ tailWord_742576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742583 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_742583 : Nat := 118140960795 + 742583 * 2 ^ 59
def prefixEnd_742583 : Nat := 4983230072969 + 3 ^ 40 * 742583 * 2
def baseEnd_742583 : Nat := 338935115429131888264381

theorem tailTrace_742583 : CollatzResearch.WordTrace tailWord_742583 prefixEnd_742583 338935115429131888264381 := by
  unfold tailWord_742583
  simp only [CollatzResearch.WordTrace]
  refine ⟨27084227068756088924608403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18056151379170725949738935 27084227068756088924608403)
  ·
    refine ⟨40626340603134133386912605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27084227068756088924608403 40626340603134133386912605)
    ·
      refine ⟨15234877726175300020092227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40626340603134133386912605 15234877726175300020092227)
      ·
        refine ⟨22852316589262950030138341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15234877726175300020092227 22852316589262950030138341)
        ·
          refine ⟨4284809360486803130650939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22852316589262950030138341 4284809360486803130650939)
          ·
            refine ⟨6427214040730204695976409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4284809360486803130650939 6427214040730204695976409)
            ·
              refine ⟨4820410530547653521982307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6427214040730204695976409 4820410530547653521982307)
              ·
                refine ⟨7230615795821480282973461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820410530547653521982307 7230615795821480282973461)
                ·
                  refine ⟨338935115429131888264381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7230615795821480282973461 338935115429131888264381)
                  ·
                    rfl

theorem cell20_742583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_742583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742583 prefixEnd_742583 := by exact prefixLift 742583
  have htrace : WordTrace (prefixWord ++ tailWord_742583) baseStart_742583 baseEnd_742583 := by
    simpa [prefixWord, tailWord_742583, baseEnd_742583] using wordTrace_append hprefix tailTrace_742583
  have hstable : (prefixWord ++ tailWord_742583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742583).length < 2 ^ (prefixWord ++ tailWord_742583).sum := by decide
  have hdescent : baseEnd_742583 < baseStart_742583 := by decide
  rcases family_descends (prefixWord ++ tailWord_742583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742613 : List Nat := [1, 3, 2, 4, 1, 3, 2, 2, 2]
def baseStart_742613 : Nat := 118140960795 + 742613 * 2 ^ 59
def prefixEnd_742613 : Nat := 4983230072969 + 3 ^ 40 * 742613 * 2
def baseEnd_742613 : Nat := 338948808246585117264259

theorem tailTrace_742613 : CollatzResearch.WordTrace tailWord_742613 prefixEnd_742613 338948808246585117264259 := by
  unfold tailWord_742613
  simp only [CollatzResearch.WordTrace]
  refine ⟨27085321258647404048200493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18056880839098269365466995 27085321258647404048200493)
  ·
    refine ⟨10156995471992776518075185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27085321258647404048200493 10156995471992776518075185)
    ·
      refine ⟨7617746603994582388556389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10156995471992776518075185 7617746603994582388556389)
      ·
        refine ⟨1428327488248984197854323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7617746603994582388556389 1428327488248984197854323)
        ·
          refine ⟨2142491232373476296781485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428327488248984197854323 2142491232373476296781485)
          ·
            refine ⟨803434212140053611293057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2142491232373476296781485 803434212140053611293057)
            ·
              refine ⟨602575659105040208469793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803434212140053611293057 602575659105040208469793)
              ·
                refine ⟨451931744328780156352345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602575659105040208469793 451931744328780156352345)
                ·
                  refine ⟨338948808246585117264259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451931744328780156352345 338948808246585117264259)
                  ·
                    rfl

theorem cell20_742613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_742613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742613 prefixEnd_742613 := by exact prefixLift 742613
  have htrace : WordTrace (prefixWord ++ tailWord_742613) baseStart_742613 baseEnd_742613 := by
    simpa [prefixWord, tailWord_742613, baseEnd_742613] using wordTrace_append hprefix tailTrace_742613
  have hstable : (prefixWord ++ tailWord_742613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742613).length < 2 ^ (prefixWord ++ tailWord_742613).sum := by decide
  have hdescent : baseEnd_742613 < baseStart_742613 := by decide
  rcases family_descends (prefixWord ++ tailWord_742613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742655 : List Nat := [1, 1, 2, 2, 1, 6, 2, 3, 2]
def baseStart_742655 : Nat := 118140960795 + 742655 * 2 ^ 59
def prefixEnd_742655 : Nat := 4983230072969 + 3 ^ 40 * 742655 * 2
def baseEnd_742655 : Nat := 338967978191019637864087

theorem tailTrace_742655 : CollatzResearch.WordTrace tailWord_742655 prefixEnd_742655 338967978191019637864087 := by
  unfold tailWord_742655
  simp only [CollatzResearch.WordTrace]
  refine ⟨27086853124495245221229419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18057902082996830147486279 27086853124495245221229419)
  ·
    refine ⟨40630279686742867831844129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27086853124495245221229419 40630279686742867831844129)
    ·
      refine ⟨30472709765057150873883097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40630279686742867831844129 30472709765057150873883097)
      ·
        refine ⟨22854532323792863155412323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30472709765057150873883097 22854532323792863155412323)
        ·
          refine ⟨34281798485689294733118485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22854532323792863155412323 34281798485689294733118485)
          ·
            refine ⟨1606959304016685690614929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34281798485689294733118485 1606959304016685690614929)
            ·
              refine ⟨1205219478012514267961197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606959304016685690614929 1205219478012514267961197)
              ·
                refine ⟨451957304254692850485449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1205219478012514267961197 451957304254692850485449)
                ·
                  refine ⟨338967978191019637864087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451957304254692850485449 338967978191019637864087)
                  ·
                    rfl

theorem cell20_742655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 2].length) (baseStart_742655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742655 prefixEnd_742655 := by exact prefixLift 742655
  have htrace : WordTrace (prefixWord ++ tailWord_742655) baseStart_742655 baseEnd_742655 := by
    simpa [prefixWord, tailWord_742655, baseEnd_742655] using wordTrace_append hprefix tailTrace_742655
  have hstable : (prefixWord ++ tailWord_742655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742655).length < 2 ^ (prefixWord ++ tailWord_742655).sum := by decide
  have hdescent : baseEnd_742655 < baseStart_742655 := by decide
  rcases family_descends (prefixWord ++ tailWord_742655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742704 : List Nat := [2, 1, 1, 1, 2, 2, 5, 6]
def baseStart_742704 : Nat := 118140960795 + 742704 * 2 ^ 59
def prefixEnd_742704 : Nat := 4983230072969 + 3 ^ 40 * 742704 * 2
def baseEnd_742704 : Nat := 112996781042064415076851

theorem tailTrace_742704 : CollatzResearch.WordTrace tailWord_742704 prefixEnd_742704 112996781042064415076851 := by
  unfold tailWord_742704
  simp only [CollatzResearch.WordTrace]
  refine ⟨13544320150658863294881583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18059093534211817726508777 13544320150658863294881583)
  ·
    refine ⟨20316480225988294942322375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13544320150658863294881583 20316480225988294942322375)
    ·
      refine ⟨30474720338982442413483563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20316480225988294942322375 30474720338982442413483563)
      ·
        refine ⟨45712080508473663620225345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30474720338982442413483563 45712080508473663620225345)
        ·
          refine ⟨34284060381355247715169009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45712080508473663620225345 34284060381355247715169009)
          ·
            refine ⟨25713045286016435786376757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34284060381355247715169009 25713045286016435786376757)
            ·
              refine ⟨2410597995564040854972821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25713045286016435786376757 2410597995564040854972821)
              ·
                refine ⟨112996781042064415076851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2410597995564040854972821 112996781042064415076851)
                ·
                  rfl

theorem cell20_742704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_742704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742704 prefixEnd_742704 := by exact prefixLift 742704
  have htrace : WordTrace (prefixWord ++ tailWord_742704) baseStart_742704 baseEnd_742704 := by
    simpa [prefixWord, tailWord_742704, baseEnd_742704] using wordTrace_append hprefix tailTrace_742704
  have hstable : (prefixWord ++ tailWord_742704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742704).length < 2 ^ (prefixWord ++ tailWord_742704).sum := by decide
  have hdescent : baseEnd_742704 < baseStart_742704 := by decide
  rcases family_descends (prefixWord ++ tailWord_742704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742717 : List Nat := [1, 4, 1, 5, 2, 1, 6]
def baseStart_742717 : Nat := 118140960795 + 742717 * 2 ^ 59
def prefixEnd_742717 : Nat := 4983230072969 + 3 ^ 40 * 742717 * 2
def baseEnd_742717 : Nat := 37666252964491441977463

theorem tailTrace_742717 : CollatzResearch.WordTrace tailWord_742717 prefixEnd_742717 37666252964491441977463 := by
  unfold tailWord_742717
  simp only [CollatzResearch.WordTrace]
  refine ⟨27089114450270629809986405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18059409633513753206657603 27089114450270629809986405)
  ·
    refine ⟨5079208959425743089372451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27089114450270629809986405 5079208959425743089372451)
    ·
      refine ⟨7618813439138614634058677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5079208959425743089372451 7618813439138614634058677)
      ·
        refine ⟨714263759919245121943001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7618813439138614634058677 714263759919245121943001)
        ·
          refine ⟨535697819939433841457251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 714263759919245121943001 535697819939433841457251)
          ·
            refine ⟨803546729909150762185877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535697819939433841457251 803546729909150762185877)
            ·
              refine ⟨37666252964491441977463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 803546729909150762185877 37666252964491441977463)
              ·
                rfl

theorem cell20_742717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 6].length) (baseStart_742717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742717 prefixEnd_742717 := by exact prefixLift 742717
  have htrace : WordTrace (prefixWord ++ tailWord_742717) baseStart_742717 baseEnd_742717 := by
    simpa [prefixWord, tailWord_742717, baseEnd_742717] using wordTrace_append hprefix tailTrace_742717
  have hstable : (prefixWord ++ tailWord_742717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742717).length < 2 ^ (prefixWord ++ tailWord_742717).sum := by decide
  have hdescent : baseEnd_742717 < baseStart_742717 := by decide
  rcases family_descends (prefixWord ++ tailWord_742717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742721 : List Nat := [1, 2, 5, 2, 1, 1, 8]
def baseStart_742721 : Nat := 118140960795 + 742721 * 2 ^ 59
def prefixEnd_742721 : Nat := 4983230072969 + 3 ^ 40 * 742721 * 2
def baseEnd_742721 : Nat := 37666455821046304629313

theorem tailTrace_742721 : CollatzResearch.WordTrace tailWord_742721 prefixEnd_742721 37666455821046304629313 := by
  unfold tailWord_742721
  simp only [CollatzResearch.WordTrace]
  refine ⟨27089260342256138493132017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18059506894837425662088011 27089260342256138493132017)
  ·
    refine ⟨20316945256692103869849013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27089260342256138493132017 20316945256692103869849013)
    ·
      refine ⟨1904713617814884737798345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20316945256692103869849013 1904713617814884737798345)
      ·
        refine ⟨1428535213361163553348759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1904713617814884737798345 1428535213361163553348759)
        ·
          refine ⟨2142802820041745330023139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428535213361163553348759 2142802820041745330023139)
          ·
            refine ⟨3214204230062617995034709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142802820041745330023139 3214204230062617995034709)
            ·
              refine ⟨37666455821046304629313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3214204230062617995034709 37666455821046304629313)
              ·
                rfl

theorem cell20_742721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 8].length) (baseStart_742721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742721 prefixEnd_742721 := by exact prefixLift 742721
  have htrace : WordTrace (prefixWord ++ tailWord_742721) baseStart_742721 baseEnd_742721 := by
    simpa [prefixWord, tailWord_742721, baseEnd_742721] using wordTrace_append hprefix tailTrace_742721
  have hstable : (prefixWord ++ tailWord_742721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742721).length < 2 ^ (prefixWord ++ tailWord_742721).sum := by decide
  have hdescent : baseEnd_742721 < baseStart_742721 := by decide
  rcases family_descends (prefixWord ++ tailWord_742721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742728 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 3]
def baseStart_742728 : Nat := 118140960795 + 742728 * 2 ^ 59
def prefixEnd_742728 : Nat := 4983230072969 + 3 ^ 40 * 742728 * 2
def baseEnd_742728 : Nat := 339001297380155828430455

theorem tailTrace_742728 : CollatzResearch.WordTrace tailWord_742728 prefixEnd_742728 339001297380155828430455 := by
  unfold tailWord_742728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13544757826615389344318419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18059677102153852459091225 13544757826615389344318419)
  ·
    refine ⟨20317136739923084016477629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13544757826615389344318419 20317136739923084016477629)
    ·
      refine ⟨7618926277471156506179111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20317136739923084016477629 7618926277471156506179111)
      ·
        refine ⟨11428389416206734759268667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7618926277471156506179111 11428389416206734759268667)
        ·
          refine ⟨17142584124310102138903001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11428389416206734759268667 17142584124310102138903001)
          ·
            refine ⟨12856938093232576604177251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17142584124310102138903001 12856938093232576604177251)
            ·
              refine ⟨19285407139848864906265877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12856938093232576604177251 19285407139848864906265877)
              ·
                refine ⟨904003459680415542481213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19285407139848864906265877 904003459680415542481213)
                ·
                  refine ⟨339001297380155828430455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904003459680415542481213 339001297380155828430455)
                  ·
                    rfl

theorem cell20_742728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_742728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742728 prefixEnd_742728 := by exact prefixLift 742728
  have htrace : WordTrace (prefixWord ++ tailWord_742728) baseStart_742728 baseEnd_742728 := by
    simpa [prefixWord, tailWord_742728, baseEnd_742728] using wordTrace_append hprefix tailTrace_742728
  have hstable : (prefixWord ++ tailWord_742728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742728).length < 2 ^ (prefixWord ++ tailWord_742728).sum := by decide
  have hdescent : baseEnd_742728 < baseStart_742728 := by decide
  rcases family_descends (prefixWord ++ tailWord_742728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742745 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 3]
def baseStart_742745 : Nat := 118140960795 + 742745 * 2 ^ 59
def prefixEnd_742745 : Nat := 4983230072969 + 3 ^ 40 * 742745 * 2
def baseEnd_742745 : Nat := 339009056643379324863719

theorem tailTrace_742745 : CollatzResearch.WordTrace tailWord_742745 prefixEnd_742745 339009056643379324863719 := by
  unfold tailWord_742745
  simp only [CollatzResearch.WordTrace]
  refine ⟨27090135694169190592005689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18060090462779460394670459 27090135694169190592005689)
  ·
    refine ⟨20317601770626892944004267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27090135694169190592005689 20317601770626892944004267)
    ·
      refine ⟨30476402655940339416006401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20317601770626892944004267 30476402655940339416006401)
      ·
        refine ⟨22857301991955254562004801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30476402655940339416006401 22857301991955254562004801)
        ·
          refine ⟨17142976493966440921503601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22857301991955254562004801 17142976493966440921503601)
          ·
            refine ⟨12857232370474830691127701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17142976493966440921503601 12857232370474830691127701)
            ·
              refine ⟨602682767366007688646611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12857232370474830691127701 602682767366007688646611)
              ·
                refine ⟨904024151049011532969917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602682767366007688646611 904024151049011532969917)
                ·
                  refine ⟨339009056643379324863719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904024151049011532969917 339009056643379324863719)
                  ·
                    rfl

theorem cell20_742745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_742745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742745 prefixEnd_742745 := by exact prefixLift 742745
  have htrace : WordTrace (prefixWord ++ tailWord_742745) baseStart_742745 baseEnd_742745 := by
    simpa [prefixWord, tailWord_742745, baseEnd_742745] using wordTrace_append hprefix tailTrace_742745
  have hstable : (prefixWord ++ tailWord_742745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742745).length < 2 ^ (prefixWord ++ tailWord_742745).sum := by decide
  have hdescent : baseEnd_742745 < baseStart_742745 := by decide
  rcases family_descends (prefixWord ++ tailWord_742745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742828 : List Nat := [2, 2, 1, 1, 1, 1, 5, 5, 2]
def baseStart_742828 : Nat := 118140960795 + 742828 * 2 ^ 59
def prefixEnd_742828 : Nat := 4983230072969 + 3 ^ 40 * 742828 * 2
def baseEnd_742828 : Nat := 339046940104999925096713

theorem tailTrace_742828 : CollatzResearch.WordTrace tailWord_742828 prefixEnd_742828 339046940104999925096713 := by
  unfold tailWord_742828
  simp only [CollatzResearch.WordTrace]
  refine ⟨13546581476434247883638569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18062108635245663844851425 13546581476434247883638569)
  ·
    refine ⟨10159936107325685912728927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13546581476434247883638569 10159936107325685912728927)
    ·
      refine ⟨15239904160988528869093391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10159936107325685912728927 15239904160988528869093391)
      ·
        refine ⟨22859856241482793303640087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15239904160988528869093391 22859856241482793303640087)
        ·
          refine ⟨34289784362224189955460131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22859856241482793303640087 34289784362224189955460131)
          ·
            refine ⟨51434676543336284933190197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34289784362224189955460131 51434676543336284933190197)
            ·
              refine ⟨4822000925937776712486581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51434676543336284933190197 4822000925937776712486581)
              ·
                refine ⟨452062586806666566795617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4822000925937776712486581 452062586806666566795617)
                ·
                  refine ⟨339046940104999925096713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452062586806666566795617 339046940104999925096713)
                  ·
                    rfl

theorem cell20_742828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_742828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742828 prefixEnd_742828 := by exact prefixLift 742828
  have htrace : WordTrace (prefixWord ++ tailWord_742828) baseStart_742828 baseEnd_742828 := by
    simpa [prefixWord, tailWord_742828, baseEnd_742828] using wordTrace_append hprefix tailTrace_742828
  have hstable : (prefixWord ++ tailWord_742828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742828).length < 2 ^ (prefixWord ++ tailWord_742828).sum := by decide
  have hdescent : baseEnd_742828 < baseStart_742828 := by decide
  rcases family_descends (prefixWord ++ tailWord_742828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742856 : List Nat := [2, 1, 3, 1, 3, 1, 2, 7]
def baseStart_742856 : Nat := 118140960795 + 742856 * 2 ^ 59
def prefixEnd_742856 : Nat := 4983230072969 + 3 ^ 40 * 742856 * 2
def baseEnd_742856 : Nat := 113019906689318757387755

theorem tailTrace_742856 : CollatzResearch.WordTrace tailWord_742856 prefixEnd_742856 113019906689318757387755 := by
  unfold tailWord_742856
  simp only [CollatzResearch.WordTrace]
  refine ⟨13547092098383528274648211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18062789464511371032864281 13547092098383528274648211)
  ·
    refine ⟨20320638147575292411972317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13547092098383528274648211 20320638147575292411972317)
    ·
      refine ⟨7620239305340734654489619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20320638147575292411972317 7620239305340734654489619)
      ·
        refine ⟨11430358958011101981734429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7620239305340734654489619 11430358958011101981734429)
        ·
          refine ⟨4286384609254163243150411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11430358958011101981734429 4286384609254163243150411)
          ·
            refine ⟨6429576913881244864725617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286384609254163243150411 6429576913881244864725617)
            ·
              refine ⟨4822182685410933648544213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6429576913881244864725617 4822182685410933648544213)
              ·
                refine ⟨113019906689318757387755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4822182685410933648544213 113019906689318757387755)
                ·
                  rfl

theorem cell20_742856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_742856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742856 prefixEnd_742856 := by exact prefixLift 742856
  have htrace : WordTrace (prefixWord ++ tailWord_742856) baseStart_742856 baseEnd_742856 := by
    simpa [prefixWord, tailWord_742856, baseEnd_742856] using wordTrace_append hprefix tailTrace_742856
  have hstable : (prefixWord ++ tailWord_742856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742856).length < 2 ^ (prefixWord ++ tailWord_742856).sum := by decide
  have hdescent : baseEnd_742856 < baseStart_742856 := by decide
  rcases family_descends (prefixWord ++ tailWord_742856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742873 : List Nat := [1, 2, 1, 2, 4, 2, 4, 4]
def baseStart_742873 : Nat := 118140960795 + 742873 * 2 ^ 59
def prefixEnd_742873 : Nat := 4983230072969 + 3 ^ 40 * 742873 * 2
def baseEnd_742873 : Nat := 113022493110393256198843

theorem tailTrace_742873 : CollatzResearch.WordTrace tailWord_742873 prefixEnd_742873 113022493110393256198843 := by
  unfold tailWord_742873
  simp only [CollatzResearch.WordTrace]
  refine ⟨27094804237705468452665273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18063202825136978968443515 27094804237705468452665273)
  ·
    refine ⟨20321103178279101339498955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27094804237705468452665273 20321103178279101339498955)
    ·
      refine ⟨30481654767418652009248433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20321103178279101339498955 30481654767418652009248433)
      ·
        refine ⟨22861241075563989006936325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30481654767418652009248433 22861241075563989006936325)
        ·
          refine ⟨4286482701668247938800561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22861241075563989006936325 4286482701668247938800561)
          ·
            refine ⟨3214862026251185954100421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4286482701668247938800561 3214862026251185954100421)
            ·
              refine ⟨602786629922097366393829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3214862026251185954100421 602786629922097366393829)
              ·
                refine ⟨113022493110393256198843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 602786629922097366393829 113022493110393256198843)
                ·
                  rfl

theorem cell20_742873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 4].length) (baseStart_742873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742873 prefixEnd_742873 := by exact prefixLift 742873
  have htrace : WordTrace (prefixWord ++ tailWord_742873) baseStart_742873 baseEnd_742873 := by
    simpa [prefixWord, tailWord_742873, baseEnd_742873] using wordTrace_append hprefix tailTrace_742873
  have hstable : (prefixWord ++ tailWord_742873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742873).length < 2 ^ (prefixWord ++ tailWord_742873).sum := by decide
  have hdescent : baseEnd_742873 < baseStart_742873 := by decide
  rcases family_descends (prefixWord ++ tailWord_742873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742883 : List Nat := [1, 1, 1, 6, 2, 1, 3, 3, 2]
def baseStart_742883 : Nat := 118140960795 + 742883 * 2 ^ 59
def prefixEnd_742883 : Nat := 4983230072969 + 3 ^ 40 * 742883 * 2
def baseEnd_742883 : Nat := 339072043603664178263155

theorem tailTrace_742883 : CollatzResearch.WordTrace tailWord_742883 prefixEnd_742883 339072043603664178263155 := by
  unfold tailWord_742883
  simp only [CollatzResearch.WordTrace]
  refine ⟨27095168967669240160529303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18063445978446160107019535 27095168967669240160529303)
  ·
    refine ⟨40642753451503860240793955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27095168967669240160529303 40642753451503860240793955)
    ·
      refine ⟨60964130177255790361190933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40642753451503860240793955 60964130177255790361190933)
      ·
        refine ⟨2857693602058865173180825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60964130177255790361190933 2857693602058865173180825)
        ·
          refine ⟨2143270201544148879885619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2857693602058865173180825 2143270201544148879885619)
          ·
            refine ⟨3214905302316223319828429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143270201544148879885619 3214905302316223319828429)
            ·
              refine ⟨1205589488368583744935661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3214905302316223319828429 1205589488368583744935661)
              ·
                refine ⟨452096058138218904350873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1205589488368583744935661 452096058138218904350873)
                ·
                  refine ⟨339072043603664178263155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452096058138218904350873 339072043603664178263155)
                  ·
                    rfl

theorem cell20_742883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 2].length) (baseStart_742883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742883 prefixEnd_742883 := by exact prefixLift 742883
  have htrace : WordTrace (prefixWord ++ tailWord_742883) baseStart_742883 baseEnd_742883 := by
    simpa [prefixWord, tailWord_742883, baseEnd_742883] using wordTrace_append hprefix tailTrace_742883
  have hstable : (prefixWord ++ tailWord_742883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742883).length < 2 ^ (prefixWord ++ tailWord_742883).sum := by decide
  have hdescent : baseEnd_742883 < baseStart_742883 := by decide
  rcases family_descends (prefixWord ++ tailWord_742883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742890 : List Nat := [3, 1, 3, 1, 5, 1, 6]
def baseStart_742890 : Nat := 118140960795 + 742890 * 2 ^ 59
def prefixEnd_742890 : Nat := 4983230072969 + 3 ^ 40 * 742890 * 2
def baseEnd_742890 : Nat := 37675026510489251669977

theorem tailTrace_742890 : CollatzResearch.WordTrace tailWord_742890 prefixEnd_742890 37675026510489251669977 := by
  unfold tailWord_742890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6773856069660970089008531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18063616185762586904022749 6773856069660970089008531)
  ·
    refine ⟨10160784104491455133512797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6773856069660970089008531 10160784104491455133512797)
    ·
      refine ⟨3810294039184295675067299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10160784104491455133512797 3810294039184295675067299)
      ·
        refine ⟨5715441058776443512600949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3810294039184295675067299 5715441058776443512600949)
        ·
          refine ⟨535822599260291579306339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5715441058776443512600949 535822599260291579306339)
          ·
            refine ⟨803733898890437368959509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535822599260291579306339 803733898890437368959509)
            ·
              refine ⟨37675026510489251669977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 803733898890437368959509 37675026510489251669977)
              ·
                rfl

theorem cell20_742890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 6].length) (baseStart_742890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742890 prefixEnd_742890 := by exact prefixLift 742890
  have htrace : WordTrace (prefixWord ++ tailWord_742890) baseStart_742890 baseEnd_742890 := by
    simpa [prefixWord, tailWord_742890, baseEnd_742890] using wordTrace_append hprefix tailTrace_742890
  have hstable : (prefixWord ++ tailWord_742890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742890).length < 2 ^ (prefixWord ++ tailWord_742890).sum := by decide
  have hdescent : baseEnd_742890 < baseStart_742890 := by decide
  rcases family_descends (prefixWord ++ tailWord_742890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742904 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 4]
def baseStart_742904 : Nat := 118140960795 + 742904 * 2 ^ 59
def prefixEnd_742904 : Nat := 4983230072969 + 3 ^ 40 * 742904 * 2
def baseEnd_742904 : Nat := 339081628575881438563069

theorem tailTrace_742904 : CollatzResearch.WordTrace tailWord_742904 prefixEnd_742904 339081628575881438563069 := by
  unfold tailWord_742904
  simp only [CollatzResearch.WordTrace]
  refine ⟨13547967450296580373521883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18063956600395440498029177 13547967450296580373521883)
  ·
    refine ⟨20321951175444870560282825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13547967450296580373521883 20321951175444870560282825)
    ·
      refine ⟨15241463381583652920212119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20321951175444870560282825 15241463381583652920212119)
      ·
        refine ⟨22862195072375479380318179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15241463381583652920212119 22862195072375479380318179)
        ·
          refine ⟨34293292608563219070477269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22862195072375479380318179 34293292608563219070477269)
          ·
            refine ⟨803749045513200446964311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 34293292608563219070477269 803749045513200446964311)
            ·
              refine ⟨1205623568269800670446467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803749045513200446964311 1205623568269800670446467)
              ·
                refine ⟨1808435352404701005669701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205623568269800670446467 1808435352404701005669701)
                ·
                  refine ⟨339081628575881438563069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1808435352404701005669701 339081628575881438563069)
                  ·
                    rfl

theorem cell20_742904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_742904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742904 prefixEnd_742904 := by exact prefixLift 742904
  have htrace : WordTrace (prefixWord ++ tailWord_742904) baseStart_742904 baseEnd_742904 := by
    simpa [prefixWord, tailWord_742904, baseEnd_742904] using wordTrace_append hprefix tailTrace_742904
  have hstable : (prefixWord ++ tailWord_742904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742904).length < 2 ^ (prefixWord ++ tailWord_742904).sum := by decide
  have hdescent : baseEnd_742904 < baseStart_742904 := by decide
  rcases family_descends (prefixWord ++ tailWord_742904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742910 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_742910 : Nat := 118140960795 + 742910 * 2 ^ 59
def prefixEnd_742910 : Nat := 4983230072969 + 3 ^ 40 * 742910 * 2
def baseEnd_742910 : Nat := 339084367139372084363045

theorem tailTrace_742910 : CollatzResearch.WordTrace tailWord_742910 prefixEnd_742910 339084367139372084363045 := by
  unfold tailWord_742910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3387019217321427971470273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18064102492380949181174789 3387019217321427971470273)
  ·
    refine ⟨2540264412991070978602705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3387019217321427971470273 2540264412991070978602705)
    ·
      refine ⟨1905198309743303233952029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2540264412991070978602705 1905198309743303233952029)
      ·
        refine ⟨714449366153738712732011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1905198309743303233952029 714449366153738712732011)
        ·
          refine ⟨1071674049230608069098017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714449366153738712732011 1071674049230608069098017)
          ·
            refine ⟨803755536922956051823513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1071674049230608069098017 803755536922956051823513)
            ·
              refine ⟨602816652692217038867635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803755536922956051823513 602816652692217038867635)
              ·
                refine ⟨904224979038325558301453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602816652692217038867635 904224979038325558301453)
                ·
                  refine ⟨339084367139372084363045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904224979038325558301453 339084367139372084363045)
                  ·
                    rfl

theorem cell20_742910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_742910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742910 prefixEnd_742910 := by exact prefixLift 742910
  have htrace : WordTrace (prefixWord ++ tailWord_742910) baseStart_742910 baseEnd_742910 := by
    simpa [prefixWord, tailWord_742910, baseEnd_742910] using wordTrace_append hprefix tailTrace_742910
  have hstable : (prefixWord ++ tailWord_742910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742910).length < 2 ^ (prefixWord ++ tailWord_742910).sum := by decide
  have hdescent : baseEnd_742910 < baseStart_742910 := by decide
  rcases family_descends (prefixWord ++ tailWord_742910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742914 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_742914 : Nat := 118140960795 + 742914 * 2 ^ 59
def prefixEnd_742914 : Nat := 4983230072969 + 3 ^ 40 * 742914 * 2
def baseEnd_742914 : Nat := 339086192848365848229695

theorem tailTrace_742914 : CollatzResearch.WordTrace tailWord_742914 prefixEnd_742914 339086192848365848229695 := by
  unfold tailWord_742914
  simp only [CollatzResearch.WordTrace]
  refine ⟨6774074907639233113726949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18064199753704621636605197 6774074907639233113726949)
  ·
    refine ⟨1270139045182356208823803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6774074907639233113726949 1270139045182356208823803)
    ·
      refine ⟨1905208567773534313235705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270139045182356208823803 1905208567773534313235705)
      ·
        refine ⟨1428906425830150734926779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1905208567773534313235705 1428906425830150734926779)
        ·
          refine ⟨2143359638745226102390169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428906425830150734926779 2143359638745226102390169)
          ·
            refine ⟨1607519729058919576792627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2143359638745226102390169 1607519729058919576792627)
            ·
              refine ⟨2411279593588379365188941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607519729058919576792627 2411279593588379365188941)
              ·
                refine ⟨904229847595642261945853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2411279593588379365188941 904229847595642261945853)
                ·
                  refine ⟨339086192848365848229695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904229847595642261945853 339086192848365848229695)
                  ·
                    rfl

theorem cell20_742914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_742914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742914 prefixEnd_742914 := by exact prefixLift 742914
  have htrace : WordTrace (prefixWord ++ tailWord_742914) baseStart_742914 baseEnd_742914 := by
    simpa [prefixWord, tailWord_742914, baseEnd_742914] using wordTrace_append hprefix tailTrace_742914
  have hstable : (prefixWord ++ tailWord_742914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742914).length < 2 ^ (prefixWord ++ tailWord_742914).sum := by decide
  have hdescent : baseEnd_742914 < baseStart_742914 := by decide
  rcases family_descends (prefixWord ++ tailWord_742914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742952 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 3]
def baseStart_742952 : Nat := 118140960795 + 742952 * 2 ^ 59
def prefixEnd_742952 : Nat := 4983230072969 + 3 ^ 40 * 742952 * 2
def baseEnd_742952 : Nat := 339103537083806604962873

theorem tailTrace_742952 : CollatzResearch.WordTrace tailWord_742952 prefixEnd_742952 339103537083806604962873 := by
  unfold tailWord_742952
  simp only [CollatzResearch.WordTrace]
  refine ⟨13548842802209632472395555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18065123736279509963194073 13548842802209632472395555)
  ·
    refine ⟨20323264203314448708593333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13548842802209632472395555 20323264203314448708593333)
    ·
      refine ⟨1905306019060729566430625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20323264203314448708593333 1905306019060729566430625)
      ·
        refine ⟨1428979514295547174822969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1905306019060729566430625 1428979514295547174822969)
        ·
          refine ⟨1071734635721660381117227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1428979514295547174822969 1071734635721660381117227)
          ·
            refine ⟨1607601953582490571675841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071734635721660381117227 1607601953582490571675841)
            ·
              refine ⟨1205701465186867928756881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1607601953582490571675841 1205701465186867928756881)
              ·
                refine ⟨904276098890150946567661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205701465186867928756881 904276098890150946567661)
                ·
                  refine ⟨339103537083806604962873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904276098890150946567661 339103537083806604962873)
                  ·
                    rfl

theorem cell20_742952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_742952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_742952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_742952 prefixEnd_742952 := by exact prefixLift 742952
  have htrace : WordTrace (prefixWord ++ tailWord_742952) baseStart_742952 baseEnd_742952 := by
    simpa [prefixWord, tailWord_742952, baseEnd_742952] using wordTrace_append hprefix tailTrace_742952
  have hstable : (prefixWord ++ tailWord_742952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742952).length < 2 ^ (prefixWord ++ tailWord_742952).sum := by decide
  have hdescent : baseEnd_742952 < baseStart_742952 := by decide
  rcases family_descends (prefixWord ++ tailWord_742952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743011 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 3]
def baseStart_743011 : Nat := 118140960795 + 743011 * 2 ^ 59
def prefixEnd_743011 : Nat := 4983230072969 + 3 ^ 40 * 743011 * 2
def baseEnd_743011 : Nat := 339130466291464621995965

theorem tailTrace_743011 : CollatzResearch.WordTrace tailWord_743011 prefixEnd_743011 339130466291464621995965 := by
  unfold tailWord_743011
  simp only [CollatzResearch.WordTrace]
  refine ⟨27099837511205518021188887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18066558340803678680792591 27099837511205518021188887)
  ·
    refine ⟨40649756266808277031783331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27099837511205518021188887 40649756266808277031783331)
    ·
      refine ⟨60974634400212415547674997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40649756266808277031783331 60974634400212415547674997)
      ·
        refine ⟨5716371975019913957594531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60974634400212415547674997 5716371975019913957594531)
        ·
          refine ⟨8574557962529870936391797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5716371975019913957594531 8574557962529870936391797)
          ·
            refine ⟨803864808987175400286731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8574557962529870936391797 803864808987175400286731)
            ·
              refine ⟨1205797213480763100430097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803864808987175400286731 1205797213480763100430097)
              ·
                refine ⟨904347910110572325322573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205797213480763100430097 904347910110572325322573)
                ·
                  refine ⟨339130466291464621995965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904347910110572325322573 339130466291464621995965)
                  ·
                    rfl

theorem cell20_743011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 3].length) (baseStart_743011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743011 prefixEnd_743011 := by exact prefixLift 743011
  have htrace : WordTrace (prefixWord ++ tailWord_743011) baseStart_743011 baseEnd_743011 := by
    simpa [prefixWord, tailWord_743011, baseEnd_743011] using wordTrace_append hprefix tailTrace_743011
  have hstable : (prefixWord ++ tailWord_743011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743011).length < 2 ^ (prefixWord ++ tailWord_743011).sum := by decide
  have hdescent : baseEnd_743011 < baseStart_743011 := by decide
  rcases family_descends (prefixWord ++ tailWord_743011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743018 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_743018 : Nat := 118140960795 + 743018 * 2 ^ 59
def prefixEnd_743018 : Nat := 4983230072969 + 3 ^ 40 * 743018 * 2
def baseEnd_743018 : Nat := 339133661282203708762603

theorem tailTrace_743018 : CollatzResearch.WordTrace tailWord_743018 prefixEnd_743018 339133661282203708762603 := by
  unfold tailWord_743018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6775023205545039554173427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18066728548120105477795805 6775023205545039554173427)
  ·
    refine ⟨10162534808317559331260141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6775023205545039554173427 10162534808317559331260141)
    ·
      refine ⟨3810950553119084749222553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10162534808317559331260141 3810950553119084749222553)
      ·
        refine ⟨2858212914839313561916915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3810950553119084749222553 2858212914839313561916915)
        ·
          refine ⟨4287319372258970342875373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2858212914839313561916915 4287319372258970342875373)
          ·
            refine ⟨1607744764597113878578265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4287319372258970342875373 1607744764597113878578265)
            ·
              refine ⟨1205808573447835408933699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1607744764597113878578265 1205808573447835408933699)
              ·
                refine ⟨1808712860171753113400549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205808573447835408933699 1808712860171753113400549)
                ·
                  refine ⟨339133661282203708762603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1808712860171753113400549 339133661282203708762603)
                  ·
                    rfl

theorem cell20_743018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_743018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743018 prefixEnd_743018 := by exact prefixLift 743018
  have htrace : WordTrace (prefixWord ++ tailWord_743018) baseStart_743018 baseEnd_743018 := by
    simpa [prefixWord, tailWord_743018, baseEnd_743018] using wordTrace_append hprefix tailTrace_743018
  have hstable : (prefixWord ++ tailWord_743018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743018).length < 2 ^ (prefixWord ++ tailWord_743018).sum := by decide
  have hdescent : baseEnd_743018 < baseStart_743018 := by decide
  rcases family_descends (prefixWord ++ tailWord_743018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743077 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 4]
def baseStart_743077 : Nat := 118140960795 + 743077 * 2 ^ 59
def prefixEnd_743077 : Nat := 4983230072969 + 3 ^ 40 * 743077 * 2
def baseEnd_743077 : Nat := 339160590489861725795695

theorem tailTrace_743077 : CollatzResearch.WordTrace tailWord_743077 prefixEnd_743077 339160590489861725795695 := by
  unfold tailWord_743077
  simp only [CollatzResearch.WordTrace]
  refine ⟨27102244728966411293091485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18068163152644274195394323 27102244728966411293091485)
  ·
    refine ⟨10163341773362404234909307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27102244728966411293091485 10163341773362404234909307)
    ·
      refine ⟨15245012660043606352363961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10163341773362404234909307 15245012660043606352363961)
      ·
        refine ⟨11433759495032704764272971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15245012660043606352363961 11433759495032704764272971)
        ·
          refine ⟨17150639242549057146409457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11433759495032704764272971 17150639242549057146409457)
          ·
            refine ⟨12862979431911792859807093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17150639242549057146409457 12862979431911792859807093)
            ·
              refine ⟨1205904321741730580606915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12862979431911792859807093 1205904321741730580606915)
              ·
                refine ⟨1808856482612595870910373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205904321741730580606915 1808856482612595870910373)
                ·
                  refine ⟨339160590489861725795695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1808856482612595870910373 339160590489861725795695)
                  ·
                    rfl

theorem cell20_743077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_743077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743077 prefixEnd_743077 := by exact prefixLift 743077
  have htrace : WordTrace (prefixWord ++ tailWord_743077) baseStart_743077 baseEnd_743077 := by
    simpa [prefixWord, tailWord_743077, baseEnd_743077] using wordTrace_append hprefix tailTrace_743077
  have hstable : (prefixWord ++ tailWord_743077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743077).length < 2 ^ (prefixWord ++ tailWord_743077).sum := by decide
  have hdescent : baseEnd_743077 < baseStart_743077 := by decide
  rcases family_descends (prefixWord ++ tailWord_743077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743122 : List Nat := [3, 2, 2, 2, 2, 9]
def baseStart_743122 : Nat := 118140960795 + 743122 * 2 ^ 59
def prefixEnd_743122 : Nat := 4983230072969 + 3 ^ 40 * 743122 * 2
def baseEnd_743122 : Nat := 12562264063557095159093

theorem tailTrace_743122 : CollatzResearch.WordTrace tailWord_743122 prefixEnd_743122 12562264063557095159093 := by
  unfold tailWord_743122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6775971503450845994619905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18069257342535589318986413 6775971503450845994619905)
  ·
    refine ⟨5081978627588134495964929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6775971503450845994619905 5081978627588134495964929)
    ·
      refine ⟨3811483970691100871973697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5081978627588134495964929 3811483970691100871973697)
      ·
        refine ⟨2858612978018325653980273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3811483970691100871973697 2858612978018325653980273)
        ·
          refine ⟨2143959733513744240485205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2858612978018325653980273 2143959733513744240485205)
          ·
            refine ⟨12562264063557095159093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2143959733513744240485205 12562264063557095159093)
            ·
              rfl

theorem cell20_743122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 9].length) (baseStart_743122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743122 prefixEnd_743122 := by exact prefixLift 743122
  have htrace : WordTrace (prefixWord ++ tailWord_743122) baseStart_743122 baseEnd_743122 := by
    simpa [prefixWord, tailWord_743122, baseEnd_743122] using wordTrace_append hprefix tailTrace_743122
  have hstable : (prefixWord ++ tailWord_743122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743122).length < 2 ^ (prefixWord ++ tailWord_743122).sum := by decide
  have hdescent : baseEnd_743122 < baseStart_743122 := by decide
  rcases family_descends (prefixWord ++ tailWord_743122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743146 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_743146 : Nat := 118140960795 + 743146 * 2 ^ 59
def prefixEnd_743146 : Nat := 4983230072969 + 3 ^ 40 * 743146 * 2
def baseEnd_743146 : Nat := 339192083970004152495413

theorem tailTrace_743146 : CollatzResearch.WordTrace tailWord_743146 prefixEnd_743146 339192083970004152495413 := by
  unfold tailWord_743146
  simp only [CollatzResearch.WordTrace]
  refine ⟨6776190341429109019338323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18069840910477624051568861 6776190341429109019338323)
  ·
    refine ⟨10164285512143663529007485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6776190341429109019338323 10164285512143663529007485)
    ·
      refine ⟨3811607067053873823377807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10164285512143663529007485 3811607067053873823377807)
      ·
        refine ⟨5717410600580810735066711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3811607067053873823377807 5717410600580810735066711)
        ·
          refine ⟨8576115900871216102600067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5717410600580810735066711 8576115900871216102600067)
          ·
            refine ⟨12864173851306824153900101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8576115900871216102600067 12864173851306824153900101)
            ·
              refine ⟨2412032597120029528856269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12864173851306824153900101 2412032597120029528856269)
              ·
                refine ⟨904512223920011073321101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2412032597120029528856269 904512223920011073321101)
                ·
                  refine ⟨339192083970004152495413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904512223920011073321101 339192083970004152495413)
                  ·
                    rfl

theorem cell20_743146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_743146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743146 prefixEnd_743146 := by exact prefixLift 743146
  have htrace : WordTrace (prefixWord ++ tailWord_743146) baseStart_743146 baseEnd_743146 := by
    simpa [prefixWord, tailWord_743146, baseEnd_743146] using wordTrace_append hprefix tailTrace_743146
  have hstable : (prefixWord ++ tailWord_743146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743146).length < 2 ^ (prefixWord ++ tailWord_743146).sum := by decide
  have hdescent : baseEnd_743146 < baseStart_743146 := by decide
  rcases family_descends (prefixWord ++ tailWord_743146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743153 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 4]
def baseStart_743153 : Nat := 118140960795 + 743153 * 2 ^ 59
def prefixEnd_743153 : Nat := 4983230072969 + 3 ^ 40 * 743153 * 2
def baseEnd_743153 : Nat := 339195278960743239262051

theorem tailTrace_743153 : CollatzResearch.WordTrace tailWord_743153 prefixEnd_743153 339195278960743239262051 := by
  unfold tailWord_743153
  simp only [CollatzResearch.WordTrace]
  refine ⟨27105016676691076272858113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18070011117794050848572075 27105016676691076272858113)
  ·
    refine ⟨20328762507518307204643585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27105016676691076272858113 20328762507518307204643585)
    ·
      refine ⟨15246571880638730403482689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20328762507518307204643585 15246571880638730403482689)
      ·
        refine ⟨11434928910479047802612017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15246571880638730403482689 11434928910479047802612017)
        ·
          refine ⟨8576196682859285851959013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11434928910479047802612017 8576196682859285851959013)
          ·
            refine ⟨1608036878036116097242315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8576196682859285851959013 1608036878036116097242315)
            ·
              refine ⟨2412055317054174145863473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1608036878036116097242315 2412055317054174145863473)
              ·
                refine ⟨1809041487790630609397605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412055317054174145863473 1809041487790630609397605)
                ·
                  refine ⟨339195278960743239262051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809041487790630609397605 339195278960743239262051)
                  ·
                    rfl

theorem cell20_743153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_743153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743153 prefixEnd_743153 := by exact prefixLift 743153
  have htrace : WordTrace (prefixWord ++ tailWord_743153) baseStart_743153 baseEnd_743153 := by
    simpa [prefixWord, tailWord_743153, baseEnd_743153] using wordTrace_append hprefix tailTrace_743153
  have hstable : (prefixWord ++ tailWord_743153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743153).length < 2 ^ (prefixWord ++ tailWord_743153).sum := by decide
  have hdescent : baseEnd_743153 < baseStart_743153 := by decide
  rcases family_descends (prefixWord ++ tailWord_743153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743166 : List Nat := [4, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_743166 : Nat := 118140960795 + 743166 * 2 ^ 59
def prefixEnd_743166 : Nat := 4983230072969 + 3 ^ 40 * 743166 * 2
def baseEnd_743166 : Nat := 339201212514972971828665

theorem tailTrace_743166 : CollatzResearch.WordTrace tailWord_743166 prefixEnd_743166 339201212514972971828665 := by
  unfold tailWord_743166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3388186353205497436635169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18070327217095986328720901 3388186353205497436635169)
  ·
    refine ⟨2541139764904123077476377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3388186353205497436635169 2541139764904123077476377)
    ·
      refine ⟨1905854823678092308107283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2541139764904123077476377 1905854823678092308107283)
      ·
        refine ⟨2858782235517138462160925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905854823678092308107283 2858782235517138462160925)
        ·
          refine ⟨1072043338318926923310347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2858782235517138462160925 1072043338318926923310347)
          ·
            refine ⟨1608065007478390384965521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072043338318926923310347 1608065007478390384965521)
            ·
              refine ⟨1206048755608792788724141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608065007478390384965521 1206048755608792788724141)
              ·
                refine ⟨452268283353297295771553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1206048755608792788724141 452268283353297295771553)
                ·
                  refine ⟨339201212514972971828665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452268283353297295771553 339201212514972971828665)
                  ·
                    rfl

theorem cell20_743166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_743166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743166 prefixEnd_743166 := by exact prefixLift 743166
  have htrace : WordTrace (prefixWord ++ tailWord_743166) baseStart_743166 baseEnd_743166 := by
    simpa [prefixWord, tailWord_743166, baseEnd_743166] using wordTrace_append hprefix tailTrace_743166
  have hstable : (prefixWord ++ tailWord_743166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743166).length < 2 ^ (prefixWord ++ tailWord_743166).sum := by decide
  have hdescent : baseEnd_743166 < baseStart_743166 := by decide
  rcases family_descends (prefixWord ++ tailWord_743166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743191 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 4]
def baseStart_743191 : Nat := 118140960795 + 743191 * 2 ^ 59
def prefixEnd_743191 : Nat := 4983230072969 + 3 ^ 40 * 743191 * 2
def baseEnd_743191 : Nat := 339212623196183995995229

theorem tailTrace_743191 : CollatzResearch.WordTrace tailWord_743191 prefixEnd_743191 339212623196183995995229 := by
  unfold tailWord_743191
  simp only [CollatzResearch.WordTrace]
  refine ⟨27106402650553408762741427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18070935100368939175160951 27106402650553408762741427)
  ·
    refine ⟨40659603975830113144112141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27106402650553408762741427 40659603975830113144112141)
    ·
      refine ⟨15247351490936292429042053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40659603975830113144112141 15247351490936292429042053)
      ·
        refine ⟨2858878404550554830445385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15247351490936292429042053 2858878404550554830445385)
        ·
          refine ⟨2144158803412916122834039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2858878404550554830445385 2144158803412916122834039)
          ·
            refine ⟨3216238205119374184251059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144158803412916122834039 3216238205119374184251059)
            ·
              refine ⟨4824357307679061276376589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216238205119374184251059 4824357307679061276376589)
              ·
                refine ⟨1809133990379647978641221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4824357307679061276376589 1809133990379647978641221)
                ·
                  refine ⟨339212623196183995995229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809133990379647978641221 339212623196183995995229)
                  ·
                    rfl

theorem cell20_743191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_743191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743191 prefixEnd_743191 := by exact prefixLift 743191
  have htrace : WordTrace (prefixWord ++ tailWord_743191) baseStart_743191 baseEnd_743191 := by
    simpa [prefixWord, tailWord_743191, baseEnd_743191] using wordTrace_append hprefix tailTrace_743191
  have hstable : (prefixWord ++ tailWord_743191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743191).length < 2 ^ (prefixWord ++ tailWord_743191).sum := by decide
  have hdescent : baseEnd_743191 < baseStart_743191 := by decide
  rcases family_descends (prefixWord ++ tailWord_743191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743201 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 3]
def baseStart_743201 : Nat := 118140960795 + 743201 * 2 ^ 59
def prefixEnd_743201 : Nat := 4983230072969 + 3 ^ 40 * 743201 * 2
def baseEnd_743201 : Nat := 339217187468668405661855

theorem tailTrace_743201 : CollatzResearch.WordTrace tailWord_743201 prefixEnd_743201 339217187468668405661855 := by
  unfold tailWord_743201
  simp only [CollatzResearch.WordTrace]
  refine ⟨27106767380517180470605457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18071178253678120313736971 27106767380517180470605457)
  ·
    refine ⟨20330075535387885352954093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27106767380517180470605457 20330075535387885352954093)
    ·
      refine ⟨7623778325770457007357785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20330075535387885352954093 7623778325770457007357785)
      ·
        refine ⟨5717833744327842755518339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7623778325770457007357785 5717833744327842755518339)
        ·
          refine ⟨8576750616491764133277509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5717833744327842755518339 8576750616491764133277509)
          ·
            refine ⟨1608140740592205774989533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8576750616491764133277509 1608140740592205774989533)
            ·
              refine ⟨603052777722077165621075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1608140740592205774989533 603052777722077165621075)
              ·
                refine ⟨904579166583115748431613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603052777722077165621075 904579166583115748431613)
                ·
                  refine ⟨339217187468668405661855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904579166583115748431613 339217187468668405661855)
                  ·
                    rfl

theorem cell20_743201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_743201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743201 prefixEnd_743201 := by exact prefixLift 743201
  have htrace : WordTrace (prefixWord ++ tailWord_743201) baseStart_743201 baseEnd_743201 := by
    simpa [prefixWord, tailWord_743201, baseEnd_743201] using wordTrace_append hprefix tailTrace_743201
  have hstable : (prefixWord ++ tailWord_743201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743201).length < 2 ^ (prefixWord ++ tailWord_743201).sum := by decide
  have hdescent : baseEnd_743201 < baseStart_743201 := by decide
  rcases family_descends (prefixWord ++ tailWord_743201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743294 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_743294 : Nat := 118140960795 + 743294 * 2 ^ 59
def prefixEnd_743294 : Nat := 4983230072969 + 3 ^ 40 * 743294 * 2
def baseEnd_743294 : Nat := 339259635202773415561475

theorem tailTrace_743294 : CollatzResearch.WordTrace tailWord_743294 prefixEnd_743294 339259635202773415561475 := by
  unfold tailWord_743294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3388769921147532169217617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18073439579453504902493957 3388769921147532169217617)
  ·
    refine ⟨2541577440860649126913213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3388769921147532169217617 2541577440860649126913213)
    ·
      refine ⟨953091540322743422592455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2541577440860649126913213 953091540322743422592455)
      ·
        refine ⟨1429637310484115133888683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953091540322743422592455 1429637310484115133888683)
        ·
          refine ⟨2144455965726172700833025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429637310484115133888683 2144455965726172700833025)
          ·
            refine ⟨1608341974294629525624769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2144455965726172700833025 1608341974294629525624769)
            ·
              refine ⟨1206256480720972144218577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608341974294629525624769 1206256480720972144218577)
              ·
                refine ⟨904692360540729108163933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206256480720972144218577 904692360540729108163933)
                ·
                  refine ⟨339259635202773415561475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904692360540729108163933 339259635202773415561475)
                  ·
                    rfl

theorem cell20_743294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_743294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743294 prefixEnd_743294 := by exact prefixLift 743294
  have htrace : WordTrace (prefixWord ++ tailWord_743294) baseStart_743294 baseEnd_743294 := by
    simpa [prefixWord, tailWord_743294, baseEnd_743294] using wordTrace_append hprefix tailTrace_743294
  have hstable : (prefixWord ++ tailWord_743294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743294).length < 2 ^ (prefixWord ++ tailWord_743294).sum := by decide
  have hdescent : baseEnd_743294 < baseStart_743294 := by decide
  rcases family_descends (prefixWord ++ tailWord_743294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743297 : List Nat := [1, 2, 4, 4, 1, 2, 2, 2, 2]
def baseStart_743297 : Nat := 118140960795 + 743297 * 2 ^ 59
def prefixEnd_743297 : Nat := 4983230072969 + 3 ^ 40 * 743297 * 2
def baseEnd_743297 : Nat := 339261004484518738461463

theorem tailTrace_743297 : CollatzResearch.WordTrace tailWord_743297 prefixEnd_743297 339261004484518738461463 := by
  unfold tailWord_743297
  simp only [CollatzResearch.WordTrace]
  refine ⟨27110268788169388866100145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18073512525446259244066763 27110268788169388866100145)
  ·
    refine ⟨20332701591127041649575109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27110268788169388866100145 20332701591127041649575109)
    ·
      refine ⟨3812381548336320309295333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20332701591127041649575109 3812381548336320309295333)
      ·
        refine ⟨714821540313060057992875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3812381548336320309295333 714821540313060057992875)
        ·
          refine ⟨1072232310469590086989313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714821540313060057992875 1072232310469590086989313)
          ·
            refine ⟨804174232852192565241985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072232310469590086989313 804174232852192565241985)
            ·
              refine ⟨603130674639144423931489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804174232852192565241985 603130674639144423931489)
              ·
                refine ⟨452348005979358317948617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603130674639144423931489 452348005979358317948617)
                ·
                  refine ⟨339261004484518738461463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452348005979358317948617 339261004484518738461463)
                  ·
                    rfl

theorem cell20_743297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 2].length) (baseStart_743297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743297 prefixEnd_743297 := by exact prefixLift 743297
  have htrace : WordTrace (prefixWord ++ tailWord_743297) baseStart_743297 baseEnd_743297 := by
    simpa [prefixWord, tailWord_743297, baseEnd_743297] using wordTrace_append hprefix tailTrace_743297
  have hstable : (prefixWord ++ tailWord_743297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743297).length < 2 ^ (prefixWord ++ tailWord_743297).sum := by decide
  have hdescent : baseEnd_743297 < baseStart_743297 := by decide
  rcases family_descends (prefixWord ++ tailWord_743297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743318 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_743318 : Nat := 118140960795 + 743318 * 2 ^ 59
def prefixEnd_743318 : Nat := 4983230072969 + 3 ^ 40 * 743318 * 2
def baseEnd_743318 : Nat := 339270589456735998761377

theorem tailTrace_743318 : CollatzResearch.WordTrace tailWord_743318 prefixEnd_743318 339270589456735998761377 := by
  unfold tailWord_743318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694439670068331840788413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18074023147395539635076405 1694439670068331840788413)
  ·
    refine ⟨635414876275624440295655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1694439670068331840788413 635414876275624440295655)
    ·
      refine ⟨953122314413436660443483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635414876275624440295655 953122314413436660443483)
      ·
        refine ⟨1429683471620154990665225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953122314413436660443483 1429683471620154990665225)
        ·
          refine ⟨1072262603715116242998919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1429683471620154990665225 1072262603715116242998919)
          ·
            refine ⟨1608393905572674364498379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072262603715116242998919 1608393905572674364498379)
            ·
              refine ⟨2412590858359011546747569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1608393905572674364498379 2412590858359011546747569)
              ·
                refine ⟨1809443143769258660060677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412590858359011546747569 1809443143769258660060677)
                ·
                  refine ⟨339270589456735998761377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809443143769258660060677 339270589456735998761377)
                  ·
                    rfl

theorem cell20_743318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_743318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743318 prefixEnd_743318 := by exact prefixLift 743318
  have htrace : WordTrace (prefixWord ++ tailWord_743318) baseStart_743318 baseEnd_743318 := by
    simpa [prefixWord, tailWord_743318, baseEnd_743318] using wordTrace_append hprefix tailTrace_743318
  have hstable : (prefixWord ++ tailWord_743318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743318).length < 2 ^ (prefixWord ++ tailWord_743318).sum := by decide
  have hdescent : baseEnd_743318 < baseStart_743318 := by decide
  rcases family_descends (prefixWord ++ tailWord_743318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743333 : List Nat := [1, 3, 1, 2, 1, 1, 1, 10]
def baseStart_743333 : Nat := 118140960795 + 743333 * 2 ^ 59
def prefixEnd_743333 : Nat := 4983230072969 + 3 ^ 40 * 743333 * 2
def baseEnd_743333 : Nat := 113092478621820871087105

theorem tailTrace_743333 : CollatzResearch.WordTrace tailWord_743333 prefixEnd_743333 113092478621820871087105 := by
  unfold tailWord_743333
  simp only [CollatzResearch.WordTrace]
  refine ⟨27111581816038967014410653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18074387877359311342940435 27111581816038967014410653)
  ·
    refine ⟨10166843181014612630403995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27111581816038967014410653 10166843181014612630403995)
    ·
      refine ⟨15250264771521918945605993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10166843181014612630403995 15250264771521918945605993)
      ·
        refine ⟨11437698578641439209204495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15250264771521918945605993 11437698578641439209204495)
        ·
          refine ⟨17156547867962158813806743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11437698578641439209204495 17156547867962158813806743)
          ·
            refine ⟨25734821801943238220710115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17156547867962158813806743 25734821801943238220710115)
            ·
              refine ⟨38602232702914857331065173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25734821801943238220710115 38602232702914857331065173)
              ·
                refine ⟨113092478621820871087105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38602232702914857331065173 113092478621820871087105)
                ·
                  rfl

theorem cell20_743333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_743333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743333 prefixEnd_743333 := by exact prefixLift 743333
  have htrace : WordTrace (prefixWord ++ tailWord_743333) baseStart_743333 baseEnd_743333 := by
    simpa [prefixWord, tailWord_743333, baseEnd_743333] using wordTrace_append hprefix tailTrace_743333
  have hstable : (prefixWord ++ tailWord_743333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743333).length < 2 ^ (prefixWord ++ tailWord_743333).sum := by decide
  have hdescent : baseEnd_743333 < baseStart_743333 := by decide
  rcases family_descends (prefixWord ++ tailWord_743333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743371 : List Nat := [1, 1, 1, 1, 3, 4, 2, 7]
def baseStart_743371 : Nat := 118140960795 + 743371 * 2 ^ 59
def prefixEnd_743371 : Nat := 4983230072969 + 3 ^ 40 * 743371 * 2
def baseEnd_743371 : Nat := 113098260033634456664831

theorem tailTrace_743371 : CollatzResearch.WordTrace tailWord_743371 prefixEnd_743371 113098260033634456664831 := by
  unfold tailWord_743371
  simp only [CollatzResearch.WordTrace]
  refine ⟨27112967789901299504293967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18075311859934199669529311 27112967789901299504293967)
  ·
    refine ⟨40669451684851949256440951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27112967789901299504293967 40669451684851949256440951)
    ·
      refine ⟨61004177527277923884661427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40669451684851949256440951 61004177527277923884661427)
      ·
        refine ⟨91506266290916885826992141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61004177527277923884661427 91506266290916885826992141)
        ·
          refine ⟨34314849859093832185122053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91506266290916885826992141 34314849859093832185122053)
          ·
            refine ⟨6434034348580093534710385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34314849859093832185122053 6434034348580093534710385)
            ·
              refine ⟨4825525761435070151032789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6434034348580093534710385 4825525761435070151032789)
              ·
                refine ⟨113098260033634456664831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4825525761435070151032789 113098260033634456664831)
                ·
                  rfl

theorem cell20_743371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_743371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743371 prefixEnd_743371 := by exact prefixLift 743371
  have htrace : WordTrace (prefixWord ++ tailWord_743371) baseStart_743371 baseEnd_743371 := by
    simpa [prefixWord, tailWord_743371, baseEnd_743371] using wordTrace_append hprefix tailTrace_743371
  have hstable : (prefixWord ++ tailWord_743371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743371).length < 2 ^ (prefixWord ++ tailWord_743371).sum := by decide
  have hdescent : baseEnd_743371 < baseStart_743371 := by decide
  rcases family_descends (prefixWord ++ tailWord_743371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743381 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 4]
def baseStart_743381 : Nat := 118140960795 + 743381 * 2 ^ 59
def prefixEnd_743381 : Nat := 4983230072969 + 3 ^ 40 * 743381 * 2
def baseEnd_743381 : Nat := 339299344373387779661119

theorem tailTrace_743381 : CollatzResearch.WordTrace tailWord_743381 prefixEnd_743381 339299344373387779661119 := by
  unfold tailWord_743381
  simp only [CollatzResearch.WordTrace]
  refine ⟨27113332519865071212157997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18075555013243380808105331 27113332519865071212157997)
  ·
    refine ⟨10167499694949401704559249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27113332519865071212157997 10167499694949401704559249)
    ·
      refine ⟨7625624771212051278419437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10167499694949401704559249 7625624771212051278419437)
      ·
        refine ⟨2859609289204519229407289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7625624771212051278419437 2859609289204519229407289)
        ·
          refine ⟨2144706966903389422055467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2859609289204519229407289 2144706966903389422055467)
          ·
            refine ⟨3217060450355084133083201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144706966903389422055467 3217060450355084133083201)
            ·
              refine ⟨2412795337766313099812401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3217060450355084133083201 2412795337766313099812401)
              ·
                refine ⟨1809596503324734824859301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412795337766313099812401 1809596503324734824859301)
                ·
                  refine ⟨339299344373387779661119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809596503324734824859301 339299344373387779661119)
                  ·
                    rfl

theorem cell20_743381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_743381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743381 prefixEnd_743381 := by exact prefixLift 743381
  have htrace : WordTrace (prefixWord ++ tailWord_743381) baseStart_743381 baseEnd_743381 := by
    simpa [prefixWord, tailWord_743381, baseEnd_743381] using wordTrace_append hprefix tailTrace_743381
  have hstable : (prefixWord ++ tailWord_743381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743381).length < 2 ^ (prefixWord ++ tailWord_743381).sum := by decide
  have hdescent : baseEnd_743381 < baseStart_743381 := by decide
  rcases family_descends (prefixWord ++ tailWord_743381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743395 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 5]
def baseStart_743395 : Nat := 118140960795 + 743395 * 2 ^ 59
def prefixEnd_743395 : Nat := 4983230072969 + 3 ^ 40 * 743395 * 2
def baseEnd_743395 : Nat := 339305734354865953194395

theorem tailTrace_743395 : CollatzResearch.WordTrace tailWord_743395 prefixEnd_743395 339305734354865953194395 := by
  unfold tailWord_743395
  simp only [CollatzResearch.WordTrace]
  refine ⟨27113843141814351603167639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18075895427876234402111759 27113843141814351603167639)
  ·
    refine ⟨40670764712721527404751459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27113843141814351603167639 40670764712721527404751459)
    ·
      refine ⟨61006147069082291107127189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40670764712721527404751459 61006147069082291107127189)
      ·
        refine ⟨2859663143863232395646587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61006147069082291107127189 2859663143863232395646587)
        ·
          refine ⟨4289494715794848593469881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2859663143863232395646587 4289494715794848593469881)
          ·
            refine ⟨3217121036846136445102411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4289494715794848593469881 3217121036846136445102411)
            ·
              refine ⟨4825681555269204667653617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217121036846136445102411 4825681555269204667653617)
              ·
                refine ⟨3619261166451903500740213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4825681555269204667653617 3619261166451903500740213)
                ·
                  refine ⟨339305734354865953194395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3619261166451903500740213 339305734354865953194395)
                  ·
                    rfl

theorem cell20_743395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_743395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743395 prefixEnd_743395 := by exact prefixLift 743395
  have htrace : WordTrace (prefixWord ++ tailWord_743395) baseStart_743395 baseEnd_743395 := by
    simpa [prefixWord, tailWord_743395, baseEnd_743395] using wordTrace_append hprefix tailTrace_743395
  have hstable : (prefixWord ++ tailWord_743395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743395).length < 2 ^ (prefixWord ++ tailWord_743395).sum := by decide
  have hdescent : baseEnd_743395 < baseStart_743395 := by decide
  rcases family_descends (prefixWord ++ tailWord_743395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743419 : List Nat := [1, 1, 1, 1, 1, 3, 4, 6, 2]
def baseStart_743419 : Nat := 118140960795 + 743419 * 2 ^ 59
def prefixEnd_743419 : Nat := 4983230072969 + 3 ^ 40 * 743419 * 2
def baseEnd_743419 : Nat := 339316688608828536394297

theorem tailTrace_743419 : CollatzResearch.WordTrace tailWord_743419 prefixEnd_743419 339316688608828536394297 := by
  unfold tailWord_743419
  simp only [CollatzResearch.WordTrace]
  refine ⟨27114718493727403702041311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18076478995818269134694207 27114718493727403702041311)
  ·
    refine ⟨40672077740591105553061967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27114718493727403702041311 40672077740591105553061967)
    ·
      refine ⟨61008116610886658329592951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40672077740591105553061967 61008116610886658329592951)
      ·
        refine ⟨91512174916329987494389427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61008116610886658329592951 91512174916329987494389427)
        ·
          refine ⟨137268262374494981241584141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91512174916329987494389427 137268262374494981241584141)
          ·
            refine ⟨51475598390435617965594053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137268262374494981241584141 51475598390435617965594053)
            ·
              refine ⟨9651674698206678368548885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51475598390435617965594053 9651674698206678368548885)
              ·
                refine ⟨452422251478438048525729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9651674698206678368548885 452422251478438048525729)
                ·
                  refine ⟨339316688608828536394297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452422251478438048525729 339316688608828536394297)
                  ·
                    rfl

theorem cell20_743419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 2].length) (baseStart_743419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743419 prefixEnd_743419 := by exact prefixLift 743419
  have htrace : WordTrace (prefixWord ++ tailWord_743419) baseStart_743419 baseEnd_743419 := by
    simpa [prefixWord, tailWord_743419, baseEnd_743419] using wordTrace_append hprefix tailTrace_743419
  have hstable : (prefixWord ++ tailWord_743419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743419).length < 2 ^ (prefixWord ++ tailWord_743419).sum := by decide
  have hdescent : baseEnd_743419 < baseStart_743419 := by decide
  rcases family_descends (prefixWord ++ tailWord_743419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743429 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 3]
def baseStart_743429 : Nat := 118140960795 + 743429 * 2 ^ 59
def prefixEnd_743429 : Nat := 4983230072969 + 3 ^ 40 * 743429 * 2
def baseEnd_743429 : Nat := 339321252881312946060923

theorem tailTrace_743429 : CollatzResearch.WordTrace tailWord_743429 prefixEnd_743429 339321252881312946060923 := by
  unfold tailWord_743429
  simp only [CollatzResearch.WordTrace]
  refine ⟨27115083223691175409905341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18076722149127450273270227 27115083223691175409905341)
  ·
    refine ⟨10168156208884190778714503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27115083223691175409905341 10168156208884190778714503)
    ·
      refine ⟨15252234313326286168071755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10168156208884190778714503 15252234313326286168071755)
      ·
        refine ⟨22878351469989429252107633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15252234313326286168071755 22878351469989429252107633)
        ·
          refine ⟨17158763602492071939080725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22878351469989429252107633 17158763602492071939080725)
          ·
            refine ⟨804317043866815872144409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17158763602492071939080725 804317043866815872144409)
            ·
              refine ⟨603237782900111904108307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804317043866815872144409 603237782900111904108307)
              ·
                refine ⟨904856674350167856162461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603237782900111904108307 904856674350167856162461)
                ·
                  refine ⟨339321252881312946060923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904856674350167856162461 339321252881312946060923)
                  ·
                    rfl

theorem cell20_743429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_743429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743429 prefixEnd_743429 := by exact prefixLift 743429
  have htrace : WordTrace (prefixWord ++ tailWord_743429) baseStart_743429 baseEnd_743429 := by
    simpa [prefixWord, tailWord_743429, baseEnd_743429] using wordTrace_append hprefix tailTrace_743429
  have hstable : (prefixWord ++ tailWord_743429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743429).length < 2 ^ (prefixWord ++ tailWord_743429).sum := by decide
  have hdescent : baseEnd_743429 < baseStart_743429 := by decide
  rcases family_descends (prefixWord ++ tailWord_743429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743464 : List Nat := [2, 1, 5, 3, 9]
def baseStart_743464 : Nat := 118140960795 + 743464 * 2 ^ 59
def prefixEnd_743464 : Nat := 4983230072969 + 3 ^ 40 * 743464 * 2
def baseEnd_743464 : Nat := 4189348491790226912273

theorem tailTrace_743464 : CollatzResearch.WordTrace tailWord_743464 prefixEnd_743464 4189348491790226912273 := by
  unfold tailWord_743464
  simp only [CollatzResearch.WordTrace]
  refine ⟨13558179889282188193714723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18077573185709584258286297 13558179889282188193714723)
  ·
    refine ⟨20337269833923282290572085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13558179889282188193714723 20337269833923282290572085)
    ·
      refine ⟨1906619046930307714741133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20337269833923282290572085 1906619046930307714741133)
      ·
        refine ⟨714982142598865393027925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1906619046930307714741133 714982142598865393027925)
        ·
          refine ⟨4189348491790226912273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 714982142598865393027925 4189348491790226912273)
          ·
            rfl

theorem cell20_743464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 9].length) (baseStart_743464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743464 prefixEnd_743464 := by exact prefixLift 743464
  have htrace : WordTrace (prefixWord ++ tailWord_743464) baseStart_743464 baseEnd_743464 := by
    simpa [prefixWord, tailWord_743464, baseEnd_743464] using wordTrace_append hprefix tailTrace_743464
  have hstable : (prefixWord ++ tailWord_743464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743464).length < 2 ^ (prefixWord ++ tailWord_743464).sum := by decide
  have hdescent : baseEnd_743464 < baseStart_743464 := by decide
  rcases family_descends (prefixWord ++ tailWord_743464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743470 : List Nat := [4, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_743470 : Nat := 118140960795 + 743470 * 2 ^ 59
def prefixEnd_743470 : Nat := 4983230072969 + 3 ^ 40 * 743470 * 2
def baseEnd_743470 : Nat := 339339966398499025694089

theorem tailTrace_743470 : CollatzResearch.WordTrace tailWord_743470 prefixEnd_743470 339339966398499025694089 := by
  unfold tailWord_743470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389572327067829926518483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18077719077695092941431909 3389572327067829926518483)
  ·
    refine ⟨5084358490601744889777725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3389572327067829926518483 5084358490601744889777725)
    ·
      refine ⟨1906634433975654333666647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5084358490601744889777725 1906634433975654333666647)
      ·
        refine ⟨2859951650963481500499971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906634433975654333666647 2859951650963481500499971)
        ·
          refine ⟨4289927476445222250749957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2859951650963481500499971 4289927476445222250749957)
          ·
            refine ⟨804361401833479172015617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4289927476445222250749957 804361401833479172015617)
            ·
              refine ⟨603271051375109379011713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804361401833479172015617 603271051375109379011713)
              ·
                refine ⟨452453288531332034258785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603271051375109379011713 452453288531332034258785)
                ·
                  refine ⟨339339966398499025694089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452453288531332034258785 339339966398499025694089)
                  ·
                    rfl

theorem cell20_743470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_743470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743470 prefixEnd_743470 := by exact prefixLift 743470
  have htrace : WordTrace (prefixWord ++ tailWord_743470) baseStart_743470 baseEnd_743470 := by
    simpa [prefixWord, tailWord_743470, baseEnd_743470] using wordTrace_append hprefix tailTrace_743470
  have hstable : (prefixWord ++ tailWord_743470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743470).length < 2 ^ (prefixWord ++ tailWord_743470).sum := by decide
  have hdescent : baseEnd_743470 < baseStart_743470 := by decide
  rcases family_descends (prefixWord ++ tailWord_743470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743474 : List Nat := [3, 2, 1, 1, 2, 4, 1, 4, 2]
def baseStart_743474 : Nat := 118140960795 + 743474 * 2 ^ 59
def prefixEnd_743474 : Nat := 4983230072969 + 3 ^ 40 * 743474 * 2
def baseEnd_743474 : Nat := 339341792107492789560739

theorem tailTrace_743474 : CollatzResearch.WordTrace tailWord_743474 prefixEnd_743474 339341792107492789560739 := by
  unfold tailWord_743474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6779181127132037023823369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18077816339018765396862317 6779181127132037023823369)
  ·
    refine ⟨5084385845349027767867527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6779181127132037023823369 5084385845349027767867527)
    ·
      refine ⟨7626578768023541651801291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5084385845349027767867527 7626578768023541651801291)
      ·
        refine ⟨11439868152035312477701937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7626578768023541651801291 11439868152035312477701937)
        ·
          refine ⟨8579901114026484358276453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11439868152035312477701937 8579901114026484358276453)
          ·
            refine ⟨1608731458879965817176835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8579901114026484358276453 1608731458879965817176835)
            ·
              refine ⟨2413097188319948725765253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1608731458879965817176835 2413097188319948725765253)
              ·
                refine ⟨452455722809990386080985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2413097188319948725765253 452455722809990386080985)
                ·
                  refine ⟨339341792107492789560739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452455722809990386080985 339341792107492789560739)
                  ·
                    rfl

theorem cell20_743474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_743474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743474 prefixEnd_743474 := by exact prefixLift 743474
  have htrace : WordTrace (prefixWord ++ tailWord_743474) baseStart_743474 baseEnd_743474 := by
    simpa [prefixWord, tailWord_743474, baseEnd_743474] using wordTrace_append hprefix tailTrace_743474
  have hstable : (prefixWord ++ tailWord_743474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743474).length < 2 ^ (prefixWord ++ tailWord_743474).sum := by decide
  have hdescent : baseEnd_743474 < baseStart_743474 := by decide
  rcases family_descends (prefixWord ++ tailWord_743474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743481 : List Nat := [1, 2, 1, 5, 3, 2, 1, 5]
def baseStart_743481 : Nat := 118140960795 + 743481 * 2 ^ 59
def prefixEnd_743481 : Nat := 4983230072969 + 3 ^ 40 * 743481 * 2
def baseEnd_743481 : Nat := 113114995699410625442459

theorem tailTrace_743481 : CollatzResearch.WordTrace tailWord_743481 prefixEnd_743481 113114995699410625442459 := by
  unfold tailWord_743481
  simp only [CollatzResearch.WordTrace]
  refine ⟨27116979819502788290798297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18077986546335192193865531 27116979819502788290798297)
  ·
    refine ⟨20337734864627091218098723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27116979819502788290798297 20337734864627091218098723)
    ·
      refine ⟨30506602296940636827148085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20337734864627091218098723 30506602296940636827148085)
      ·
        refine ⟨2859993965338184702545133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30506602296940636827148085 2859993965338184702545133)
        ·
          refine ⟨1072497737001819263454425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2859993965338184702545133 1072497737001819263454425)
          ·
            refine ⟨804373302751364447590819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072497737001819263454425 804373302751364447590819)
            ·
              refine ⟨1206559954127046671386229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804373302751364447590819 1206559954127046671386229)
              ·
                refine ⟨113114995699410625442459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1206559954127046671386229 113114995699410625442459)
                ·
                  rfl

theorem cell20_743481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 5].length) (baseStart_743481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743481 prefixEnd_743481 := by exact prefixLift 743481
  have htrace : WordTrace (prefixWord ++ tailWord_743481) baseStart_743481 baseEnd_743481 := by
    simpa [prefixWord, tailWord_743481, baseEnd_743481] using wordTrace_append hprefix tailTrace_743481
  have hstable : (prefixWord ++ tailWord_743481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743481).length < 2 ^ (prefixWord ++ tailWord_743481).sum := by decide
  have hdescent : baseEnd_743481 < baseStart_743481 := by decide
  rcases family_descends (prefixWord ++ tailWord_743481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743512 : List Nat := [2, 1, 2, 2, 1, 5, 2, 3, 2]
def baseStart_743512 : Nat := 118140960795 + 743512 * 2 ^ 59
def prefixEnd_743512 : Nat := 4983230072969 + 3 ^ 40 * 743512 * 2
def baseEnd_743512 : Nat := 339359136342933546293917

theorem tailTrace_743512 : CollatzResearch.WordTrace tailWord_743512 prefixEnd_743512 339359136342933546293917 := by
  unfold tailWord_743512
  simp only [CollatzResearch.WordTrace]
  refine ⟨13559055241195240292588395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18078740321593653723451193 13559055241195240292588395)
  ·
    refine ⟨20338582861792860438882593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13559055241195240292588395 20338582861792860438882593)
    ·
      refine ⟨15253937146344645329161945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20338582861792860438882593 15253937146344645329161945)
      ·
        refine ⟨11440452859758483996871459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15253937146344645329161945 11440452859758483996871459)
        ·
          refine ⟨17160679289637725995307189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11440452859758483996871459 17160679289637725995307189)
          ·
            refine ⟨1608813683403536812060049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17160679289637725995307189 1608813683403536812060049)
            ·
              refine ⟨1206610262552652609045037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608813683403536812060049 1206610262552652609045037)
              ·
                refine ⟨452478848457244728391889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1206610262552652609045037 452478848457244728391889)
                ·
                  refine ⟨339359136342933546293917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452478848457244728391889 339359136342933546293917)
                  ·
                    rfl

theorem cell20_743512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 2].length) (baseStart_743512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743512 prefixEnd_743512 := by exact prefixLift 743512
  have htrace : WordTrace (prefixWord ++ tailWord_743512) baseStart_743512 baseEnd_743512 := by
    simpa [prefixWord, tailWord_743512, baseEnd_743512] using wordTrace_append hprefix tailTrace_743512
  have hstable : (prefixWord ++ tailWord_743512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743512).length < 2 ^ (prefixWord ++ tailWord_743512).sum := by decide
  have hdescent : baseEnd_743512 < baseStart_743512 := by decide
  rcases family_descends (prefixWord ++ tailWord_743512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743518 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_743518 : Nat := 118140960795 + 743518 * 2 ^ 59
def prefixEnd_743518 : Nat := 4983230072969 + 3 ^ 40 * 743518 * 2
def baseEnd_743518 : Nat := 339361874906424192093893

theorem tailTrace_743518 : CollatzResearch.WordTrace tailWord_743518 prefixEnd_743518 339361874906424192093893 := by
  unfold tailWord_743518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389791165046092951236901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18078886213579162406596805 3389791165046092951236901)
  ·
    refine ⟨635585843446142428356919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3389791165046092951236901 635585843446142428356919)
    ·
      refine ⟨953378765169213642535379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635585843446142428356919 953378765169213642535379)
      ·
        refine ⟨1430068147753820463803069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953378765169213642535379 1430068147753820463803069)
        ·
          refine ⟨536275555407682673926151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1430068147753820463803069 536275555407682673926151)
          ·
            refine ⟨804413333111524010889227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536275555407682673926151 804413333111524010889227)
            ·
              refine ⟨1206619999667286016333841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804413333111524010889227 1206619999667286016333841)
              ·
                refine ⟨904964999750464512250381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206619999667286016333841 904964999750464512250381)
                ·
                  refine ⟨339361874906424192093893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904964999750464512250381 339361874906424192093893)
                  ·
                    rfl

theorem cell20_743518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_743518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743518 prefixEnd_743518 := by exact prefixLift 743518
  have htrace : WordTrace (prefixWord ++ tailWord_743518) baseStart_743518 baseEnd_743518 := by
    simpa [prefixWord, tailWord_743518, baseEnd_743518] using wordTrace_append hprefix tailTrace_743518
  have hstable : (prefixWord ++ tailWord_743518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743518).length < 2 ^ (prefixWord ++ tailWord_743518).sum := by decide
  have hdescent : baseEnd_743518 < baseStart_743518 := by decide
  rcases family_descends (prefixWord ++ tailWord_743518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743522 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_743522 : Nat := 118140960795 + 743522 * 2 ^ 59
def prefixEnd_743522 : Nat := 4983230072969 + 3 ^ 40 * 743522 * 2
def baseEnd_743522 : Nat := 339363700615417955960543

theorem tailTrace_743522 : CollatzResearch.WordTrace tailWord_743522 prefixEnd_743522 339363700615417955960543 := by
  unfold tailWord_743522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6779618803088563073260205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18078983474902834862027213 6779618803088563073260205)
  ·
    refine ⟨2542357051158211152472577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6779618803088563073260205 2542357051158211152472577)
    ·
      refine ⟨1906767788368658364354433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2542357051158211152472577 1906767788368658364354433)
      ·
        refine ⟨1430075841276493773265825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1906767788368658364354433 1430075841276493773265825)
        ·
          refine ⟨1072556880957370329949369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1430075841276493773265825 1072556880957370329949369)
          ·
            refine ⟨804417660718027747462027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072556880957370329949369 804417660718027747462027)
            ·
              refine ⟨1206626491077041621193041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804417660718027747462027 1206626491077041621193041)
              ·
                refine ⟨904969868307781215894781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206626491077041621193041 904969868307781215894781)
                ·
                  refine ⟨339363700615417955960543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904969868307781215894781 339363700615417955960543)
                  ·
                    rfl

theorem cell20_743522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_743522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743522 prefixEnd_743522 := by exact prefixLift 743522
  have htrace : WordTrace (prefixWord ++ tailWord_743522) baseStart_743522 baseEnd_743522 := by
    simpa [prefixWord, tailWord_743522, baseEnd_743522] using wordTrace_append hprefix tailTrace_743522
  have hstable : (prefixWord ++ tailWord_743522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743522).length < 2 ^ (prefixWord ++ tailWord_743522).sum := by decide
  have hdescent : baseEnd_743522 < baseStart_743522 := by decide
  rcases family_descends (prefixWord ++ tailWord_743522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743533 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 4]
def baseStart_743533 : Nat := 118140960795 + 743533 * 2 ^ 59
def prefixEnd_743533 : Nat := 4983230072969 + 3 ^ 40 * 743533 * 2
def baseEnd_743533 : Nat := 339368721315150806593831

theorem tailTrace_743533 : CollatzResearch.WordTrace tailWord_743533 prefixEnd_743533 339368721315150806593831 := by
  unfold tailWord_743533
  simp only [CollatzResearch.WordTrace]
  refine ⟨27118876415314401171691253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18079250943542934114460835 27118876415314401171691253)
  ·
    refine ⟨2542394663935725109846055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27118876415314401171691253 2542394663935725109846055)
    ·
      refine ⟨3813591995903587664769083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2542394663935725109846055 3813591995903587664769083)
      ·
        refine ⟨5720387993855381497153625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3813591995903587664769083 5720387993855381497153625)
        ·
          refine ⟨4290290995391536122865219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5720387993855381497153625 4290290995391536122865219)
          ·
            refine ⟨6435436493087304184297829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290290995391536122865219 6435436493087304184297829)
            ·
              refine ⟨1206644342453869534555843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6435436493087304184297829 1206644342453869534555843)
              ·
                refine ⟨1809966513680804301833765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206644342453869534555843 1809966513680804301833765)
                ·
                  refine ⟨339368721315150806593831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1809966513680804301833765 339368721315150806593831)
                  ·
                    rfl

theorem cell20_743533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_743533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743533 prefixEnd_743533 := by exact prefixLift 743533
  have htrace : WordTrace (prefixWord ++ tailWord_743533) baseStart_743533 baseEnd_743533 := by
    simpa [prefixWord, tailWord_743533, baseEnd_743533] using wordTrace_append hprefix tailTrace_743533
  have hstable : (prefixWord ++ tailWord_743533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743533).length < 2 ^ (prefixWord ++ tailWord_743533).sum := by decide
  have hdescent : baseEnd_743533 < baseStart_743533 := by decide
  rcases family_descends (prefixWord ++ tailWord_743533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743557 : List Nat := [1, 3, 1, 1, 5, 3, 2, 4]
def baseStart_743557 : Nat := 118140960795 + 743557 * 2 ^ 59
def prefixEnd_743557 : Nat := 4983230072969 + 3 ^ 40 * 743557 * 2
def baseEnd_743557 : Nat := 113126558523037796597911

theorem tailTrace_743557 : CollatzResearch.WordTrace tailWord_743557 prefixEnd_743557 113126558523037796597911 := by
  unfold tailWord_743557
  simp only [CollatzResearch.WordTrace]
  refine ⟨27119751767227453270564925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18079834511484968847043283 27119751767227453270564925)
  ·
    refine ⟨10169906912710294976461847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27119751767227453270564925 10169906912710294976461847)
    ·
      refine ⟨15254860369065442464692771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10169906912710294976461847 15254860369065442464692771)
      ·
        refine ⟨22882290553598163697039157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15254860369065442464692771 22882290553598163697039157)
        ·
          refine ⟨2145214739399827846597421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22882290553598163697039157 2145214739399827846597421)
          ·
            refine ⟨804455527274935442474033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2145214739399827846597421 804455527274935442474033)
            ·
              refine ⟨603341645456201581855525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804455527274935442474033 603341645456201581855525)
              ·
                refine ⟨113126558523037796597911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 603341645456201581855525 113126558523037796597911)
                ·
                  rfl

theorem cell20_743557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 4].length) (baseStart_743557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743557 prefixEnd_743557 := by exact prefixLift 743557
  have htrace : WordTrace (prefixWord ++ tailWord_743557) baseStart_743557 baseEnd_743557 := by
    simpa [prefixWord, tailWord_743557, baseEnd_743557] using wordTrace_append hprefix tailTrace_743557
  have hstable : (prefixWord ++ tailWord_743557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743557).length < 2 ^ (prefixWord ++ tailWord_743557).sum := by decide
  have hdescent : baseEnd_743557 < baseStart_743557 := by decide
  rcases family_descends (prefixWord ++ tailWord_743557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743561 : List Nat := [1, 2, 1, 1, 4, 2, 3, 6]
def baseStart_743561 : Nat := 118140960795 + 743561 * 2 ^ 59
def prefixEnd_743561 : Nat := 4983230072969 + 3 ^ 40 * 743561 * 2
def baseEnd_743561 : Nat := 113127167092702384553461

theorem tailTrace_743561 : CollatzResearch.WordTrace tailWord_743561 prefixEnd_743561 113127167092702384553461 := by
  unfold tailWord_743561
  simp only [CollatzResearch.WordTrace]
  refine ⟨27119897659212961953710537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18079931772808641302473691 27119897659212961953710537)
  ·
    refine ⟨20339923244409721465282903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27119897659212961953710537 20339923244409721465282903)
    ·
      refine ⟨30509884866614582197924355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20339923244409721465282903 30509884866614582197924355)
      ·
        refine ⟨45764827299921873296886533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30509884866614582197924355 45764827299921873296886533)
        ·
          refine ⟨8580905118735351243166225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45764827299921873296886533 8580905118735351243166225)
          ·
            refine ⟨6435678839051513432374669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8580905118735351243166225 6435678839051513432374669)
            ·
              refine ⟨2413379564644317537140501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6435678839051513432374669 2413379564644317537140501)
              ·
                refine ⟨113127167092702384553461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2413379564644317537140501 113127167092702384553461)
                ·
                  rfl

theorem cell20_743561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_743561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743561 prefixEnd_743561 := by exact prefixLift 743561
  have htrace : WordTrace (prefixWord ++ tailWord_743561) baseStart_743561 baseEnd_743561 := by
    simpa [prefixWord, tailWord_743561, baseEnd_743561] using wordTrace_append hprefix tailTrace_743561
  have hstable : (prefixWord ++ tailWord_743561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743561).length < 2 ^ (prefixWord ++ tailWord_743561).sum := by decide
  have hdescent : baseEnd_743561 < baseStart_743561 := by decide
  rcases family_descends (prefixWord ++ tailWord_743561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743568 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_743568 : Nat := 118140960795 + 743568 * 2 ^ 59
def prefixEnd_743568 : Nat := 4983230072969 + 3 ^ 40 * 743568 * 2
def baseEnd_743568 : Nat := 339384696268846240427021

theorem tailTrace_743568 : CollatzResearch.WordTrace tailWord_743568 prefixEnd_743568 339384696268846240427021 := by
  unfold tailWord_743568
  simp only [CollatzResearch.WordTrace]
  refine ⟨13560076485093801074607679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18080101980125068099476905 13560076485093801074607679)
  ·
    refine ⟨20340114727640701611911519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13560076485093801074607679 20340114727640701611911519)
    ·
      refine ⟨30510172091461052417867279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20340114727640701611911519 30510172091461052417867279)
      ·
        refine ⟨45765258137191578626800919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30510172091461052417867279 45765258137191578626800919)
        ·
          refine ⟨68647887205787367940201379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45765258137191578626800919 68647887205787367940201379)
          ·
            refine ⟨102971830808681051910302069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68647887205787367940201379 102971830808681051910302069)
            ·
              refine ⟨9653609138313848616590819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102971830808681051910302069 9653609138313848616590819)
              ·
                refine ⟨14480413707470772924886229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9653609138313848616590819 14480413707470772924886229)
                ·
                  refine ⟨339384696268846240427021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14480413707470772924886229 339384696268846240427021)
                  ·
                    rfl

theorem cell20_743568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_743568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743568 prefixEnd_743568 := by exact prefixLift 743568
  have htrace : WordTrace (prefixWord ++ tailWord_743568) baseStart_743568 baseEnd_743568 := by
    simpa [prefixWord, tailWord_743568, baseEnd_743568] using wordTrace_append hprefix tailTrace_743568
  have hstable : (prefixWord ++ tailWord_743568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743568).length < 2 ^ (prefixWord ++ tailWord_743568).sum := by decide
  have hdescent : baseEnd_743568 < baseStart_743568 := by decide
  rcases family_descends (prefixWord ++ tailWord_743568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743585 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 5]
def baseStart_743585 : Nat := 118140960795 + 743585 * 2 ^ 59
def prefixEnd_743585 : Nat := 4983230072969 + 3 ^ 40 * 743585 * 2
def baseEnd_743585 : Nat := 339392455532069736860285

theorem tailTrace_743585 : CollatzResearch.WordTrace tailWord_743585 prefixEnd_743585 339392455532069736860285 := by
  unfold tailWord_743585
  simp only [CollatzResearch.WordTrace]
  refine ⟨27120773011126014052584209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18080515340750676035056139 27120773011126014052584209)
  ·
    refine ⟨20340579758344510539438157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27120773011126014052584209 20340579758344510539438157)
    ·
      refine ⟨7627717409379191452289309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20340579758344510539438157 7627717409379191452289309)
      ·
        refine ⟨2860394028517196794608491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7627717409379191452289309 2860394028517196794608491)
        ·
          refine ⟨4290591042775795191912737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860394028517196794608491 4290591042775795191912737)
          ·
            refine ⟨3217943282081846393934553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4290591042775795191912737 3217943282081846393934553)
            ·
              refine ⟨2413457461561384795450915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3217943282081846393934553 2413457461561384795450915)
              ·
                refine ⟨3620186192342077193176373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413457461561384795450915 3620186192342077193176373)
                ·
                  refine ⟨339392455532069736860285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3620186192342077193176373 339392455532069736860285)
                  ·
                    rfl

theorem cell20_743585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_743585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743585 prefixEnd_743585 := by exact prefixLift 743585
  have htrace : WordTrace (prefixWord ++ tailWord_743585) baseStart_743585 baseEnd_743585 := by
    simpa [prefixWord, tailWord_743585, baseEnd_743585] using wordTrace_append hprefix tailTrace_743585
  have hstable : (prefixWord ++ tailWord_743585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743585).length < 2 ^ (prefixWord ++ tailWord_743585).sum := by decide
  have hdescent : baseEnd_743585 < baseStart_743585 := by decide
  rcases family_descends (prefixWord ++ tailWord_743585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743588 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 4]
def baseStart_743588 : Nat := 118140960795 + 743588 * 2 ^ 59
def prefixEnd_743588 : Nat := 4983230072969 + 3 ^ 40 * 743588 * 2
def baseEnd_743588 : Nat := 339393824813815059760273

theorem tailTrace_743588 : CollatzResearch.WordTrace tailWord_743588 prefixEnd_743588 339393824813815059760273 := by
  unfold tailWord_743588
  simp only [CollatzResearch.WordTrace]
  refine ⟨13560441215057572782471709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18080588286743430376628945 13560441215057572782471709)
  ·
    refine ⟨5085165455646589793426891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13560441215057572782471709 5085165455646589793426891)
    ·
      refine ⟨7627748183469884690140337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5085165455646589793426891 7627748183469884690140337)
      ·
        refine ⟨5720811137602413517605253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7627748183469884690140337 5720811137602413517605253)
        ·
          refine ⟨1072652088300452534550985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5720811137602413517605253 1072652088300452534550985)
          ·
            refine ⟨804489066225339400913239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072652088300452534550985 804489066225339400913239)
            ·
              refine ⟨1206733599338009101369859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804489066225339400913239 1206733599338009101369859)
              ·
                refine ⟨1810100399007013652054789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206733599338009101369859 1810100399007013652054789)
                ·
                  refine ⟨339393824813815059760273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1810100399007013652054789 339393824813815059760273)
                  ·
                    rfl

theorem cell20_743588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_743588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743588 prefixEnd_743588 := by exact prefixLift 743588
  have htrace : WordTrace (prefixWord ++ tailWord_743588) baseStart_743588 baseEnd_743588 := by
    simpa [prefixWord, tailWord_743588, baseEnd_743588] using wordTrace_append hprefix tailTrace_743588
  have hstable : (prefixWord ++ tailWord_743588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743588).length < 2 ^ (prefixWord ++ tailWord_743588).sum := by decide
  have hdescent : baseEnd_743588 < baseStart_743588 := by decide
  rcases family_descends (prefixWord ++ tailWord_743588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743598 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_743598 : Nat := 118140960795 + 743598 * 2 ^ 59
def prefixEnd_743598 : Nat := 4983230072969 + 3 ^ 40 * 743598 * 2
def baseEnd_743598 : Nat := 339398389086299469426899

theorem tailTrace_743598 : CollatzResearch.WordTrace tailWord_743598 prefixEnd_743598 339398389086299469426899 := by
  unfold tailWord_743598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390155895009864659100931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18080831440052611515204965 3390155895009864659100931)
  ·
    refine ⟨5085233842514796988651397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3390155895009864659100931 5085233842514796988651397)
    ·
      refine ⟨953481345471524435372137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5085233842514796988651397 953481345471524435372137)
      ·
        refine ⟨715111009103643326529103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 953481345471524435372137 715111009103643326529103)
        ·
          refine ⟨1072666513655464989793655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715111009103643326529103 1072666513655464989793655)
          ·
            refine ⟨1608999770483197484690483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072666513655464989793655 1608999770483197484690483)
            ·
              refine ⟨2413499655724796227035725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1608999770483197484690483 2413499655724796227035725)
              ·
                refine ⟨905062370896798585138397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2413499655724796227035725 905062370896798585138397)
                ·
                  refine ⟨339398389086299469426899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905062370896798585138397 339398389086299469426899)
                  ·
                    rfl

theorem cell20_743598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_743598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743598 prefixEnd_743598 := by exact prefixLift 743598
  have htrace : WordTrace (prefixWord ++ tailWord_743598) baseStart_743598 baseEnd_743598 := by
    simpa [prefixWord, tailWord_743598, baseEnd_743598] using wordTrace_append hprefix tailTrace_743598
  have hstable : (prefixWord ++ tailWord_743598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743598).length < 2 ^ (prefixWord ++ tailWord_743598).sum := by decide
  have hdescent : baseEnd_743598 < baseStart_743598 := by decide
  rcases family_descends (prefixWord ++ tailWord_743598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743637 : List Nat := [1, 3, 2, 4, 10]
def baseStart_743637 : Nat := 118140960795 + 743637 * 2 ^ 59
def prefixEnd_743637 : Nat := 4983230072969 + 3 ^ 40 * 743637 * 2
def baseEnd_743637 : Nat := 4190323330234427989219

theorem tailTrace_743637 : CollatzResearch.WordTrace tailWord_743637 prefixEnd_743637 4190323330234427989219 := by
  unfold tailWord_743637
  simp only [CollatzResearch.WordTrace]
  refine ⟨27122669606937626933477165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18081779737958417955651443 27122669606937626933477165)
  ·
    refine ⟨10171001102601610100053937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27122669606937626933477165 10171001102601610100053937)
    ·
      refine ⟨7628250826951207575040453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10171001102601610100053937 7628250826951207575040453)
      ·
        refine ⟨1430297030053351420320085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7628250826951207575040453 1430297030053351420320085)
        ·
          refine ⟨4190323330234427989219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1430297030053351420320085 4190323330234427989219)
          ·
            rfl

theorem cell20_743637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 10].length) (baseStart_743637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743637 prefixEnd_743637 := by exact prefixLift 743637
  have htrace : WordTrace (prefixWord ++ tailWord_743637) baseStart_743637 baseEnd_743637 := by
    simpa [prefixWord, tailWord_743637, baseEnd_743637] using wordTrace_append hprefix tailTrace_743637
  have hstable : (prefixWord ++ tailWord_743637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743637).length < 2 ^ (prefixWord ++ tailWord_743637).sum := by decide
  have hdescent : baseEnd_743637 < baseStart_743637 := by decide
  rcases family_descends (prefixWord ++ tailWord_743637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743640 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 3]
def baseStart_743640 : Nat := 118140960795 + 743640 * 2 ^ 59
def prefixEnd_743640 : Nat := 4983230072969 + 3 ^ 40 * 743640 * 2
def baseEnd_743640 : Nat := 339417559030733990026727

theorem tailTrace_743640 : CollatzResearch.WordTrace tailWord_743640 prefixEnd_743640 339417559030733990026727 := by
  unfold tailWord_743640
  simp only [CollatzResearch.WordTrace]
  refine ⟨13561389512963379222918187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18081852683951172297224249 13561389512963379222918187)
  ·
    refine ⟨20342084269445068834377281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13561389512963379222918187 20342084269445068834377281)
    ·
      refine ⟨15256563202083801625782961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20342084269445068834377281 15256563202083801625782961)
      ·
        refine ⟨11442422401562851219337221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15256563202083801625782961 11442422401562851219337221)
        ·
          refine ⟨2145454200293034603625729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11442422401562851219337221 2145454200293034603625729)
          ·
            refine ⟨1609090650219775952719297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2145454200293034603625729 1609090650219775952719297)
            ·
              refine ⟨1206817987664831964539473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1609090650219775952719297 1206817987664831964539473)
              ·
                refine ⟨905113490748623973404605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206817987664831964539473 905113490748623973404605)
                ·
                  refine ⟨339417559030733990026727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905113490748623973404605 339417559030733990026727)
                  ·
                    rfl

theorem cell20_743640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_743640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743640 prefixEnd_743640 := by exact prefixLift 743640
  have htrace : WordTrace (prefixWord ++ tailWord_743640) baseStart_743640 baseEnd_743640 := by
    simpa [prefixWord, tailWord_743640, baseEnd_743640] using wordTrace_append hprefix tailTrace_743640
  have hstable : (prefixWord ++ tailWord_743640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743640).length < 2 ^ (prefixWord ++ tailWord_743640).sum := by decide
  have hdescent : baseEnd_743640 < baseStart_743640 := by decide
  rcases family_descends (prefixWord ++ tailWord_743640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743730 : List Nat := [3, 2, 1, 1, 5, 1, 1, 6]
def baseStart_743730 : Nat := 118140960795 + 743730 * 2 ^ 59
def prefixEnd_743730 : Nat := 4983230072969 + 3 ^ 40 * 743730 * 2
def baseEnd_743730 : Nat := 113152879161031225675453

theorem tailTrace_743730 : CollatzResearch.WordTrace tailWord_743730 prefixEnd_743730 113152879161031225675453 := by
  unfold tailWord_743730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6781515398900175954153161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18084041063733802544408429 6781515398900175954153161)
  ·
    refine ⟨5086136549175131965614871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6781515398900175954153161 5086136549175131965614871)
    ·
      refine ⟨7629204823762697948422307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5086136549175131965614871 7629204823762697948422307)
      ·
        refine ⟨11443807235644046922633461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7629204823762697948422307 11443807235644046922633461)
        ·
          refine ⟨1072856928341629398996887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11443807235644046922633461 1072856928341629398996887)
          ·
            refine ⟨1609285392512444098495331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072856928341629398996887 1609285392512444098495331)
            ·
              refine ⟨2413928088768666147742997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609285392512444098495331 2413928088768666147742997)
              ·
                refine ⟨113152879161031225675453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2413928088768666147742997 113152879161031225675453)
                ·
                  rfl

theorem cell20_743730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_743730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743730 prefixEnd_743730 := by exact prefixLift 743730
  have htrace : WordTrace (prefixWord ++ tailWord_743730) baseStart_743730 baseEnd_743730 := by
    simpa [prefixWord, tailWord_743730, baseEnd_743730] using wordTrace_append hprefix tailTrace_743730
  have hstable : (prefixWord ++ tailWord_743730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743730).length < 2 ^ (prefixWord ++ tailWord_743730).sum := by decide
  have hdescent : baseEnd_743730 < baseStart_743730 := by decide
  rcases family_descends (prefixWord ++ tailWord_743730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743737 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 5]
def baseStart_743737 : Nat := 118140960795 + 743737 * 2 ^ 59
def prefixEnd_743737 : Nat := 4983230072969 + 3 ^ 40 * 743737 * 2
def baseEnd_743737 : Nat := 339461832473832763792997

theorem tailTrace_743737 : CollatzResearch.WordTrace tailWord_743737 prefixEnd_743737 339461832473832763792997 := by
  unfold tailWord_743737
  simp only [CollatzResearch.WordTrace]
  refine ⟨27126316906575344012117465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18084211271050229341411643 27126316906575344012117465)
  ·
    refine ⟨20344737679931508009088099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27126316906575344012117465 20344737679931508009088099)
    ·
      refine ⟨30517106519897262013632149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20344737679931508009088099 30517106519897262013632149)
      ·
        refine ⟨1430489368120184156889007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30517106519897262013632149 1430489368120184156889007)
        ·
          refine ⟨2145734052180276235333511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430489368120184156889007 2145734052180276235333511)
          ·
            refine ⟨3218601078270414353000267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145734052180276235333511 3218601078270414353000267)
            ·
              refine ⟨4827901617405621529500401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3218601078270414353000267 4827901617405621529500401)
              ·
                refine ⟨3620926213054216147125301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827901617405621529500401 3620926213054216147125301)
                ·
                  refine ⟨339461832473832763792997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3620926213054216147125301 339461832473832763792997)
                  ·
                    rfl

theorem cell20_743737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_743737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743737 prefixEnd_743737 := by exact prefixLift 743737
  have htrace : WordTrace (prefixWord ++ tailWord_743737) baseStart_743737 baseEnd_743737 := by
    simpa [prefixWord, tailWord_743737, baseEnd_743737] using wordTrace_append hprefix tailTrace_743737
  have hstable : (prefixWord ++ tailWord_743737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743737).length < 2 ^ (prefixWord ++ tailWord_743737).sum := by decide
  have hdescent : baseEnd_743737 < baseStart_743737 := by decide
  rcases family_descends (prefixWord ++ tailWord_743737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743761 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 4]
def baseStart_743761 : Nat := 118140960795 + 743761 * 2 ^ 59
def prefixEnd_743761 : Nat := 4983230072969 + 3 ^ 40 * 743761 * 2
def baseEnd_743761 : Nat := 339472786727795346992899

theorem tailTrace_743761 : CollatzResearch.WordTrace tailWord_743761 prefixEnd_743761 339472786727795346992899 := by
  unfold tailWord_743761
  simp only [CollatzResearch.WordTrace]
  refine ⟨27127192258488396110991137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18084794838992264073994091 27127192258488396110991137)
  ·
    refine ⟨20345394193866297083243353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27127192258488396110991137 20345394193866297083243353)
    ·
      refine ⟨15259045645399722812432515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20345394193866297083243353 15259045645399722812432515)
      ·
        refine ⟨22888568468099584218648773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15259045645399722812432515 22888568468099584218648773)
        ·
          refine ⟨4291606587768672040996645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22888568468099584218648773 4291606587768672040996645)
          ·
            refine ⟨804676235206626007686871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4291606587768672040996645 804676235206626007686871)
            ·
              refine ⟨1207014352809939011530307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804676235206626007686871 1207014352809939011530307)
              ·
                refine ⟨1810521529214908517295461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207014352809939011530307 1810521529214908517295461)
                ·
                  refine ⟨339472786727795346992899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1810521529214908517295461 339472786727795346992899)
                  ·
                    rfl

theorem cell20_743761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_743761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743761 prefixEnd_743761 := by exact prefixLift 743761
  have htrace : WordTrace (prefixWord ++ tailWord_743761) baseStart_743761 baseEnd_743761 := by
    simpa [prefixWord, tailWord_743761, baseEnd_743761] using wordTrace_append hprefix tailTrace_743761
  have hstable : (prefixWord ++ tailWord_743761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743761).length < 2 ^ (prefixWord ++ tailWord_743761).sum := by decide
  have hdescent : baseEnd_743761 < baseStart_743761 := by decide
  rcases family_descends (prefixWord ++ tailWord_743761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743789 : List Nat := [1, 5, 1, 1, 1, 2, 1, 8]
def baseStart_743789 : Nat := 118140960795 + 743789 * 2 ^ 59
def prefixEnd_743789 : Nat := 4983230072969 + 3 ^ 40 * 743789 * 2
def baseEnd_743789 : Nat := 113161855563583898019817

theorem tailTrace_743789 : CollatzResearch.WordTrace tailWord_743789 prefixEnd_743789 113161855563583898019817 := by
  unfold tailWord_743789
  simp only [CollatzResearch.WordTrace]
  refine ⟨27128213502386956893010421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18085475668257971262006947 27128213502386956893010421)
  ·
    refine ⟨2543270015848777208719727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27128213502386956893010421 2543270015848777208719727)
    ·
      refine ⟨3814905023773165813079591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2543270015848777208719727 3814905023773165813079591)
      ·
        refine ⟨5722357535659748719619387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3814905023773165813079591 5722357535659748719619387)
        ·
          refine ⟨8583536303489623079429081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5722357535659748719619387 8583536303489623079429081)
          ·
            refine ⟨6437652227617217309571811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8583536303489623079429081 6437652227617217309571811)
            ·
              refine ⟨9656478341425825964357717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6437652227617217309571811 9656478341425825964357717)
              ·
                refine ⟨113161855563583898019817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9656478341425825964357717 113161855563583898019817)
                ·
                  rfl

theorem cell20_743789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_743789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743789 prefixEnd_743789 := by exact prefixLift 743789
  have htrace : WordTrace (prefixWord ++ tailWord_743789) baseStart_743789 baseEnd_743789 := by
    simpa [prefixWord, tailWord_743789, baseEnd_743789] using wordTrace_append hprefix tailTrace_743789
  have hstable : (prefixWord ++ tailWord_743789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743789).length < 2 ^ (prefixWord ++ tailWord_743789).sum := by decide
  have hdescent : baseEnd_743789 < baseStart_743789 := by decide
  rcases family_descends (prefixWord ++ tailWord_743789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743837 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 4]
def baseStart_743837 : Nat := 118140960795 + 743837 * 2 ^ 59
def prefixEnd_743837 : Nat := 4983230072969 + 3 ^ 40 * 743837 * 2
def baseEnd_743837 : Nat := 339507475198676860459255

theorem tailTrace_743837 : CollatzResearch.WordTrace tailWord_743837 prefixEnd_743837 339507475198676860459255 := by
  unfold tailWord_743837
  simp only [CollatzResearch.WordTrace]
  refine ⟨27129964206213061090757765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18086642804142040727171843 27129964206213061090757765)
  ·
    refine ⟨5086868288664948954517081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27129964206213061090757765 5086868288664948954517081)
    ·
      refine ⟨3815151216498711715887811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5086868288664948954517081 3815151216498711715887811)
      ·
        refine ⟨5722726824748067573831717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815151216498711715887811 5722726824748067573831717)
        ·
          refine ⟨1073011279640262670093447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5722726824748067573831717 1073011279640262670093447)
          ·
            refine ⟨1609516919460394005140171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073011279640262670093447 1609516919460394005140171)
            ·
              refine ⟨2414275379190591007710257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609516919460394005140171 2414275379190591007710257)
              ·
                refine ⟨1810706534392943255782693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414275379190591007710257 1810706534392943255782693)
                ·
                  refine ⟨339507475198676860459255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1810706534392943255782693 339507475198676860459255)
                  ·
                    rfl

theorem cell20_743837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_743837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743837 prefixEnd_743837 := by exact prefixLift 743837
  have htrace : WordTrace (prefixWord ++ tailWord_743837) baseStart_743837 baseEnd_743837 := by
    simpa [prefixWord, tailWord_743837, baseEnd_743837] using wordTrace_append hprefix tailTrace_743837
  have hstable : (prefixWord ++ tailWord_743837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743837).length < 2 ^ (prefixWord ++ tailWord_743837).sum := by decide
  have hdescent : baseEnd_743837 < baseStart_743837 := by decide
  rcases family_descends (prefixWord ++ tailWord_743837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743865 : List Nat := [1, 2, 1, 4, 3, 2, 7]
def baseStart_743865 : Nat := 118140960795 + 743865 * 2 ^ 59
def prefixEnd_743865 : Nat := 4983230072969 + 3 ^ 40 * 743865 * 2
def baseEnd_743865 : Nat := 37724472795737023058423

theorem tailTrace_743865 : CollatzResearch.WordTrace tailWord_743865 prefixEnd_743865 37724472795737023058423 := by
  unfold tailWord_743865
  simp only [CollatzResearch.WordTrace]
  refine ⟨27130985450111621872777049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18087323633407747915184699 27130985450111621872777049)
  ·
    refine ⟨20348239087583716404582787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27130985450111621872777049 20348239087583716404582787)
    ·
      refine ⟨30522358631375574606874181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20348239087583716404582787 30522358631375574606874181)
      ·
        refine ⟨5722942243382920238788909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30522358631375574606874181 5722942243382920238788909)
        ·
          refine ⟨2146103341268595089545841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5722942243382920238788909 2146103341268595089545841)
          ·
            refine ⟨1609577505951446317159381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2146103341268595089545841 1609577505951446317159381)
            ·
              refine ⟨37724472795737023058423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1609577505951446317159381 37724472795737023058423)
              ·
                rfl

theorem cell20_743865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 7].length) (baseStart_743865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743865 prefixEnd_743865 := by exact prefixLift 743865
  have htrace : WordTrace (prefixWord ++ tailWord_743865) baseStart_743865 baseEnd_743865 := by
    simpa [prefixWord, tailWord_743865, baseEnd_743865] using wordTrace_append hprefix tailTrace_743865
  have hstable : (prefixWord ++ tailWord_743865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743865).length < 2 ^ (prefixWord ++ tailWord_743865).sum := by decide
  have hdescent : baseEnd_743865 < baseStart_743865 := by decide
  rcases family_descends (prefixWord ++ tailWord_743865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743868 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 3]
def baseStart_743868 : Nat := 118140960795 + 743868 * 2 ^ 59
def prefixEnd_743868 : Nat := 4983230072969 + 3 ^ 40 * 743868 * 2
def baseEnd_743868 : Nat := 339521624443378530425795

theorem tailTrace_743868 : CollatzResearch.WordTrace tailWord_743868 prefixEnd_743868 339521624443378530425795 := by
  unfold tailWord_743868
  simp only [CollatzResearch.WordTrace]
  refine ⟨13565547434550376692568129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18087396579400502256757505 13565547434550376692568129)
  ·
    refine ⟨10174160575912782519426097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13565547434550376692568129 10174160575912782519426097)
    ·
      refine ⟨7630620431934586889569573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10174160575912782519426097 7630620431934586889569573)
      ·
        refine ⟨1430741330987735041794295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7630620431934586889569573 1430741330987735041794295)
        ·
          refine ⟨2146111996481602562691443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430741330987735041794295 2146111996481602562691443)
          ·
            refine ⟨3219167994722403844037165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146111996481602562691443 3219167994722403844037165)
            ·
              refine ⟨1207187998020901441513937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3219167994722403844037165 1207187998020901441513937)
              ·
                refine ⟨905390998515676081135453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207187998020901441513937 905390998515676081135453)
                ·
                  refine ⟨339521624443378530425795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905390998515676081135453 339521624443378530425795)
                  ·
                    rfl

theorem cell20_743868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_743868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743868 prefixEnd_743868 := by exact prefixLift 743868
  have htrace : WordTrace (prefixWord ++ tailWord_743868) baseStart_743868 baseEnd_743868 := by
    simpa [prefixWord, tailWord_743868, baseEnd_743868] using wordTrace_append hprefix tailTrace_743868
  have hstable : (prefixWord ++ tailWord_743868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743868).length < 2 ^ (prefixWord ++ tailWord_743868).sum := by decide
  have hdescent : baseEnd_743868 < baseStart_743868 := by decide
  rcases family_descends (prefixWord ++ tailWord_743868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743903 : List Nat := [1, 1, 2, 3, 3, 3, 1, 6]
def baseStart_743903 : Nat := 118140960795 + 743903 * 2 ^ 59
def prefixEnd_743903 : Nat := 4983230072969 + 3 ^ 40 * 743903 * 2
def baseEnd_743903 : Nat := 113179199799024654752995

theorem tailTrace_743903 : CollatzResearch.WordTrace tailWord_743903 prefixEnd_743903 113179199799024654752995 := by
  unfold tailWord_743903
  simp only [CollatzResearch.WordTrace]
  refine ⟨27132371423973954362660363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18088247615982636241773575 27132371423973954362660363)
  ·
    refine ⟨40698557135960931543990545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27132371423973954362660363 40698557135960931543990545)
    ·
      refine ⟨30523917851970698657992909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40698557135960931543990545 30523917851970698657992909)
      ·
        refine ⟨11446469194489011996747341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30523917851970698657992909 11446469194489011996747341)
        ·
          refine ⟨4292425947933379498780253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11446469194489011996747341 4292425947933379498780253)
          ·
            refine ⟨1609659730475017312042595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4292425947933379498780253 1609659730475017312042595)
            ·
              refine ⟨2414489595712525968063893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609659730475017312042595 2414489595712525968063893)
              ·
                refine ⟨113179199799024654752995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2414489595712525968063893 113179199799024654752995)
                ·
                  rfl

theorem cell20_743903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_743903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743903 prefixEnd_743903 := by exact prefixLift 743903
  have htrace : WordTrace (prefixWord ++ tailWord_743903) baseStart_743903 baseEnd_743903 := by
    simpa [prefixWord, tailWord_743903, baseEnd_743903] using wordTrace_append hprefix tailTrace_743903
  have hstable : (prefixWord ++ tailWord_743903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743903).length < 2 ^ (prefixWord ++ tailWord_743903).sum := by decide
  have hdescent : baseEnd_743903 < baseStart_743903 := by decide
  rcases family_descends (prefixWord ++ tailWord_743903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743909 : List Nat := [1, 3, 1, 5, 2, 2, 1, 3, 2]
def baseStart_743909 : Nat := 118140960795 + 743909 * 2 ^ 59
def prefixEnd_743909 : Nat := 4983230072969 + 3 ^ 40 * 743909 * 2
def baseEnd_743909 : Nat := 339540337960564610058961

theorem tailTrace_743909 : CollatzResearch.WordTrace tailWord_743909 prefixEnd_743909 339540337960564610058961 := by
  unfold tailWord_743909
  simp only [CollatzResearch.WordTrace]
  refine ⟨27132590261952217387378781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18088393507968144924919187 27132590261952217387378781)
  ·
    refine ⟨10174721348232081520267043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27132590261952217387378781 10174721348232081520267043)
    ·
      refine ⟨15262082022348122280400565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10174721348232081520267043 15262082022348122280400565)
      ·
        refine ⟨1430820189595136463787553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15262082022348122280400565 1430820189595136463787553)
        ·
          refine ⟨1073115142196352347840665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1430820189595136463787553 1073115142196352347840665)
          ·
            refine ⟨804836356647264260880499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073115142196352347840665 804836356647264260880499)
            ·
              refine ⟨1207254534970896391320749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804836356647264260880499 1207254534970896391320749)
              ·
                refine ⟨452720450614086146745281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1207254534970896391320749 452720450614086146745281)
                ·
                  refine ⟨339540337960564610058961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452720450614086146745281 339540337960564610058961)
                  ·
                    rfl

theorem cell20_743909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_743909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743909 prefixEnd_743909 := by exact prefixLift 743909
  have htrace : WordTrace (prefixWord ++ tailWord_743909) baseStart_743909 baseEnd_743909 := by
    simpa [prefixWord, tailWord_743909, baseEnd_743909] using wordTrace_append hprefix tailTrace_743909
  have hstable : (prefixWord ++ tailWord_743909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743909).length < 2 ^ (prefixWord ++ tailWord_743909).sum := by decide
  have hdescent : baseEnd_743909 < baseStart_743909 := by decide
  rcases family_descends (prefixWord ++ tailWord_743909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743955 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_743955 : Nat := 118140960795 + 743955 * 2 ^ 59
def prefixEnd_743955 : Nat := 4983230072969 + 3 ^ 40 * 743955 * 2
def baseEnd_743955 : Nat := 339561333613992894525439

theorem tailTrace_743955 : CollatzResearch.WordTrace tailWord_743955 prefixEnd_743955 339561333613992894525439 := by
  unfold tailWord_743955
  simp only [CollatzResearch.WordTrace]
  refine ⟨27134268019785567243553319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18089512013190378162368879 27134268019785567243553319)
  ·
    refine ⟨40701402029678350865329979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27134268019785567243553319 40701402029678350865329979)
    ·
      refine ⟨61052103044517526297994969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40701402029678350865329979 61052103044517526297994969)
      ·
        refine ⟨45789077283388144723496227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61052103044517526297994969 45789077283388144723496227)
        ·
          refine ⟨68683615925082217085244341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45789077283388144723496227 68683615925082217085244341)
          ·
            refine ⟨6439088992976457851741657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68683615925082217085244341 6439088992976457851741657)
            ·
              refine ⟨4829316744732343388806243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6439088992976457851741657 4829316744732343388806243)
              ·
                refine ⟨7243975117098515083209365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4829316744732343388806243 7243975117098515083209365)
                ·
                  refine ⟨339561333613992894525439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7243975117098515083209365 339561333613992894525439)
                  ·
                    rfl

theorem cell20_743955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_743955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743955 prefixEnd_743955 := by exact prefixLift 743955
  have htrace : WordTrace (prefixWord ++ tailWord_743955) baseStart_743955 baseEnd_743955 := by
    simpa [prefixWord, tailWord_743955, baseEnd_743955] using wordTrace_append hprefix tailTrace_743955
  have hstable : (prefixWord ++ tailWord_743955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743955).length < 2 ^ (prefixWord ++ tailWord_743955).sum := by decide
  have hdescent : baseEnd_743955 < baseStart_743955 := by decide
  rcases family_descends (prefixWord ++ tailWord_743955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743975 : List Nat := [1, 1, 7, 2, 2, 7]
def baseStart_743975 : Nat := 118140960795 + 743975 * 2 ^ 59
def prefixEnd_743975 : Nat := 4983230072969 + 3 ^ 40 * 743975 * 2
def baseEnd_743975 : Nat := 12576683783665248661433

theorem tailTrace_743975 : CollatzResearch.WordTrace tailWord_743975 prefixEnd_743975 12576683783665248661433 := by
  unfold tailWord_743975
  simp only [CollatzResearch.WordTrace]
  refine ⟨27134997479713110659281379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18089998319808740439520919 27134997479713110659281379)
  ·
    refine ⟨40702496219569665988922069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27134997479713110659281379 40702496219569665988922069)
    ·
      refine ⟨953964755146164046615361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40702496219569665988922069 953964755146164046615361)
      ·
        refine ⟨715473566359623034961521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 953964755146164046615361 715473566359623034961521)
        ·
          refine ⟨536605174769717276221141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715473566359623034961521 536605174769717276221141)
          ·
            refine ⟨12576683783665248661433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 536605174769717276221141 12576683783665248661433)
            ·
              rfl

theorem cell20_743975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 7].length) (baseStart_743975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743975 prefixEnd_743975 := by exact prefixLift 743975
  have htrace : WordTrace (prefixWord ++ tailWord_743975) baseStart_743975 baseEnd_743975 := by
    simpa [prefixWord, tailWord_743975, baseEnd_743975] using wordTrace_append hprefix tailTrace_743975
  have hstable : (prefixWord ++ tailWord_743975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743975).length < 2 ^ (prefixWord ++ tailWord_743975).sum := by decide
  have hdescent : baseEnd_743975 < baseStart_743975 := by decide
  rcases family_descends (prefixWord ++ tailWord_743975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743986 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_743986 : Nat := 118140960795 + 743986 * 2 ^ 59
def prefixEnd_743986 : Nat := 4983230072969 + 3 ^ 40 * 743986 * 2
def baseEnd_743986 : Nat := 339575482858694564491979

theorem tailTrace_743986 : CollatzResearch.WordTrace tailWord_743986 prefixEnd_743986 339575482858694564491979 := by
  unfold tailWord_743986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6783849670668314884482953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18090265788448839691954541 6783849670668314884482953)
  ·
    refine ⟨5087887253001236163362215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6783849670668314884482953 5087887253001236163362215)
    ·
      refine ⟨7631830879501854245043323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5087887253001236163362215 7631830879501854245043323)
      ·
        refine ⟨11447746319252781367564985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7631830879501854245043323 11447746319252781367564985)
        ·
          refine ⟨8585809739439586025673739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11447746319252781367564985 8585809739439586025673739)
          ·
            refine ⟨12878714609159379038510609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8585809739439586025673739 12878714609159379038510609)
            ·
              refine ⟨9659035956869534278882957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12878714609159379038510609 9659035956869534278882957)
              ·
                refine ⟨3622138483826075354581109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9659035956869534278882957 3622138483826075354581109)
                ·
                  refine ⟨339575482858694564491979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3622138483826075354581109 339575482858694564491979)
                  ·
                    rfl

theorem cell20_743986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_743986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743986 prefixEnd_743986 := by exact prefixLift 743986
  have htrace : WordTrace (prefixWord ++ tailWord_743986) baseStart_743986 baseEnd_743986 := by
    simpa [prefixWord, tailWord_743986, baseEnd_743986] using wordTrace_append hprefix tailTrace_743986
  have hstable : (prefixWord ++ tailWord_743986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743986).length < 2 ^ (prefixWord ++ tailWord_743986).sum := by decide
  have hdescent : baseEnd_743986 < baseStart_743986 := by decide
  rcases family_descends (prefixWord ++ tailWord_743986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743989 : List Nat := [1, 3, 3, 1, 1, 2, 3, 4, 2]
def baseStart_743989 : Nat := 118140960795 + 743989 * 2 ^ 59
def prefixEnd_743989 : Nat := 4983230072969 + 3 ^ 40 * 743989 * 2
def baseEnd_743989 : Nat := 339576852140439887391967

theorem tailTrace_743989 : CollatzResearch.WordTrace tailWord_743989 prefixEnd_743989 339576852140439887391967 := by
  unfold tailWord_743989
  simp only [CollatzResearch.WordTrace]
  refine ⟨27135508101662391050291021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18090338734441594033527347 27135508101662391050291021)
  ·
    refine ⟨10175815538123396643859133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27135508101662391050291021 10175815538123396643859133)
    ·
      refine ⟨3815930826796273741447175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10175815538123396643859133 3815930826796273741447175)
      ·
        refine ⟨5723896240194410612170763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815930826796273741447175 5723896240194410612170763)
        ·
          refine ⟨8585844360291615918256145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5723896240194410612170763 8585844360291615918256145)
          ·
            refine ⟨6439383270218711938692109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8585844360291615918256145 6439383270218711938692109)
            ·
              refine ⟨2414768726332016977009541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6439383270218711938692109 2414768726332016977009541)
              ·
                refine ⟨452769136187253183189289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2414768726332016977009541 452769136187253183189289)
                ·
                  refine ⟨339576852140439887391967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452769136187253183189289 339576852140439887391967)
                  ·
                    rfl

theorem cell20_743989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_743989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743989 prefixEnd_743989 := by exact prefixLift 743989
  have htrace : WordTrace (prefixWord ++ tailWord_743989) baseStart_743989 baseEnd_743989 := by
    simpa [prefixWord, tailWord_743989, baseEnd_743989] using wordTrace_append hprefix tailTrace_743989
  have hstable : (prefixWord ++ tailWord_743989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743989).length < 2 ^ (prefixWord ++ tailWord_743989).sum := by decide
  have hdescent : baseEnd_743989 < baseStart_743989 := by decide
  rcases family_descends (prefixWord ++ tailWord_743989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743996 : List Nat := [2, 2, 2, 2, 3, 3, 1, 5]
def baseStart_743996 : Nat := 118140960795 + 743996 * 2 ^ 59
def prefixEnd_743996 : Nat := 4983230072969 + 3 ^ 40 * 743996 * 2
def baseEnd_743996 : Nat := 113193349043726324719535

theorem tailTrace_743996 : CollatzResearch.WordTrace tailWord_743996 prefixEnd_743996 113193349043726324719535 := by
  unfold tailWord_743996
  simp only [CollatzResearch.WordTrace]
  refine ⟨13567881706318515622897921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18090508941758020830530561 13567881706318515622897921)
  ·
    refine ⟨10175911279738886717173441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13567881706318515622897921 10175911279738886717173441)
    ·
      refine ⟨7631933459804165037880081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10175911279738886717173441 7631933459804165037880081)
      ·
        refine ⟨5723950094853123778410061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7631933459804165037880081 5723950094853123778410061)
        ·
          refine ⟨2146481285569921416903773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5723950094853123778410061 2146481285569921416903773)
          ·
            refine ⟨804930482088720531338915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2146481285569921416903773 804930482088720531338915)
            ·
              refine ⟨1207395723133080797008373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804930482088720531338915 1207395723133080797008373)
              ·
                refine ⟨113193349043726324719535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1207395723133080797008373 113193349043726324719535)
                ·
                  rfl

theorem cell20_743996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_743996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_743996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_743996 prefixEnd_743996 := by exact prefixLift 743996
  have htrace : WordTrace (prefixWord ++ tailWord_743996) baseStart_743996 baseEnd_743996 := by
    simpa [prefixWord, tailWord_743996, baseEnd_743996] using wordTrace_append hprefix tailTrace_743996
  have hstable : (prefixWord ++ tailWord_743996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743996).length < 2 ^ (prefixWord ++ tailWord_743996).sum := by decide
  have hdescent : baseEnd_743996 < baseStart_743996 := by decide
  rcases family_descends (prefixWord ++ tailWord_743996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744006 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_744006 : Nat := 118140960795 + 744006 * 2 ^ 59
def prefixEnd_744006 : Nat := 4983230072969 + 3 ^ 40 * 744006 * 2
def baseEnd_744006 : Nat := 339584611403663383825231

theorem tailTrace_744006 : CollatzResearch.WordTrace tailWord_744006 prefixEnd_744006 339584611403663383825231 := by
  unfold tailWord_744006
  simp only [CollatzResearch.WordTrace]
  refine ⟨848004004456275092301871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18090752095067201969106581 848004004456275092301871)
  ·
    refine ⟨1272006006684412638452807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 848004004456275092301871 1272006006684412638452807)
    ·
      refine ⟨1908009010026618957679211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1272006006684412638452807 1908009010026618957679211)
      ·
        refine ⟨2862013515039928436518817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1908009010026618957679211 2862013515039928436518817)
        ·
          refine ⟨2146510136279946327389113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2862013515039928436518817 2146510136279946327389113)
          ·
            refine ⟨1609882602209959745541835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2146510136279946327389113 1609882602209959745541835)
            ·
              refine ⟨2414823903314939618312753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609882602209959745541835 2414823903314939618312753)
              ·
                refine ⟨1811117927486204713734565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414823903314939618312753 1811117927486204713734565)
                ·
                  refine ⟨339584611403663383825231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1811117927486204713734565 339584611403663383825231)
                  ·
                    rfl

theorem cell20_744006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_744006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744006 prefixEnd_744006 := by exact prefixLift 744006
  have htrace : WordTrace (prefixWord ++ tailWord_744006) baseStart_744006 baseEnd_744006 := by
    simpa [prefixWord, tailWord_744006, baseEnd_744006] using wordTrace_append hprefix tailTrace_744006
  have hstable : (prefixWord ++ tailWord_744006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744006).length < 2 ^ (prefixWord ++ tailWord_744006).sum := by decide
  have hdescent : baseEnd_744006 < baseStart_744006 := by decide
  rcases family_descends (prefixWord ++ tailWord_744006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744010 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_744010 : Nat := 118140960795 + 744010 * 2 ^ 59
def prefixEnd_744010 : Nat := 4983230072969 + 3 ^ 40 * 744010 * 2
def baseEnd_744010 : Nat := 339586437112657147691881

theorem tailTrace_744010 : CollatzResearch.WordTrace tailWord_744010 prefixEnd_744010 339586437112657147691881 := by
  unfold tailWord_744010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6784068508646577909201371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18090849356390874424536989 6784068508646577909201371)
  ·
    refine ⟨10176102762969866863802057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6784068508646577909201371 10176102762969866863802057)
    ·
      refine ⟨7632077072227400147851543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10176102762969866863802057 7632077072227400147851543)
      ·
        refine ⟨11448115608341100221777315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7632077072227400147851543 11448115608341100221777315)
        ·
          refine ⟨17172173412511650332665973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11448115608341100221777315 17172173412511650332665973)
          ·
            refine ⟨1609891257422967218687435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17172173412511650332665973 1609891257422967218687435)
            ·
              refine ⟨2414836886134450828031153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609891257422967218687435 2414836886134450828031153)
              ·
                refine ⟨1811127664600838121023365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414836886134450828031153 1811127664600838121023365)
                ·
                  refine ⟨339586437112657147691881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1811127664600838121023365 339586437112657147691881)
                  ·
                    rfl

theorem cell20_744010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_744010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744010 prefixEnd_744010 := by exact prefixLift 744010
  have htrace : WordTrace (prefixWord ++ tailWord_744010) baseStart_744010 baseEnd_744010 := by
    simpa [prefixWord, tailWord_744010, baseEnd_744010] using wordTrace_append hprefix tailTrace_744010
  have hstable : (prefixWord ++ tailWord_744010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744010).length < 2 ^ (prefixWord ++ tailWord_744010).sum := by decide
  have hdescent : baseEnd_744010 < baseStart_744010 := by decide
  rcases family_descends (prefixWord ++ tailWord_744010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744013 : List Nat := [1, 6, 1, 1, 2, 2, 3, 4]
def baseStart_744013 : Nat := 118140960795 + 744013 * 2 ^ 59
def prefixEnd_744013 : Nat := 4983230072969 + 3 ^ 40 * 744013 * 2
def baseEnd_744013 : Nat := 113195935464800823530623

theorem tailTrace_744013 : CollatzResearch.WordTrace tailWord_744013 prefixEnd_744013 113195935464800823530623 := by
  unfold tailWord_744013
  simp only [CollatzResearch.WordTrace]
  refine ⟨27136383453575443149164693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18090922302383628766109795 27136383453575443149164693)
  ·
    refine ⟨1272017974386348897617095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27136383453575443149164693 1272017974386348897617095)
    ·
      refine ⟨1908026961579523346425643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1272017974386348897617095 1908026961579523346425643)
      ·
        refine ⟨2862040442369285019638465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1908026961579523346425643 2862040442369285019638465)
        ·
          refine ⟨2146530331776963764728849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2862040442369285019638465 2146530331776963764728849)
          ·
            refine ⟨1609897748832722823546637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2146530331776963764728849 1609897748832722823546637)
            ·
              refine ⟨603711655812271058829989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1609897748832722823546637 603711655812271058829989)
              ·
                refine ⟨113195935464800823530623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 603711655812271058829989 113195935464800823530623)
                ·
                  rfl

theorem cell20_744013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 4].length) (baseStart_744013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744013 prefixEnd_744013 := by exact prefixLift 744013
  have htrace : WordTrace (prefixWord ++ tailWord_744013) baseStart_744013 baseEnd_744013 := by
    simpa [prefixWord, tailWord_744013, baseEnd_744013] using wordTrace_append hprefix tailTrace_744013
  have hstable : (prefixWord ++ tailWord_744013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744013).length < 2 ^ (prefixWord ++ tailWord_744013).sum := by decide
  have hdescent : baseEnd_744013 < baseStart_744013 := by decide
  rcases family_descends (prefixWord ++ tailWord_744013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744030 : List Nat := [4, 4, 1, 2, 1, 1, 7]
def baseStart_744030 : Nat := 118140960795 + 744030 * 2 ^ 59
def prefixEnd_744030 : Nat := 4983230072969 + 3 ^ 40 * 744030 * 2
def baseEnd_744030 : Nat := 37732840628625107447237

theorem tailTrace_744030 : CollatzResearch.WordTrace tailWord_744030 prefixEnd_744030 37732840628625107447237 := by
  unfold tailWord_744030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392125436814231881566693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18091335663009236701689029 3392125436814231881566693)
  ·
    refine ⟨636023519402668477793755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3392125436814231881566693 636023519402668477793755)
    ·
      refine ⟨954035279104002716690633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636023519402668477793755 954035279104002716690633)
      ·
        refine ⟨715526459328002037517975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 954035279104002716690633 715526459328002037517975)
        ·
          refine ⟨1073289688992003056276963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715526459328002037517975 1073289688992003056276963)
          ·
            refine ⟨1609934533488004584415445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073289688992003056276963 1609934533488004584415445)
            ·
              refine ⟨37732840628625107447237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1609934533488004584415445 37732840628625107447237)
              ·
                rfl

theorem cell20_744030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 7].length) (baseStart_744030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744030 prefixEnd_744030 := by exact prefixLift 744030
  have htrace : WordTrace (prefixWord ++ tailWord_744030) baseStart_744030 baseEnd_744030 := by
    simpa [prefixWord, tailWord_744030, baseEnd_744030] using wordTrace_append hprefix tailTrace_744030
  have hstable : (prefixWord ++ tailWord_744030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744030).length < 2 ^ (prefixWord ++ tailWord_744030).sum := by decide
  have hdescent : baseEnd_744030 < baseStart_744030 := by decide
  rcases family_descends (prefixWord ++ tailWord_744030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744037 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 3]
def baseStart_744037 : Nat := 118140960795 + 744037 * 2 ^ 59
def prefixEnd_744037 : Nat := 4983230072969 + 3 ^ 40 * 744037 * 2
def baseEnd_744037 : Nat := 339598760648365053791771

theorem tailTrace_744037 : CollatzResearch.WordTrace tailWord_744037 prefixEnd_744037 339598760648365053791771 := by
  unfold tailWord_744037
  simp only [CollatzResearch.WordTrace]
  refine ⟨27137258805488495248038365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18091505870325663498692243 27137258805488495248038365)
  ·
    refine ⟨10176472052058185718014387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27137258805488495248038365 10176472052058185718014387)
    ·
      refine ⟨15264708078087278577021581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10176472052058185718014387 15264708078087278577021581)
      ·
        refine ⟨5724265529282729466383093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15264708078087278577021581 5724265529282729466383093)
        ·
          refine ⟨536649893370255887473415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5724265529282729466383093 536649893370255887473415)
          ·
            refine ⟨804974840055383831210123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536649893370255887473415 804974840055383831210123)
            ·
              refine ⟨1207462260083075746815185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804974840055383831210123 1207462260083075746815185)
              ·
                refine ⟨905596695062306810111389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207462260083075746815185 905596695062306810111389)
                ·
                  refine ⟨339598760648365053791771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905596695062306810111389 339598760648365053791771)
                  ·
                    rfl

theorem cell20_744037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_744037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744037 prefixEnd_744037 := by exact prefixLift 744037
  have htrace : WordTrace (prefixWord ++ tailWord_744037) baseStart_744037 baseEnd_744037 := by
    simpa [prefixWord, tailWord_744037, baseEnd_744037] using wordTrace_append hprefix tailTrace_744037
  have hstable : (prefixWord ++ tailWord_744037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744037).length < 2 ^ (prefixWord ++ tailWord_744037).sum := by decide
  have hdescent : baseEnd_744037 < baseStart_744037 := by decide
  rcases family_descends (prefixWord ++ tailWord_744037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744082 : List Nat := [3, 2, 3, 1, 2, 1, 3, 3, 2]
def baseStart_744082 : Nat := 118140960795 + 744082 * 2 ^ 59
def prefixEnd_744082 : Nat := 4983230072969 + 3 ^ 40 * 744082 * 2
def baseEnd_744082 : Nat := 339619299874544897291587

theorem tailTrace_744082 : CollatzResearch.WordTrace tailWord_744082 prefixEnd_744082 339619299874544897291587 := by
  unfold tailWord_744082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6784725022581366983356625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18092600060216978622284333 6784725022581366983356625)
  ·
    refine ⟨5088543766936025237517469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6784725022581366983356625 5088543766936025237517469)
    ·
      refine ⟨1908203912601009464069051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5088543766936025237517469 1908203912601009464069051)
      ·
        refine ⟨2862305868901514196103577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1908203912601009464069051 2862305868901514196103577)
        ·
          refine ⟨2146729401676135647077683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2862305868901514196103577 2146729401676135647077683)
          ·
            refine ⟨3220094102514203470616525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146729401676135647077683 3220094102514203470616525)
            ·
              refine ⟨1207535288442826301481197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3220094102514203470616525 1207535288442826301481197)
              ·
                refine ⟨452825733166059863055449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1207535288442826301481197 452825733166059863055449)
                ·
                  refine ⟨339619299874544897291587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452825733166059863055449 339619299874544897291587)
                  ·
                    rfl

theorem cell20_744082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_744082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744082 prefixEnd_744082 := by exact prefixLift 744082
  have htrace : WordTrace (prefixWord ++ tailWord_744082) baseStart_744082 baseEnd_744082 := by
    simpa [prefixWord, tailWord_744082, baseEnd_744082] using wordTrace_append hprefix tailTrace_744082
  have hstable : (prefixWord ++ tailWord_744082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744082).length < 2 ^ (prefixWord ++ tailWord_744082).sum := by decide
  have hdescent : baseEnd_744082 < baseStart_744082 := by decide
  rcases family_descends (prefixWord ++ tailWord_744082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744100 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_744100 : Nat := 118140960795 + 744100 * 2 ^ 59
def prefixEnd_744100 : Nat := 4983230072969 + 3 ^ 40 * 744100 * 2
def baseEnd_744100 : Nat := 339627515565016834691513

theorem tailTrace_744100 : CollatzResearch.WordTrace tailWord_744100 prefixEnd_744100 339627515565016834691513 := by
  unfold tailWord_744100
  simp only [CollatzResearch.WordTrace]
  refine ⟨13569778302130128503790877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18093037736173504671721169 13569778302130128503790877)
  ·
    refine ⟨5088666863298798188921579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13569778302130128503790877 5088666863298798188921579)
    ·
      refine ⟨7633000294948197283382369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5088666863298798188921579 7633000294948197283382369)
      ·
        refine ⟨5724750221211147962536777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7633000294948197283382369 5724750221211147962536777)
        ·
          refine ⟨4293562665908360971902583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5724750221211147962536777 4293562665908360971902583)
          ·
            refine ⟨6440343998862541457853875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293562665908360971902583 6440343998862541457853875)
            ·
              refine ⟨9660515998293812186780813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6440343998862541457853875 9660515998293812186780813)
              ·
                refine ⟨3622693499360179570042805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9660515998293812186780813 3622693499360179570042805)
                ·
                  refine ⟨339627515565016834691513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3622693499360179570042805 339627515565016834691513)
                  ·
                    rfl

theorem cell20_744100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_744100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744100 prefixEnd_744100 := by exact prefixLift 744100
  have htrace : WordTrace (prefixWord ++ tailWord_744100) baseStart_744100 baseEnd_744100 := by
    simpa [prefixWord, tailWord_744100, baseEnd_744100] using wordTrace_append hprefix tailTrace_744100
  have hstable : (prefixWord ++ tailWord_744100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744100).length < 2 ^ (prefixWord ++ tailWord_744100).sum := by decide
  have hdescent : baseEnd_744100 < baseStart_744100 := by decide
  rcases family_descends (prefixWord ++ tailWord_744100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744110 : List Nat := [4, 1, 4, 1, 1, 1, 1, 7]
def baseStart_744110 : Nat := 118140960795 + 744110 * 2 ^ 59
def prefixEnd_744110 : Nat := 4983230072969 + 3 ^ 40 * 744110 * 2
def baseEnd_744110 : Nat := 113210693279167081452713

theorem tailTrace_744110 : CollatzResearch.WordTrace tailWord_744110 prefixEnd_744110 113210693279167081452713 := by
  unfold tailWord_744110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392490166778003589430723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18093280889482685810297189 3392490166778003589430723)
  ·
    refine ⟨5088735250167005384146085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3392490166778003589430723 5088735250167005384146085)
    ·
      refine ⟨954137859406313509527391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5088735250167005384146085 954137859406313509527391)
      ·
        refine ⟨1431206789109470264291087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 954137859406313509527391 1431206789109470264291087)
        ·
          refine ⟨2146810183664205396436631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431206789109470264291087 2146810183664205396436631)
          ·
            refine ⟨3220215275496308094654947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146810183664205396436631 3220215275496308094654947)
            ·
              refine ⟨4830322913244462141982421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3220215275496308094654947 4830322913244462141982421)
              ·
                refine ⟨113210693279167081452713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4830322913244462141982421 113210693279167081452713)
                ·
                  rfl

theorem cell20_744110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_744110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744110 prefixEnd_744110 := by exact prefixLift 744110
  have htrace : WordTrace (prefixWord ++ tailWord_744110) baseStart_744110 baseEnd_744110 := by
    simpa [prefixWord, tailWord_744110, baseEnd_744110] using wordTrace_append hprefix tailTrace_744110
  have hstable : (prefixWord ++ tailWord_744110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744110).length < 2 ^ (prefixWord ++ tailWord_744110).sum := by decide
  have hdescent : baseEnd_744110 < baseStart_744110 := by decide
  rcases family_descends (prefixWord ++ tailWord_744110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744148 : List Nat := [2, 4, 1, 3, 3, 7]
def baseStart_744148 : Nat := 118140960795 + 744148 * 2 ^ 59
def prefixEnd_744148 : Nat := 4983230072969 + 3 ^ 40 * 744148 * 2
def baseEnd_744148 : Nat := 12579608298997851892271

theorem tailTrace_744148 : CollatzResearch.WordTrace tailWord_744148 prefixEnd_744148 12579608298997851892271 := by
  unfold tailWord_744148
  simp only [CollatzResearch.WordTrace]
  refine ⟨13570653654043180602664549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18094204872057574136886065 13570653654043180602664549)
  ·
    refine ⟨2544497560133096362999603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13570653654043180602664549 2544497560133096362999603)
    ·
      refine ⟨3816746340199644544499405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2544497560133096362999603 3816746340199644544499405)
      ·
        refine ⟨1431279877574866704187277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3816746340199644544499405 1431279877574866704187277)
        ·
          refine ⟨536729954090575014070229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1431279877574866704187277 536729954090575014070229)
          ·
            refine ⟨12579608298997851892271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 536729954090575014070229 12579608298997851892271)
            ·
              rfl

theorem cell20_744148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 7].length) (baseStart_744148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744148 prefixEnd_744148 := by exact prefixLift 744148
  have htrace : WordTrace (prefixWord ++ tailWord_744148) baseStart_744148 baseEnd_744148 := by
    simpa [prefixWord, tailWord_744148, baseEnd_744148] using wordTrace_append hprefix tailTrace_744148
  have hstable : (prefixWord ++ tailWord_744148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744148).length < 2 ^ (prefixWord ++ tailWord_744148).sum := by decide
  have hdescent : baseEnd_744148 < baseStart_744148 := by decide
  rcases family_descends (prefixWord ++ tailWord_744148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744152 : List Nat := [2, 1, 2, 2, 3, 10]
def baseStart_744152 : Nat := 118140960795 + 744152 * 2 ^ 59
def prefixEnd_744152 : Nat := 4983230072969 + 3 ^ 40 * 744152 * 2
def baseEnd_744152 : Nat := 12579675917849472776221

theorem tailTrace_744152 : CollatzResearch.WordTrace tailWord_744152 prefixEnd_744152 12579675917849472776221 := by
  unfold tailWord_744152
  simp only [CollatzResearch.WordTrace]
  refine ⟨13570726600035934944237355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18094302133381246592316473 13570726600035934944237355)
  ·
    refine ⟨20356089900053902416356033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13570726600035934944237355 20356089900053902416356033)
    ·
      refine ⟨15267067425040426812267025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20356089900053902416356033 15267067425040426812267025)
      ·
        refine ⟨11450300568780320109200269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15267067425040426812267025 11450300568780320109200269)
        ·
          refine ⟨4293862713292620040950101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11450300568780320109200269 4293862713292620040950101)
          ·
            refine ⟨12579675917849472776221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4293862713292620040950101 12579675917849472776221)
            ·
              rfl

theorem cell20_744152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 10].length) (baseStart_744152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744152 prefixEnd_744152 := by exact prefixLift 744152
  have htrace : WordTrace (prefixWord ++ tailWord_744152) baseStart_744152 baseEnd_744152 := by
    simpa [prefixWord, tailWord_744152, baseEnd_744152] using wordTrace_append hprefix tailTrace_744152
  have hstable : (prefixWord ++ tailWord_744152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744152).length < 2 ^ (prefixWord ++ tailWord_744152).sum := by decide
  have hdescent : baseEnd_744152 < baseStart_744152 := by decide
  rcases family_descends (prefixWord ++ tailWord_744152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744176 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 3]
def baseStart_744176 : Nat := 118140960795 + 744176 * 2 ^ 59
def prefixEnd_744176 : Nat := 4983230072969 + 3 ^ 40 * 744176 * 2
def baseEnd_744176 : Nat := 339662204035898348157869

theorem tailTrace_744176 : CollatzResearch.WordTrace tailWord_744176 prefixEnd_744176 339662204035898348157869 := by
  unfold tailWord_744176
  simp only [CollatzResearch.WordTrace]
  refine ⟨13571164275992460993674191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18094885701323281324898921 13571164275992460993674191)
  ·
    refine ⟨20356746413988691490511287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13571164275992460993674191 20356746413988691490511287)
    ·
      refine ⟨30535119620983037235766931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20356746413988691490511287 30535119620983037235766931)
      ·
        refine ⟨45802679431474555853650397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30535119620983037235766931 45802679431474555853650397)
        ·
          refine ⟨17176004786802958445118899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45802679431474555853650397 17176004786802958445118899)
          ·
            refine ⟨25764007180204437667678349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17176004786802958445118899 25764007180204437667678349)
            ·
              refine ⟨9661502692576664125379381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25764007180204437667678349 9661502692576664125379381)
              ·
                refine ⟨905765877429062261754317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9661502692576664125379381 905765877429062261754317)
                ·
                  refine ⟨339662204035898348157869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 905765877429062261754317 339662204035898348157869)
                  ·
                    rfl

theorem cell20_744176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_744176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744176 prefixEnd_744176 := by exact prefixLift 744176
  have htrace : WordTrace (prefixWord ++ tailWord_744176) baseStart_744176 baseEnd_744176 := by
    simpa [prefixWord, tailWord_744176, baseEnd_744176] using wordTrace_append hprefix tailTrace_744176
  have hstable : (prefixWord ++ tailWord_744176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744176).length < 2 ^ (prefixWord ++ tailWord_744176).sum := by decide
  have hdescent : baseEnd_744176 < baseStart_744176 := by decide
  rcases family_descends (prefixWord ++ tailWord_744176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744210 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_744210 : Nat := 118140960795 + 744210 * 2 ^ 59
def prefixEnd_744210 : Nat := 4983230072969 + 3 ^ 40 * 744210 * 2
def baseEnd_744210 : Nat := 339677722562345341024397

theorem tailTrace_744210 : CollatzResearch.WordTrace tailWord_744210 prefixEnd_744210 339677722562345341024397 := by
  unfold tailWord_744210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6785892158465436448521521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18095712422574497196057389 6785892158465436448521521)
  ·
    refine ⟨5089419118849077336391141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6785892158465436448521521 5089419118849077336391141)
    ·
      refine ⟨954266084784202000573339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5089419118849077336391141 954266084784202000573339)
      ·
        refine ⟨1431399127176303000860009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 954266084784202000573339 1431399127176303000860009)
        ·
          refine ⟨1073549345382227250645007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1431399127176303000860009 1073549345382227250645007)
          ·
            refine ⟨1610324018073340875967511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073549345382227250645007 1610324018073340875967511)
            ·
              refine ⟨2415486027110011313951267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610324018073340875967511 2415486027110011313951267)
              ·
                refine ⟨3623229040665016970926901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2415486027110011313951267 3623229040665016970926901)
                ·
                  refine ⟨339677722562345341024397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3623229040665016970926901 339677722562345341024397)
                  ·
                    rfl

theorem cell20_744210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_744210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744210 prefixEnd_744210 := by exact prefixLift 744210
  have htrace : WordTrace (prefixWord ++ tailWord_744210) baseStart_744210 baseEnd_744210 := by
    simpa [prefixWord, tailWord_744210, baseEnd_744210] using wordTrace_append hprefix tailTrace_744210
  have hstable : (prefixWord ++ tailWord_744210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744210).length < 2 ^ (prefixWord ++ tailWord_744210).sum := by decide
  have hdescent : baseEnd_744210 < baseStart_744210 := by decide
  rcases family_descends (prefixWord ++ tailWord_744210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744235 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 7]
def baseStart_744235 : Nat := 118140960795 + 744235 * 2 ^ 59
def prefixEnd_744235 : Nat := 4983230072969 + 3 ^ 40 * 744235 * 2
def baseEnd_744235 : Nat := 339689133243556365190961

theorem tailTrace_744235 : CollatzResearch.WordTrace tailWord_744235 prefixEnd_744235 339689133243556365190961 := by
  unfold tailWord_744235
  simp only [CollatzResearch.WordTrace]
  refine ⟨27144480458771175063746159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18096320305847450042497439 27144480458771175063746159)
  ·
    refine ⟨40716720688156762595619239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27144480458771175063746159 40716720688156762595619239)
    ·
      refine ⟨61075081032235143893428859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40716720688156762595619239 61075081032235143893428859)
      ·
        refine ⟨91612621548352715840143289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61075081032235143893428859 91612621548352715840143289)
        ·
          refine ⟨68709466161264536880107467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91612621548352715840143289 68709466161264536880107467)
          ·
            refine ⟨103064199241896805320161201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68709466161264536880107467 103064199241896805320161201)
            ·
              refine ⟨77298149431422603990120901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103064199241896805320161201 77298149431422603990120901)
              ·
                refine ⟨14493403018391738248147669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77298149431422603990120901 14493403018391738248147669)
                ·
                  refine ⟨339689133243556365190961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14493403018391738248147669 339689133243556365190961)
                  ·
                    rfl

theorem cell20_744235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_744235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744235 prefixEnd_744235 := by exact prefixLift 744235
  have htrace : WordTrace (prefixWord ++ tailWord_744235) baseStart_744235 baseEnd_744235 := by
    simpa [prefixWord, tailWord_744235, baseEnd_744235] using wordTrace_append hprefix tailTrace_744235
  have hstable : (prefixWord ++ tailWord_744235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744235).length < 2 ^ (prefixWord ++ tailWord_744235).sum := by decide
  have hdescent : baseEnd_744235 < baseStart_744235 := by decide
  rcases family_descends (prefixWord ++ tailWord_744235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744237 : List Nat := [1, 5, 3, 2, 2, 1, 2, 4]
def baseStart_744237 : Nat := 118140960795 + 744237 * 2 ^ 59
def prefixEnd_744237 : Nat := 4983230072969 + 3 ^ 40 * 744237 * 2
def baseEnd_744237 : Nat := 113230015366017749041429

theorem tailTrace_744237 : CollatzResearch.WordTrace tailWord_744237 prefixEnd_744237 113230015366017749041429 := by
  unfold tailWord_744237
  simp only [CollatzResearch.WordTrace]
  refine ⟨27144553404763929405318965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18096368936509286270212643 27144553404763929405318965)
  ·
    refine ⟨2544801881696618381748653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27144553404763929405318965 2544801881696618381748653)
    ·
      refine ⟨954300705636231893155745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2544801881696618381748653 954300705636231893155745)
      ·
        refine ⟨715725529227173919866809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 954300705636231893155745 715725529227173919866809)
        ·
          refine ⟨536794146920380439900107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715725529227173919866809 536794146920380439900107)
          ·
            refine ⟨805191220380570659850161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536794146920380439900107 805191220380570659850161)
            ·
              refine ⟨603893415285427994887621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805191220380570659850161 603893415285427994887621)
              ·
                refine ⟨113230015366017749041429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 603893415285427994887621 113230015366017749041429)
                ·
                  rfl

theorem cell20_744237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 4].length) (baseStart_744237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744237 prefixEnd_744237 := by exact prefixLift 744237
  have htrace : WordTrace (prefixWord ++ tailWord_744237) baseStart_744237 baseEnd_744237 := by
    simpa [prefixWord, tailWord_744237, baseEnd_744237] using wordTrace_append hprefix tailTrace_744237
  have hstable : (prefixWord ++ tailWord_744237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744237).length < 2 ^ (prefixWord ++ tailWord_744237).sum := by decide
  have hdescent : baseEnd_744237 < baseStart_744237 := by decide
  rcases family_descends (prefixWord ++ tailWord_744237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744245 : List Nat := [1, 3, 3, 1, 3, 2, 1, 6]
def baseStart_744245 : Nat := 118140960795 + 744245 * 2 ^ 59
def prefixEnd_744245 : Nat := 4983230072969 + 3 ^ 40 * 744245 * 2
def baseEnd_744245 : Nat := 113231232505346924952529

theorem tailTrace_744245 : CollatzResearch.WordTrace tailWord_744245 prefixEnd_744245 113231232505346924952529 := by
  unfold tailWord_744245
  simp only [CollatzResearch.WordTrace]
  refine ⟨27144845188734946771610189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18096563459156631181073459 27144845188734946771610189)
  ·
    refine ⟨10179316945775605039353821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27144845188734946771610189 10179316945775605039353821)
    ·
      refine ⟨3817243854665851889757683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10179316945775605039353821 3817243854665851889757683)
      ·
        refine ⟨5725865781998777834636525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3817243854665851889757683 5725865781998777834636525)
        ·
          refine ⟨2147199668249541687988697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5725865781998777834636525 2147199668249541687988697)
          ·
            refine ⟨1610399751187156265991523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2147199668249541687988697 1610399751187156265991523)
            ·
              refine ⟨2415599626780734398987285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610399751187156265991523 2415599626780734398987285)
              ·
                refine ⟨113231232505346924952529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2415599626780734398987285 113231232505346924952529)
                ·
                  rfl

theorem cell20_744245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_744245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744245 prefixEnd_744245 := by exact prefixLift 744245
  have htrace : WordTrace (prefixWord ++ tailWord_744245) baseStart_744245 baseEnd_744245 := by
    simpa [prefixWord, tailWord_744245, baseEnd_744245] using wordTrace_append hprefix tailTrace_744245
  have hstable : (prefixWord ++ tailWord_744245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744245).length < 2 ^ (prefixWord ++ tailWord_744245).sum := by decide
  have hdescent : baseEnd_744245 < baseStart_744245 := by decide
  rcases family_descends (prefixWord ++ tailWord_744245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744255 : List Nat := [1, 1, 2, 2, 5, 1, 3, 3, 2]
def baseStart_744255 : Nat := 118140960795 + 744255 * 2 ^ 59
def prefixEnd_744255 : Nat := 4983230072969 + 3 ^ 40 * 744255 * 2
def baseEnd_744255 : Nat := 339698261788525184524213

theorem tailTrace_744255 : CollatzResearch.WordTrace tailWord_744255 prefixEnd_744255 339698261788525184524213 := by
  unfold tailWord_744255
  simp only [CollatzResearch.WordTrace]
  refine ⟨27145209918698718479474219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18096806612465812319649479 27145209918698718479474219)
  ·
    refine ⟨40717814878048077719211329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27145209918698718479474219 40717814878048077719211329)
    ·
      refine ⟨30538361158536058289408497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40717814878048077719211329 30538361158536058289408497)
      ·
        refine ⟨22903770868902043717056373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30538361158536058289408497 22903770868902043717056373)
        ·
          refine ⟨2147228518959566598474035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22903770868902043717056373 2147228518959566598474035)
          ·
            refine ⟨3220842778439349897711053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147228518959566598474035 3220842778439349897711053)
            ·
              refine ⟨1207816041914756211641645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3220842778439349897711053 1207816041914756211641645)
              ·
                refine ⟨452931015718033579365617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1207816041914756211641645 452931015718033579365617)
                ·
                  refine ⟨339698261788525184524213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452931015718033579365617 339698261788525184524213)
                  ·
                    rfl

theorem cell20_744255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 2].length) (baseStart_744255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744255 prefixEnd_744255 := by exact prefixLift 744255
  have htrace : WordTrace (prefixWord ++ tailWord_744255) baseStart_744255 baseEnd_744255 := by
    simpa [prefixWord, tailWord_744255, baseEnd_744255] using wordTrace_append hprefix tailTrace_744255
  have hstable : (prefixWord ++ tailWord_744255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744255).length < 2 ^ (prefixWord ++ tailWord_744255).sum := by decide
  have hdescent : baseEnd_744255 < baseStart_744255 := by decide
  rcases family_descends (prefixWord ++ tailWord_744255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744304 : List Nat := [2, 1, 1, 1, 4, 1, 4, 6]
def baseStart_744304 : Nat := 118140960795 + 744304 * 2 ^ 59
def prefixEnd_744304 : Nat := 4983230072969 + 3 ^ 40 * 744304 * 2
def baseEnd_744304 : Nat := 113240208907899597296893

theorem tailTrace_744304 : CollatzResearch.WordTrace tailWord_744304 prefixEnd_744304 113240208907899597296893 := by
  unfold tailWord_744304
  simp only [CollatzResearch.WordTrace]
  refine ⟨13573498547760599924003983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18097998063680799898671977 13573498547760599924003983)
  ·
    refine ⟨20360247821640899886005975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13573498547760599924003983 20360247821640899886005975)
    ·
      refine ⟨30540371732461349829008963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20360247821640899886005975 30540371732461349829008963)
      ·
        refine ⟨45810557598692024743513445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30540371732461349829008963 45810557598692024743513445)
        ·
          refine ⟨8589479549754754639408771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45810557598692024743513445 8589479549754754639408771)
          ·
            refine ⟨12884219324632131959113157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8589479549754754639408771 12884219324632131959113157)
            ·
              refine ⟨2415791123368524742333717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12884219324632131959113157 2415791123368524742333717)
              ·
                refine ⟨113240208907899597296893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2415791123368524742333717 113240208907899597296893)
                ·
                  rfl

theorem cell20_744304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_744304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744304 prefixEnd_744304 := by exact prefixLift 744304
  have htrace : WordTrace (prefixWord ++ tailWord_744304) baseStart_744304 baseEnd_744304 := by
    simpa [prefixWord, tailWord_744304, baseEnd_744304] using wordTrace_append hprefix tailTrace_744304
  have hstable : (prefixWord ++ tailWord_744304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744304).length < 2 ^ (prefixWord ++ tailWord_744304).sum := by decide
  have hdescent : baseEnd_744304 < baseStart_744304 := by decide
  rcases family_descends (prefixWord ++ tailWord_744304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744311 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_744311 : Nat := 118140960795 + 744311 * 2 ^ 59
def prefixEnd_744311 : Nat := 4983230072969 + 3 ^ 40 * 744311 * 2
def baseEnd_744311 : Nat := 339723821714437878657317

theorem tailTrace_744311 : CollatzResearch.WordTrace tailWord_744311 prefixEnd_744311 339723821714437878657317 := by
  unfold tailWord_744311
  simp only [CollatzResearch.WordTrace]
  refine ⟨27147252406495840043512787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18098168270997226695675191 27147252406495840043512787)
  ·
    refine ⟨40720878609743760065269181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27147252406495840043512787 40720878609743760065269181)
    ·
      refine ⟨15270329478653910024475943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40720878609743760065269181 15270329478653910024475943)
      ·
        refine ⟨22905494217980865036713915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15270329478653910024475943 22905494217980865036713915)
        ·
          refine ⟨34358241326971297555070873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22905494217980865036713915 34358241326971297555070873)
          ·
            refine ⟨25768680995228473166303155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34358241326971297555070873 25768680995228473166303155)
            ·
              refine ⟨38653021492842709749454733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25768680995228473166303155 38653021492842709749454733)
              ·
                refine ⟨14494883059816016156045525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38653021492842709749454733 14494883059816016156045525)
                ·
                  refine ⟨339723821714437878657317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14494883059816016156045525 339723821714437878657317)
                  ·
                    rfl

theorem cell20_744311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_744311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744311 prefixEnd_744311 := by exact prefixLift 744311
  have htrace : WordTrace (prefixWord ++ tailWord_744311) baseStart_744311 baseEnd_744311 := by
    simpa [prefixWord, tailWord_744311, baseEnd_744311] using wordTrace_append hprefix tailTrace_744311
  have hstable : (prefixWord ++ tailWord_744311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744311).length < 2 ^ (prefixWord ++ tailWord_744311).sum := by decide
  have hdescent : baseEnd_744311 < baseStart_744311 := by decide
  rcases family_descends (prefixWord ++ tailWord_744311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744314 : List Nat := [3, 1, 1, 1, 1, 1, 3, 7, 2]
def baseStart_744314 : Nat := 118140960795 + 744314 * 2 ^ 59
def prefixEnd_744314 : Nat := 4983230072969 + 3 ^ 40 * 744314 * 2
def baseEnd_744314 : Nat := 339725190996183201557305

theorem tailTrace_744314 : CollatzResearch.WordTrace tailWord_744314 prefixEnd_744314 339725190996183201557305 := by
  unfold tailWord_744314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786840456371242888967999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18098241216989981037247997 6786840456371242888967999)
  ·
    refine ⟨10180260684556864333451999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6786840456371242888967999 10180260684556864333451999)
    ·
      refine ⟨15270391026835296500177999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10180260684556864333451999 15270391026835296500177999)
      ·
        refine ⟨22905586540252944750266999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15270391026835296500177999 22905586540252944750266999)
        ·
          refine ⟨34358379810379417125400499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22905586540252944750266999 34358379810379417125400499)
          ·
            refine ⟨51537569715569125688100749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34358379810379417125400499 51537569715569125688100749)
            ·
              refine ⟨19326588643338422133037781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51537569715569125688100749 19326588643338422133037781)
              ·
                refine ⟨452966921328244268743073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19326588643338422133037781 452966921328244268743073)
                ·
                  refine ⟨339725190996183201557305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452966921328244268743073 339725190996183201557305)
                  ·
                    rfl

theorem cell20_744314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_744314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744314 prefixEnd_744314 := by exact prefixLift 744314
  have htrace : WordTrace (prefixWord ++ tailWord_744314) baseStart_744314 baseEnd_744314 := by
    simpa [prefixWord, tailWord_744314, baseEnd_744314] using wordTrace_append hprefix tailTrace_744314
  have hstable : (prefixWord ++ tailWord_744314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744314).length < 2 ^ (prefixWord ++ tailWord_744314).sum := by decide
  have hdescent : baseEnd_744314 < baseStart_744314 := by decide
  rcases family_descends (prefixWord ++ tailWord_744314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744331 : List Nat := [1, 1, 1, 1, 4, 2, 6, 2, 2]
def baseStart_744331 : Nat := 118140960795 + 744331 * 2 ^ 59
def prefixEnd_744331 : Nat := 4983230072969 + 3 ^ 40 * 744331 * 2
def baseEnd_744331 : Nat := 339732950259406697990569

theorem tailTrace_744331 : CollatzResearch.WordTrace tailWord_744331 prefixEnd_744331 339732950259406697990569 := by
  unfold tailWord_744331
  simp only [CollatzResearch.WordTrace]
  refine ⟨27147981866423383459240847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18098654577615588972827231 27147981866423383459240847)
  ·
    refine ⟨40721972799635075188861271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27147981866423383459240847 40721972799635075188861271)
    ·
      refine ⟨61082959199452612783291907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40721972799635075188861271 61082959199452612783291907)
      ·
        refine ⟨91624438799178919174937861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61082959199452612783291907 91624438799178919174937861)
        ·
          refine ⟨17179582274846047345300849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91624438799178919174937861 17179582274846047345300849)
          ·
            refine ⟨12884686706134535508975637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17179582274846047345300849 12884686706134535508975637)
            ·
              refine ⟨603969689350056351983233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12884686706134535508975637 603969689350056351983233)
              ·
                refine ⟨452977267012542263987425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603969689350056351983233 452977267012542263987425)
                ·
                  refine ⟨339732950259406697990569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452977267012542263987425 339732950259406697990569)
                  ·
                    rfl

theorem cell20_744331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 2].length) (baseStart_744331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744331 prefixEnd_744331 := by exact prefixLift 744331
  have htrace : WordTrace (prefixWord ++ tailWord_744331) baseStart_744331 baseEnd_744331 := by
    simpa [prefixWord, tailWord_744331, baseEnd_744331] using wordTrace_append hprefix tailTrace_744331
  have hstable : (prefixWord ++ tailWord_744331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744331).length < 2 ^ (prefixWord ++ tailWord_744331).sum := by decide
  have hdescent : baseEnd_744331 < baseStart_744331 := by decide
  rcases family_descends (prefixWord ++ tailWord_744331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744365 : List Nat := [1, 5, 2, 3, 1, 1, 2, 3, 2]
def baseStart_744365 : Nat := 118140960795 + 744365 * 2 ^ 59
def prefixEnd_744365 : Nat := 4983230072969 + 3 ^ 40 * 744365 * 2
def baseEnd_744365 : Nat := 339748468785853690857097

theorem tailTrace_744365 : CollatzResearch.WordTrace tailWord_744365 prefixEnd_744365 339748468785853690857097 := by
  unfold tailWord_744365
  simp only [CollatzResearch.WordTrace]
  refine ⟨27149221948300207265978549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18099481298866804843985699 27149221948300207265978549)
  ·
    refine ⟨2545239557653144431185489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27149221948300207265978549 2545239557653144431185489)
    ·
      refine ⟨1908929668239858323389117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2545239557653144431185489 1908929668239858323389117)
      ·
        refine ⟨715848625589946871270919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1908929668239858323389117 715848625589946871270919)
        ·
          refine ⟨1073772938384920306906379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715848625589946871270919 1073772938384920306906379)
          ·
            refine ⟨1610659407577380460359569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073772938384920306906379 1610659407577380460359569)
            ·
              refine ⟨1207994555683035345269677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1610659407577380460359569 1207994555683035345269677)
              ·
                refine ⟨452997958381138254476129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1207994555683035345269677 452997958381138254476129)
                ·
                  refine ⟨339748468785853690857097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452997958381138254476129 339748468785853690857097)
                  ·
                    rfl

theorem cell20_744365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_744365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744365 prefixEnd_744365 := by exact prefixLift 744365
  have htrace : WordTrace (prefixWord ++ tailWord_744365) baseStart_744365 baseEnd_744365 := by
    simpa [prefixWord, tailWord_744365, baseEnd_744365] using wordTrace_append hprefix tailTrace_744365
  have hstable : (prefixWord ++ tailWord_744365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744365).length < 2 ^ (prefixWord ++ tailWord_744365).sum := by decide
  have hdescent : baseEnd_744365 < baseStart_744365 := by decide
  rcases family_descends (prefixWord ++ tailWord_744365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744373 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 6]
def baseStart_744373 : Nat := 118140960795 + 744373 * 2 ^ 59
def prefixEnd_744373 : Nat := 4983230072969 + 3 ^ 40 * 744373 * 2
def baseEnd_744373 : Nat := 339752120203841218590397

theorem tailTrace_744373 : CollatzResearch.WordTrace tailWord_744373 prefixEnd_744373 339752120203841218590397 := by
  unfold tailWord_744373
  simp only [CollatzResearch.WordTrace]
  refine ⟨27149513732271224632269773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18099675821514149754846515 27149513732271224632269773)
  ·
    refine ⟨10181067649601709237101165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27149513732271224632269773 10181067649601709237101165)
    ·
      refine ⟨3817900368600640963912937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10181067649601709237101165 3817900368600640963912937)
      ·
        refine ⟨2863425276450480722934703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3817900368600640963912937 2863425276450480722934703)
        ·
          refine ⟨4295137914675721084402055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2863425276450480722934703 4295137914675721084402055)
          ·
            refine ⟨6442706872013581626603083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4295137914675721084402055 6442706872013581626603083)
            ·
              refine ⟨9664060308020372439904625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442706872013581626603083 9664060308020372439904625)
              ·
                refine ⟨7248045231015279329928469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9664060308020372439904625 7248045231015279329928469)
                ·
                  refine ⟨339752120203841218590397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7248045231015279329928469 339752120203841218590397)
                  ·
                    rfl

theorem cell20_744373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_744373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744373 prefixEnd_744373 := by exact prefixLift 744373
  have htrace : WordTrace (prefixWord ++ tailWord_744373) baseStart_744373 baseEnd_744373 := by
    simpa [prefixWord, tailWord_744373, baseEnd_744373] using wordTrace_append hprefix tailTrace_744373
  have hstable : (prefixWord ++ tailWord_744373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744373).length < 2 ^ (prefixWord ++ tailWord_744373).sum := by decide
  have hdescent : baseEnd_744373 < baseStart_744373 := by decide
  rcases family_descends (prefixWord ++ tailWord_744373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744387 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_744387 : Nat := 118140960795 + 744387 * 2 ^ 59
def prefixEnd_744387 : Nat := 4983230072969 + 3 ^ 40 * 744387 * 2
def baseEnd_744387 : Nat := 339758510185319392123673

theorem tailTrace_744387 : CollatzResearch.WordTrace tailWord_744387 prefixEnd_744387 339758510185319392123673 := by
  unfold tailWord_744387
  simp only [CollatzResearch.WordTrace]
  refine ⟨27150024354220505023279415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18100016236147003348852943 27150024354220505023279415)
  ·
    refine ⟨40725036531330757534919123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27150024354220505023279415 40725036531330757534919123)
    ·
      refine ⟨61087554796996136302378685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40725036531330757534919123 61087554796996136302378685)
      ·
        refine ⟨22907833048873551113392007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61087554796996136302378685 22907833048873551113392007)
        ·
          refine ⟨34361749573310326670088011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22907833048873551113392007 34361749573310326670088011)
          ·
            refine ⟨51542624359965490005132017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34361749573310326670088011 51542624359965490005132017)
            ·
              refine ⟨38656968269974117503849013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51542624359965490005132017 38656968269974117503849013)
              ·
                refine ⟨3624090775310073515985845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38656968269974117503849013 3624090775310073515985845)
                ·
                  refine ⟨339758510185319392123673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3624090775310073515985845 339758510185319392123673)
                  ·
                    rfl

theorem cell20_744387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_744387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744387 prefixEnd_744387 := by exact prefixLift 744387
  have htrace : WordTrace (prefixWord ++ tailWord_744387) baseStart_744387 baseEnd_744387 := by
    simpa [prefixWord, tailWord_744387, baseEnd_744387] using wordTrace_append hprefix tailTrace_744387
  have hstable : (prefixWord ++ tailWord_744387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744387).length < 2 ^ (prefixWord ++ tailWord_744387).sum := by decide
  have hdescent : baseEnd_744387 < baseStart_744387 := by decide
  rcases family_descends (prefixWord ++ tailWord_744387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744456 : List Nat := [2, 1, 3, 2, 1, 3, 1, 7]
def baseStart_744456 : Nat := 118140960795 + 744456 * 2 ^ 59
def prefixEnd_744456 : Nat := 4983230072969 + 3 ^ 40 * 744456 * 2
def baseEnd_744456 : Nat := 113263334555153939607797

theorem tailTrace_744456 : CollatzResearch.WordTrace tailWord_744456 prefixEnd_744456 113263334555153939607797 := by
  unfold tailWord_744456
  simp only [CollatzResearch.WordTrace]
  refine ⟨13576270495485264903770611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18101693993980353205027481 13576270495485264903770611)
  ·
    refine ⟨20364405743227897355655917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13576270495485264903770611 20364405743227897355655917)
    ·
      refine ⟨7636652153710461508370969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20364405743227897355655917 7636652153710461508370969)
      ·
        refine ⟨5727489115282846131278227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7636652153710461508370969 5727489115282846131278227)
        ·
          refine ⟨8591233672924269196917341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5727489115282846131278227 8591233672924269196917341)
          ·
            refine ⟨3221712627346600948844003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8591233672924269196917341 3221712627346600948844003)
            ·
              refine ⟨4832568941019901423266005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221712627346600948844003 4832568941019901423266005)
              ·
                refine ⟨113263334555153939607797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4832568941019901423266005 113263334555153939607797)
                ·
                  rfl

theorem cell20_744456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_744456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744456 prefixEnd_744456 := by exact prefixLift 744456
  have htrace : WordTrace (prefixWord ++ tailWord_744456) baseStart_744456 baseEnd_744456 := by
    simpa [prefixWord, tailWord_744456, baseEnd_744456] using wordTrace_append hprefix tailTrace_744456
  have hstable : (prefixWord ++ tailWord_744456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744456).length < 2 ^ (prefixWord ++ tailWord_744456).sum := by decide
  have hdescent : baseEnd_744456 < baseStart_744456 := by decide
  rcases family_descends (prefixWord ++ tailWord_744456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744459 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 3]
def baseStart_744459 : Nat := 118140960795 + 744459 * 2 ^ 59
def prefixEnd_744459 : Nat := 4983230072969 + 3 ^ 40 * 744459 * 2
def baseEnd_744459 : Nat := 339791372947207141723379

theorem tailTrace_744459 : CollatzResearch.WordTrace tailWord_744459 prefixEnd_744459 339791372947207141723379 := by
  unfold tailWord_744459
  simp only [CollatzResearch.WordTrace]
  refine ⟨27152650409959661319900431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18101766939973107546600287 27152650409959661319900431)
  ·
    refine ⟨40728975614939491979850647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27152650409959661319900431 40728975614939491979850647)
    ·
      refine ⟨61093463422409237969775971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40728975614939491979850647 61093463422409237969775971)
      ·
        refine ⟨91640195133613856954663957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61093463422409237969775971 91640195133613856954663957)
        ·
          refine ⟨4295634146888149544749873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91640195133613856954663957 4295634146888149544749873)
          ·
            refine ⟨3221725610166112158562405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4295634146888149544749873 3221725610166112158562405)
            ·
              refine ⟨604073551906146029730451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3221725610166112158562405 604073551906146029730451)
              ·
                refine ⟨906110327859219044595677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604073551906146029730451 906110327859219044595677)
                ·
                  refine ⟨339791372947207141723379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906110327859219044595677 339791372947207141723379)
                  ·
                    rfl

theorem cell20_744459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 3].length) (baseStart_744459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744459 prefixEnd_744459 := by exact prefixLift 744459
  have htrace : WordTrace (prefixWord ++ tailWord_744459) baseStart_744459 baseEnd_744459 := by
    simpa [prefixWord, tailWord_744459, baseEnd_744459] using wordTrace_append hprefix tailTrace_744459
  have hstable : (prefixWord ++ tailWord_744459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744459).length < 2 ^ (prefixWord ++ tailWord_744459).sum := by decide
  have hdescent : baseEnd_744459 < baseStart_744459 := by decide
  rcases family_descends (prefixWord ++ tailWord_744459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744500 : List Nat := [2, 5, 1, 2, 1, 2, 1, 4, 2]
def baseStart_744500 : Nat := 118140960795 + 744500 * 2 ^ 59
def prefixEnd_744500 : Nat := 4983230072969 + 3 ^ 40 * 744500 * 2
def baseEnd_744500 : Nat := 339810086464393221356545

theorem tailTrace_744500 : CollatzResearch.WordTrace tailWord_744500 prefixEnd_744500 339810086464393221356545 := by
  unfold tailWord_744500
  simp only [CollatzResearch.WordTrace]
  refine ⟨13577072901405562661071477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18102763868540750214761969 13577072901405562661071477)
  ·
    refine ⟨1272850584506771499475451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13577072901405562661071477 1272850584506771499475451)
    ·
      refine ⟨1909275876760157249213177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1272850584506771499475451 1909275876760157249213177)
      ·
        refine ⟨1431956907570117936909883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1909275876760157249213177 1431956907570117936909883)
        ·
          refine ⟨2147935361355176905364825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431956907570117936909883 2147935361355176905364825)
          ·
            refine ⟨1610951521016382679023619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2147935361355176905364825 1610951521016382679023619)
            ·
              refine ⟨2416427281524574018535429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610951521016382679023619 2416427281524574018535429)
              ·
                refine ⟨453080115285857628475393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2416427281524574018535429 453080115285857628475393)
                ·
                  refine ⟨339810086464393221356545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453080115285857628475393 339810086464393221356545)
                  ·
                    rfl

theorem cell20_744500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_744500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744500 prefixEnd_744500 := by exact prefixLift 744500
  have htrace : WordTrace (prefixWord ++ tailWord_744500) baseStart_744500 baseEnd_744500 := by
    simpa [prefixWord, tailWord_744500, baseEnd_744500] using wordTrace_append hprefix tailTrace_744500
  have hstable : (prefixWord ++ tailWord_744500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744500).length < 2 ^ (prefixWord ++ tailWord_744500).sum := by decide
  have hdescent : baseEnd_744500 < baseStart_744500 := by decide
  rcases family_descends (prefixWord ++ tailWord_744500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744532 : List Nat := [2, 4, 1, 1, 1, 1, 2, 8]
def baseStart_744532 : Nat := 118140960795 + 744532 * 2 ^ 59
def prefixEnd_744532 : Nat := 4983230072969 + 3 ^ 40 * 744532 * 2
def baseEnd_744532 : Nat := 113274897378781110763249

theorem tailTrace_744532 : CollatzResearch.WordTrace tailWord_744532 prefixEnd_744532 113274897378781110763249 := by
  unfold tailWord_744532
  simp only [CollatzResearch.WordTrace]
  refine ⟨13577656469347597393653925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18103541959130129858205233 13577656469347597393653925)
  ·
    refine ⟨2545810588002674511310111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13577656469347597393653925 2545810588002674511310111)
    ·
      refine ⟨3818715882004011766965167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2545810588002674511310111 3818715882004011766965167)
      ·
        refine ⟨5728073823006017650447751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3818715882004011766965167 5728073823006017650447751)
        ·
          refine ⟨8592110734509026475671627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5728073823006017650447751 8592110734509026475671627)
          ·
            refine ⟨12888166101763539713507441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8592110734509026475671627 12888166101763539713507441)
            ·
              refine ⟨9666124576322654785130581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12888166101763539713507441 9666124576322654785130581)
              ·
                refine ⟨113274897378781110763249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9666124576322654785130581 113274897378781110763249)
                ·
                  rfl

theorem cell20_744532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_744532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744532 prefixEnd_744532 := by exact prefixLift 744532
  have htrace : WordTrace (prefixWord ++ tailWord_744532) baseStart_744532 baseEnd_744532 := by
    simpa [prefixWord, tailWord_744532, baseEnd_744532] using wordTrace_append hprefix tailTrace_744532
  have hstable : (prefixWord ++ tailWord_744532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744532).length < 2 ^ (prefixWord ++ tailWord_744532).sum := by decide
  have hdescent : baseEnd_744532 < baseStart_744532 := by decide
  rcases family_descends (prefixWord ++ tailWord_744532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744573 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 3]
def baseStart_744573 : Nat := 118140960795 + 744573 * 2 ^ 59
def prefixEnd_744573 : Nat := 4983230072969 + 3 ^ 40 * 744573 * 2
def baseEnd_744573 : Nat := 339843405653529411922913

theorem tailTrace_744573 : CollatzResearch.WordTrace tailWord_744573 prefixEnd_744573 339843405653529411922913 := by
  unfold tailWord_744573
  simp only [CollatzResearch.WordTrace]
  refine ⟨27156808331546658789550373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18104538887697772526366915 27156808331546658789550373)
  ·
    refine ⟨5091901562164998523040695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27156808331546658789550373 5091901562164998523040695)
    ·
      refine ⟨7637852343247497784561043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5091901562164998523040695 7637852343247497784561043)
      ·
        refine ⟨11456778514871246676841565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7637852343247497784561043 11456778514871246676841565)
        ·
          refine ⟨4296291943076717503815587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11456778514871246676841565 4296291943076717503815587)
          ·
            refine ⟨6444437914615076255723381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4296291943076717503815587 6444437914615076255723381)
            ·
              refine ⟨604166054495163398974067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6444437914615076255723381 604166054495163398974067)
              ·
                refine ⟨906249081742745098461101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604166054495163398974067 906249081742745098461101)
                ·
                  refine ⟨339843405653529411922913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906249081742745098461101 339843405653529411922913)
                  ·
                    rfl

theorem cell20_744573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_744573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744573 prefixEnd_744573 := by exact prefixLift 744573
  have htrace : WordTrace (prefixWord ++ tailWord_744573) baseStart_744573 baseEnd_744573 := by
    simpa [prefixWord, tailWord_744573, baseEnd_744573] using wordTrace_append hprefix tailTrace_744573
  have hstable : (prefixWord ++ tailWord_744573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744573).length < 2 ^ (prefixWord ++ tailWord_744573).sum := by decide
  have hdescent : baseEnd_744573 < baseStart_744573 := by decide
  rcases family_descends (prefixWord ++ tailWord_744573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744594 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_744594 : Nat := 118140960795 + 744594 * 2 ^ 59
def prefixEnd_744594 : Nat := 4983230072969 + 3 ^ 40 * 744594 * 2
def baseEnd_744594 : Nat := 339852990625746672222827

theorem tailTrace_744594 : CollatzResearch.WordTrace tailWord_744594 prefixEnd_744594 339852990625746672222827 := by
  unfold tailWord_744594
  simp only [CollatzResearch.WordTrace]
  refine ⟨6789393566117644844016209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18105049509647052917376557 6789393566117644844016209)
  ·
    refine ⟨5092045174588233633012157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6789393566117644844016209 5092045174588233633012157)
    ·
      refine ⟨1909516940470587612379559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5092045174588233633012157 1909516940470587612379559)
      ·
        refine ⟨2864275410705881418569339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1909516940470587612379559 2864275410705881418569339)
        ·
          refine ⟨4296413116058822127854009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2864275410705881418569339 4296413116058822127854009)
          ·
            refine ⟨3222309837044116595890507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4296413116058822127854009 3222309837044116595890507)
            ·
              refine ⟨4833464755566174893835761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3222309837044116595890507 4833464755566174893835761)
              ·
                refine ⟨3625098566674631170376821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4833464755566174893835761 3625098566674631170376821)
                ·
                  refine ⟨339852990625746672222827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3625098566674631170376821 339852990625746672222827)
                  ·
                    rfl

theorem cell20_744594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_744594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744594 prefixEnd_744594 := by exact prefixLift 744594
  have htrace : WordTrace (prefixWord ++ tailWord_744594) baseStart_744594 baseEnd_744594 := by
    simpa [prefixWord, tailWord_744594, baseEnd_744594] using wordTrace_append hprefix tailTrace_744594
  have hstable : (prefixWord ++ tailWord_744594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744594).length < 2 ^ (prefixWord ++ tailWord_744594).sum := by decide
  have hdescent : baseEnd_744594 < baseStart_744594 := by decide
  rcases family_descends (prefixWord ++ tailWord_744594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744625 : List Nat := [1, 2, 2, 5, 1, 2, 2, 5]
def baseStart_744625 : Nat := 118140960795 + 744625 * 2 ^ 59
def prefixEnd_744625 : Nat := 4983230072969 + 3 ^ 40 * 744625 * 2
def baseEnd_744625 : Nat := 113289046623482780729789

theorem tailTrace_744625 : CollatzResearch.WordTrace tailWord_744625 prefixEnd_744625 113289046623482780729789 := by
  unfold tailWord_744625
  simp only [CollatzResearch.WordTrace]
  refine ⟨27158704927358271670443329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18105803284905514446962219 27158704927358271670443329)
  ·
    refine ⟨20369028695518703752832497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27158704927358271670443329 20369028695518703752832497)
    ·
      refine ⟨15276771521639027814624373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20369028695518703752832497 15276771521639027814624373)
      ·
        refine ⟨1432197330153658857621035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15276771521639027814624373 1432197330153658857621035)
        ·
          refine ⟨2148295995230488286431553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432197330153658857621035 2148295995230488286431553)
          ·
            refine ⟨1611221996422866214823665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2148295995230488286431553 1611221996422866214823665)
            ·
              refine ⟨1208416497317149661117749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1611221996422866214823665 1208416497317149661117749)
              ·
                refine ⟨113289046623482780729789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1208416497317149661117749 113289046623482780729789)
                ·
                  rfl

theorem cell20_744625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_744625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744625 prefixEnd_744625 := by exact prefixLift 744625
  have htrace : WordTrace (prefixWord ++ tailWord_744625) baseStart_744625 baseEnd_744625 := by
    simpa [prefixWord, tailWord_744625, baseEnd_744625] using wordTrace_append hprefix tailTrace_744625
  have hstable : (prefixWord ++ tailWord_744625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744625).length < 2 ^ (prefixWord ++ tailWord_744625).sum := by decide
  have hdescent : baseEnd_744625 < baseStart_744625 := by decide
  rcases family_descends (prefixWord ++ tailWord_744625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744669 : List Nat := [1, 4, 3, 2, 2, 2, 2, 2, 2]
def baseStart_744669 : Nat := 118140960795 + 744669 * 2 ^ 59
def prefixEnd_744669 : Nat := 4983230072969 + 3 ^ 40 * 744669 * 2
def baseEnd_744669 : Nat := 339887222669379744722521

theorem tailTrace_744669 : CollatzResearch.WordTrace tailWord_744669 prefixEnd_744669 339887222669379744722521 := by
  unfold tailWord_744669
  simp only [CollatzResearch.WordTrace]
  refine ⟨27160309739198867185045061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18106873159465911456696707 27160309739198867185045061)
  ·
    refine ⟨5092558076099787597195949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27160309739198867185045061 5092558076099787597195949)
    ·
      refine ⟨1909709278537420348948481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5092558076099787597195949 1909709278537420348948481)
      ·
        refine ⟨1432281958903065261711361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1909709278537420348948481 1432281958903065261711361)
        ·
          refine ⟨1074211469177298946283521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1432281958903065261711361 1074211469177298946283521)
          ·
            refine ⟨805658601882974209712641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1074211469177298946283521 805658601882974209712641)
            ·
              refine ⟨604243951412230657284481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805658601882974209712641 604243951412230657284481)
              ·
                refine ⟨453182963559172992963361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604243951412230657284481 453182963559172992963361)
                ·
                  refine ⟨339887222669379744722521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453182963559172992963361 339887222669379744722521)
                  ·
                    rfl

theorem cell20_744669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_744669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744669 prefixEnd_744669 := by exact prefixLift 744669
  have htrace : WordTrace (prefixWord ++ tailWord_744669) baseStart_744669 baseEnd_744669 := by
    simpa [prefixWord, tailWord_744669, baseEnd_744669] using wordTrace_append hprefix tailTrace_744669
  have hstable : (prefixWord ++ tailWord_744669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744669).length < 2 ^ (prefixWord ++ tailWord_744669).sum := by decide
  have hdescent : baseEnd_744669 < baseStart_744669 := by decide
  rcases family_descends (prefixWord ++ tailWord_744669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744673 : List Nat := [1, 2, 3, 1, 3, 2, 4, 2, 2]
def baseStart_744673 : Nat := 118140960795 + 744673 * 2 ^ 59
def prefixEnd_744673 : Nat := 4983230072969 + 3 ^ 40 * 744673 * 2
def baseEnd_744673 : Nat := 339889048378373508589171

theorem tailTrace_744673 : CollatzResearch.WordTrace tailWord_744673 prefixEnd_744673 339889048378373508589171 := by
  unfold tailWord_744673
  simp only [CollatzResearch.WordTrace]
  refine ⟨27160455631184375868190673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18106970420789583912127115 27160455631184375868190673)
  ·
    refine ⟨20370341723388281901143005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27160455631184375868190673 20370341723388281901143005)
    ·
      refine ⟨7638878146270605712928627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20370341723388281901143005 7638878146270605712928627)
      ·
        refine ⟨11458317219405908569392941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7638878146270605712928627 11458317219405908569392941)
        ·
          refine ⟨4296868957277215713522353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11458317219405908569392941 4296868957277215713522353)
          ·
            refine ⟨3222651717957911785141765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4296868957277215713522353 3222651717957911785141765)
            ·
              refine ⟨604247197117108459714081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3222651717957911785141765 604247197117108459714081)
              ·
                refine ⟨453185397837831344785561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604247197117108459714081 453185397837831344785561)
                ·
                  refine ⟨339889048378373508589171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453185397837831344785561 339889048378373508589171)
                  ·
                    rfl

theorem cell20_744673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 2].length) (baseStart_744673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744673 prefixEnd_744673 := by exact prefixLift 744673
  have htrace : WordTrace (prefixWord ++ tailWord_744673) baseStart_744673 baseEnd_744673 := by
    simpa [prefixWord, tailWord_744673, baseEnd_744673] using wordTrace_append hprefix tailTrace_744673
  have hstable : (prefixWord ++ tailWord_744673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744673).length < 2 ^ (prefixWord ++ tailWord_744673).sum := by decide
  have hdescent : baseEnd_744673 < baseStart_744673 := by decide
  rcases family_descends (prefixWord ++ tailWord_744673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744684 : List Nat := [2, 2, 1, 1, 2, 4, 3, 5]
def baseStart_744684 : Nat := 118140960795 + 744684 * 2 ^ 59
def prefixEnd_744684 : Nat := 4983230072969 + 3 ^ 40 * 744684 * 2
def baseEnd_744684 : Nat := 113298023026035453074153

theorem tailTrace_744684 : CollatzResearch.WordTrace tailWord_744684 prefixEnd_744684 113298023026035453074153 := by
  unfold tailWord_744684
  simp only [CollatzResearch.WordTrace]
  refine ⟨13580428417072262373420553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18107237889429683164560737 13580428417072262373420553)
  ·
    refine ⟨10185321312804196780065415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13580428417072262373420553 10185321312804196780065415)
    ·
      refine ⟨15277981969206295170098123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10185321312804196780065415 15277981969206295170098123)
      ·
        refine ⟨22916972953809442755147185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15277981969206295170098123 22916972953809442755147185)
        ·
          refine ⟨17187729715357082066360389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22916972953809442755147185 17187729715357082066360389)
          ·
            refine ⟨3222699321629452887442573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17187729715357082066360389 3222699321629452887442573)
            ·
              refine ⟨1208512245611044832790965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3222699321629452887442573 1208512245611044832790965)
              ·
                refine ⟨113298023026035453074153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1208512245611044832790965 113298023026035453074153)
                ·
                  rfl

theorem cell20_744684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_744684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744684 prefixEnd_744684 := by exact prefixLift 744684
  have htrace : WordTrace (prefixWord ++ tailWord_744684) baseStart_744684 baseEnd_744684 := by
    simpa [prefixWord, tailWord_744684, baseEnd_744684] using wordTrace_append hprefix tailTrace_744684
  have hstable : (prefixWord ++ tailWord_744684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744684).length < 2 ^ (prefixWord ++ tailWord_744684).sum := by decide
  have hdescent : baseEnd_744684 < baseStart_744684 := by decide
  rcases family_descends (prefixWord ++ tailWord_744684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744732 : List Nat := [2, 2, 3, 1, 1, 1, 4, 4, 2]
def baseStart_744732 : Nat := 118140960795 + 744732 * 2 ^ 59
def prefixEnd_744732 : Nat := 4983230072969 + 3 ^ 40 * 744732 * 2
def baseEnd_744732 : Nat := 339915977586031525622263

theorem tailTrace_744732 : CollatzResearch.WordTrace tailWord_744732 prefixEnd_744732 339915977586031525622263 := by
  unfold tailWord_744732
  simp only [CollatzResearch.WordTrace]
  refine ⟨13581303768985314472294225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18108405025313752629725633 13581303768985314472294225)
  ·
    refine ⟨10185977826738985854220669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13581303768985314472294225 10185977826738985854220669)
    ·
      refine ⟨3819741685027119695332751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10185977826738985854220669 3819741685027119695332751)
      ·
        refine ⟨5729612527540679542999127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3819741685027119695332751 5729612527540679542999127)
        ·
          refine ⟨8594418791311019314498691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5729612527540679542999127 8594418791311019314498691)
          ·
            refine ⟨12891628186966528971748037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8594418791311019314498691 12891628186966528971748037)
            ·
              refine ⟨2417180285056224182202757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12891628186966528971748037 2417180285056224182202757)
              ·
                refine ⟨453221303448042034163017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2417180285056224182202757 453221303448042034163017)
                ·
                  refine ⟨339915977586031525622263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453221303448042034163017 339915977586031525622263)
                  ·
                    rfl

theorem cell20_744732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_744732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744732 prefixEnd_744732 := by exact prefixLift 744732
  have htrace : WordTrace (prefixWord ++ tailWord_744732) baseStart_744732 baseEnd_744732 := by
    simpa [prefixWord, tailWord_744732, baseEnd_744732] using wordTrace_append hprefix tailTrace_744732
  have hstable : (prefixWord ++ tailWord_744732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744732).length < 2 ^ (prefixWord ++ tailWord_744732).sum := by decide
  have hdescent : baseEnd_744732 < baseStart_744732 := by decide
  rcases family_descends (prefixWord ++ tailWord_744732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744753 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 4]
def baseStart_744753 : Nat := 118140960795 + 744753 * 2 ^ 59
def prefixEnd_744753 : Nat := 4983230072969 + 3 ^ 40 * 744753 * 2
def baseEnd_744753 : Nat := 339925562558248785922177

theorem tailTrace_744753 : CollatzResearch.WordTrace tailWord_744753 prefixEnd_744753 339925562558248785922177 := by
  unfold tailWord_744753
  simp only [CollatzResearch.WordTrace]
  refine ⟨27163373470894549531102913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18108915647263033020735275 27163373470894549531102913)
  ·
    refine ⟨20372530103170912148327185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27163373470894549531102913 20372530103170912148327185)
    ·
      refine ⟨15279397577378184111245389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20372530103170912148327185 15279397577378184111245389)
      ·
        refine ⟨5729774091516819041717021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15279397577378184111245389 5729774091516819041717021)
        ·
          refine ⟨2148665284318807140643883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5729774091516819041717021 2148665284318807140643883)
          ·
            refine ⟨3222997926478210710965825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148665284318807140643883 3222997926478210710965825)
            ·
              refine ⟨2417248444858658033224369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3222997926478210710965825 2417248444858658033224369)
              ·
                refine ⟨1812936333643993524918277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2417248444858658033224369 1812936333643993524918277)
                ·
                  refine ⟨339925562558248785922177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1812936333643993524918277 339925562558248785922177)
                  ·
                    rfl

theorem cell20_744753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_744753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744753 prefixEnd_744753 := by exact prefixLift 744753
  have htrace : WordTrace (prefixWord ++ tailWord_744753) baseStart_744753 baseEnd_744753 := by
    simpa [prefixWord, tailWord_744753, baseEnd_744753] using wordTrace_append hprefix tailTrace_744753
  have hstable : (prefixWord ++ tailWord_744753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744753).length < 2 ^ (prefixWord ++ tailWord_744753).sum := by decide
  have hdescent : baseEnd_744753 < baseStart_744753 := by decide
  rcases family_descends (prefixWord ++ tailWord_744753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744767 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 5]
def baseStart_744767 : Nat := 118140960795 + 744767 * 2 ^ 59
def prefixEnd_744767 : Nat := 4983230072969 + 3 ^ 40 * 744767 * 2
def baseEnd_744767 : Nat := 339931952539726959455453

theorem tailTrace_744767 : CollatzResearch.WordTrace tailWord_744767 prefixEnd_744767 339931952539726959455453 := by
  unfold tailWord_744767
  simp only [CollatzResearch.WordTrace]
  refine ⟨27163884092843829922112555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18109256061895886614741703 27163884092843829922112555)
  ·
    refine ⟨40745826139265744883168833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27163884092843829922112555 40745826139265744883168833)
    ·
      refine ⟨30559369604449308662376625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40745826139265744883168833 30559369604449308662376625)
      ·
        refine ⟨22919527203336981496782469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30559369604449308662376625 22919527203336981496782469)
        ·
          refine ⟨4297411350625684030646713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22919527203336981496782469 4297411350625684030646713)
          ·
            refine ⟨3223058512969263022985035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4297411350625684030646713 3223058512969263022985035)
            ·
              refine ⟨4834587769453894534477553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3223058512969263022985035 4834587769453894534477553)
              ·
                refine ⟨3625940827090420900858165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4834587769453894534477553 3625940827090420900858165)
                ·
                  refine ⟨339931952539726959455453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3625940827090420900858165 339931952539726959455453)
                  ·
                    rfl

theorem cell20_744767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_744767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744767 prefixEnd_744767 := by exact prefixLift 744767
  have htrace : WordTrace (prefixWord ++ tailWord_744767) baseStart_744767 baseEnd_744767 := by
    simpa [prefixWord, tailWord_744767, baseEnd_744767] using wordTrace_append hprefix tailTrace_744767
  have hstable : (prefixWord ++ tailWord_744767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744767).length < 2 ^ (prefixWord ++ tailWord_744767).sum := by decide
  have hdescent : baseEnd_744767 < baseStart_744767 := by decide
  rcases family_descends (prefixWord ++ tailWord_744767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744790 : List Nat := [5, 2, 3, 1, 1, 1, 2, 5]
def baseStart_744790 : Nat := 118140960795 + 744790 * 2 ^ 59
def prefixEnd_744790 : Nat := 4983230072969 + 3 ^ 40 * 744790 * 2
def baseEnd_744790 : Nat := 113314150122147033896231

theorem tailTrace_744790 : CollatzResearch.WordTrace tailWord_744790 prefixEnd_744790 113314150122147033896231 := by
  unfold tailWord_744790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1697795185735031553137489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18109815314507003233466549 1697795185735031553137489)
  ·
    refine ⟨1273346389301273664853117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1697795185735031553137489 1273346389301273664853117)
    ·
      refine ⟨477504895987977624319919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1273346389301273664853117 477504895987977624319919)
      ·
        refine ⟨716257343981966436479879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477504895987977624319919 716257343981966436479879)
        ·
          refine ⟨1074386015972949654719819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716257343981966436479879 1074386015972949654719819)
          ·
            refine ⟨1611579023959424482079729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074386015972949654719819 1611579023959424482079729)
            ·
              refine ⟨1208684267969568361559797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1611579023959424482079729 1208684267969568361559797)
              ·
                refine ⟨113314150122147033896231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1208684267969568361559797 113314150122147033896231)
                ·
                  rfl

theorem cell20_744790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_744790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744790 prefixEnd_744790 := by exact prefixLift 744790
  have htrace : WordTrace (prefixWord ++ tailWord_744790) baseStart_744790 baseEnd_744790 := by
    simpa [prefixWord, tailWord_744790, baseEnd_744790] using wordTrace_append hprefix tailTrace_744790
  have hstable : (prefixWord ++ tailWord_744790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744790).length < 2 ^ (prefixWord ++ tailWord_744790).sum := by decide
  have hdescent : baseEnd_744790 < baseStart_744790 := by decide
  rcases family_descends (prefixWord ++ tailWord_744790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744791 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 4]
def baseStart_744791 : Nat := 118140960795 + 744791 * 2 ^ 59
def prefixEnd_744791 : Nat := 4983230072969 + 3 ^ 40 * 744791 * 2
def baseEnd_744791 : Nat := 339942906793689542655355

theorem tailTrace_744791 : CollatzResearch.WordTrace tailWord_744791 prefixEnd_744791 339942906793689542655355 := by
  unfold tailWord_744791
  simp only [CollatzResearch.WordTrace]
  refine ⟨27164759444756882020986227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18109839629837921347324151 27164759444756882020986227)
  ·
    refine ⟨40747139167135323031479341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27164759444756882020986227 40747139167135323031479341)
    ·
      refine ⟨15280177187675746136804753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40747139167135323031479341 15280177187675746136804753)
      ·
        refine ⟨11460132890756809602603565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15280177187675746136804753 11460132890756809602603565)
        ·
          refine ⟨4297549834033803600976337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11460132890756809602603565 4297549834033803600976337)
          ·
            refine ⟨3223162375525352700732253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4297549834033803600976337 3223162375525352700732253)
            ·
              refine ⟨1208685890822007262774595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3223162375525352700732253 1208685890822007262774595)
              ·
                refine ⟨1813028836233010894161893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1208685890822007262774595 1813028836233010894161893)
                ·
                  refine ⟨339942906793689542655355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1813028836233010894161893 339942906793689542655355)
                  ·
                    rfl

theorem cell20_744791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_744791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744791 prefixEnd_744791 := by exact prefixLift 744791
  have htrace : WordTrace (prefixWord ++ tailWord_744791) baseStart_744791 baseEnd_744791 := by
    simpa [prefixWord, tailWord_744791, baseEnd_744791] using wordTrace_append hprefix tailTrace_744791
  have hstable : (prefixWord ++ tailWord_744791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744791).length < 2 ^ (prefixWord ++ tailWord_744791).sum := by decide
  have hdescent : baseEnd_744791 < baseStart_744791 := by decide
  rcases family_descends (prefixWord ++ tailWord_744791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744797 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 3]
def baseStart_744797 : Nat := 118140960795 + 744797 * 2 ^ 59
def prefixEnd_744797 : Nat := 4983230072969 + 3 ^ 40 * 744797 * 2
def baseEnd_744797 : Nat := 339945645357180188455331

theorem tailTrace_744797 : CollatzResearch.WordTrace tailWord_744797 prefixEnd_744797 339945645357180188455331 := by
  unfold tailWord_744797
  simp only [CollatzResearch.WordTrace]
  refine ⟨27164978282735145045704645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18109985521823430030469763 27164978282735145045704645)
  ·
    refine ⟨5093433428012839696069621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27164978282735145045704645 5093433428012839696069621)
    ·
      refine ⟨477509383876203721506527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5093433428012839696069621 477509383876203721506527)
      ·
        refine ⟨716264075814305582259791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477509383876203721506527 716264075814305582259791)
        ·
          refine ⟨1074396113721458373389687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716264075814305582259791 1074396113721458373389687)
          ·
            refine ⟨1611594170582187560084531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074396113721458373389687 1611594170582187560084531)
            ·
              refine ⟨2417391255873281340126797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611594170582187560084531 2417391255873281340126797)
              ·
                refine ⟨906521720952480502547549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2417391255873281340126797 906521720952480502547549)
                ·
                  refine ⟨339945645357180188455331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906521720952480502547549 339945645357180188455331)
                  ·
                    rfl

theorem cell20_744797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_744797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744797 prefixEnd_744797 := by exact prefixLift 744797
  have htrace : WordTrace (prefixWord ++ tailWord_744797) baseStart_744797 baseEnd_744797 := by
    simpa [prefixWord, tailWord_744797, baseEnd_744797] using wordTrace_append hprefix tailTrace_744797
  have hstable : (prefixWord ++ tailWord_744797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744797).length < 2 ^ (prefixWord ++ tailWord_744797).sum := by decide
  have hdescent : baseEnd_744797 < baseStart_744797 := by decide
  rcases family_descends (prefixWord ++ tailWord_744797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744881 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 5]
def baseStart_744881 : Nat := 118140960795 + 744881 * 2 ^ 59
def prefixEnd_744881 : Nat := 4983230072969 + 3 ^ 40 * 744881 * 2
def baseEnd_744881 : Nat := 339983985246049229654987

theorem tailTrace_744881 : CollatzResearch.WordTrace tailWord_744881 prefixEnd_744881 339983985246049229654987 := by
  unfold tailWord_744881
  simp only [CollatzResearch.WordTrace]
  refine ⟨27168042014430827391762497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18112028009620551594508331 27168042014430827391762497)
  ·
    refine ⟨20376031510823120543821873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27168042014430827391762497 20376031510823120543821873)
    ·
      refine ⟨15282023633117340407866405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20376031510823120543821873 15282023633117340407866405)
      ·
        refine ⟨2865379431209501326474951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15282023633117340407866405 2865379431209501326474951)
        ·
          refine ⟨4298069146814251989712427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865379431209501326474951 4298069146814251989712427)
          ·
            refine ⟨6447103720221377984568641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298069146814251989712427 6447103720221377984568641)
            ·
              refine ⟨4835327790166033488426481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6447103720221377984568641 4835327790166033488426481)
              ·
                refine ⟨3626495842624525116319861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4835327790166033488426481 3626495842624525116319861)
                ·
                  refine ⟨339983985246049229654987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3626495842624525116319861 339983985246049229654987)
                  ·
                    rfl

theorem cell20_744881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_744881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744881 prefixEnd_744881 := by exact prefixLift 744881
  have htrace : WordTrace (prefixWord ++ tailWord_744881) baseStart_744881 baseEnd_744881 := by
    simpa [prefixWord, tailWord_744881, baseEnd_744881] using wordTrace_append hprefix tailTrace_744881
  have hstable : (prefixWord ++ tailWord_744881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744881).length < 2 ^ (prefixWord ++ tailWord_744881).sum := by decide
  have hdescent : baseEnd_744881 < baseStart_744881 := by decide
  rcases family_descends (prefixWord ++ tailWord_744881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744919 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 3]
def baseStart_744919 : Nat := 118140960795 + 744919 * 2 ^ 59
def prefixEnd_744919 : Nat := 4983230072969 + 3 ^ 40 * 744919 * 2
def baseEnd_744919 : Nat := 340001329481489986388165

theorem tailTrace_744919 : CollatzResearch.WordTrace tailWord_744919 prefixEnd_744919 340001329481489986388165 := by
  unfold tailWord_744919
  simp only [CollatzResearch.WordTrace]
  refine ⟨27169427988293159881645811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18112951992195439921097207 27169427988293159881645811)
  ·
    refine ⟨40754141982439739822468717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27169427988293159881645811 40754141982439739822468717)
    ·
      refine ⟨15282803243414902433425769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40754141982439739822468717 15282803243414902433425769)
      ·
        refine ⟨11462102432561176825069327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15282803243414902433425769 11462102432561176825069327)
        ·
          refine ⟨17193153648841765237603991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11462102432561176825069327 17193153648841765237603991)
          ·
            refine ⟨25789730473262647856405987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17193153648841765237603991 25789730473262647856405987)
            ·
              refine ⟨38684595709893971784608981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25789730473262647856405987 38684595709893971784608981)
              ·
                refine ⟨906670211950639963701773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38684595709893971784608981 906670211950639963701773)
                ·
                  refine ⟨340001329481489986388165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906670211950639963701773 340001329481489986388165)
                  ·
                    rfl

theorem cell20_744919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 3].length) (baseStart_744919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744919 prefixEnd_744919 := by exact prefixLift 744919
  have htrace : WordTrace (prefixWord ++ tailWord_744919) baseStart_744919 baseEnd_744919 := by
    simpa [prefixWord, tailWord_744919, baseEnd_744919] using wordTrace_append hprefix tailTrace_744919
  have hstable : (prefixWord ++ tailWord_744919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744919).length < 2 ^ (prefixWord ++ tailWord_744919).sum := by decide
  have hdescent : baseEnd_744919 < baseStart_744919 := by decide
  rcases family_descends (prefixWord ++ tailWord_744919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744929 : List Nat := [1, 2, 3, 1, 2, 5, 2, 4]
def baseStart_744929 : Nat := 118140960795 + 744929 * 2 ^ 59
def prefixEnd_744929 : Nat := 4983230072969 + 3 ^ 40 * 744929 * 2
def baseEnd_744929 : Nat := 113335297917991465351597

theorem tailTrace_744929 : CollatzResearch.WordTrace tailWord_744929 prefixEnd_744929 113335297917991465351597 := by
  unfold tailWord_744929
  simp only [CollatzResearch.WordTrace]
  refine ⟨27169792718256931589509841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18113195145504621059673227 27169792718256931589509841)
  ·
    refine ⟨20377344538692698692132381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27169792718256931589509841 20377344538692698692132381)
    ·
      refine ⟨7641504202009762009549643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20377344538692698692132381 7641504202009762009549643)
      ·
        refine ⟨11462256303014643014324465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7641504202009762009549643 11462256303014643014324465)
        ·
          refine ⟨8596692227260982260743349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11462256303014643014324465 8596692227260982260743349)
          ·
            refine ⟨805939896305717086944689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8596692227260982260743349 805939896305717086944689)
            ·
              refine ⟨604454922229287815208517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805939896305717086944689 604454922229287815208517)
              ·
                refine ⟨113335297917991465351597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 604454922229287815208517 113335297917991465351597)
                ·
                  rfl

theorem cell20_744929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 4].length) (baseStart_744929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744929 prefixEnd_744929 := by exact prefixLift 744929
  have htrace : WordTrace (prefixWord ++ tailWord_744929) baseStart_744929 baseEnd_744929 := by
    simpa [prefixWord, tailWord_744929, baseEnd_744929] using wordTrace_append hprefix tailTrace_744929
  have hstable : (prefixWord ++ tailWord_744929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744929).length < 2 ^ (prefixWord ++ tailWord_744929).sum := by decide
  have hdescent : baseEnd_744929 < baseStart_744929 := by decide
  rcases family_descends (prefixWord ++ tailWord_744929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744950 : List Nat := [5, 1, 1, 1, 2, 2, 8]
def baseStart_744950 : Nat := 118140960795 + 744950 * 2 ^ 59
def prefixEnd_744950 : Nat := 4983230072969 + 3 ^ 40 * 744950 * 2
def baseEnd_744950 : Nat := 37779497636243517372745

theorem tailTrace_744950 : CollatzResearch.WordTrace tailWord_744950 prefixEnd_744950 37779497636243517372745 := by
  unfold tailWord_744950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698159915698803261001519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18113705767453901450682869 1698159915698803261001519)
  ·
    refine ⟨2547239873548204891502279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1698159915698803261001519 2547239873548204891502279)
    ·
      refine ⟨3820859810322307337253419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2547239873548204891502279 3820859810322307337253419)
      ·
        refine ⟨5731289715483461005880129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3820859810322307337253419 5731289715483461005880129)
        ·
          refine ⟨4298467286612595754410097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5731289715483461005880129 4298467286612595754410097)
          ·
            refine ⟨3223850464959446815807573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4298467286612595754410097 3223850464959446815807573)
            ·
              refine ⟨37779497636243517372745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3223850464959446815807573 37779497636243517372745)
              ·
                rfl

theorem cell20_744950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 8].length) (baseStart_744950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744950 prefixEnd_744950 := by exact prefixLift 744950
  have htrace : WordTrace (prefixWord ++ tailWord_744950) baseStart_744950 baseEnd_744950 := by
    simpa [prefixWord, tailWord_744950, baseEnd_744950] using wordTrace_append hprefix tailTrace_744950
  have hstable : (prefixWord ++ tailWord_744950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744950).length < 2 ^ (prefixWord ++ tailWord_744950).sum := by decide
  have hdescent : baseEnd_744950 < baseStart_744950 := by decide
  rcases family_descends (prefixWord ++ tailWord_744950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744957 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 5]
def baseStart_744957 : Nat := 118140960795 + 744957 * 2 ^ 59
def prefixEnd_744957 : Nat := 4983230072969 + 3 ^ 40 * 744957 * 2
def baseEnd_744957 : Nat := 340018673716930743121343

theorem tailTrace_744957 : CollatzResearch.WordTrace tailWord_744957 prefixEnd_744957 340018673716930743121343 := by
  unfold tailWord_744957
  simp only [CollatzResearch.WordTrace]
  refine ⟨27170813962155492371529125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18113875974770328247686083 27170813962155492371529125)
  ·
    refine ⟨5094527617904154819661711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27170813962155492371529125 5094527617904154819661711)
    ·
      refine ⟨7641791426856232229492567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5094527617904154819661711 7641791426856232229492567)
      ·
        refine ⟨11462687140284348344238851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7641791426856232229492567 11462687140284348344238851)
        ·
          refine ⟨17194030710426522516358277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11462687140284348344238851 17194030710426522516358277)
          ·
            refine ⟨3223880758204972971817177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17194030710426522516358277 3223880758204972971817177)
            ·
              refine ⟨2417910568653729728862883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3223880758204972971817177 2417910568653729728862883)
              ·
                refine ⟨3626865852980594593294325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417910568653729728862883 3626865852980594593294325)
                ·
                  refine ⟨340018673716930743121343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3626865852980594593294325 340018673716930743121343)
                  ·
                    rfl

theorem cell20_744957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_744957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_744957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_744957 prefixEnd_744957 := by exact prefixLift 744957
  have htrace : WordTrace (prefixWord ++ tailWord_744957) baseStart_744957 baseEnd_744957 := by
    simpa [prefixWord, tailWord_744957, baseEnd_744957] using wordTrace_append hprefix tailTrace_744957
  have hstable : (prefixWord ++ tailWord_744957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744957).length < 2 ^ (prefixWord ++ tailWord_744957).sum := by decide
  have hdescent : baseEnd_744957 < baseStart_744957 := by decide
  rcases family_descends (prefixWord ++ tailWord_744957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745015 : List Nat := [1, 1, 3, 1, 2, 6, 2, 2, 2]
def baseStart_745015 : Nat := 118140960795 + 745015 * 2 ^ 59
def prefixEnd_745015 : Nat := 4983230072969 + 3 ^ 40 * 745015 * 2
def baseEnd_745015 : Nat := 340045146497340319187773

theorem tailTrace_745015 : CollatzResearch.WordTrace tailWord_745015 prefixEnd_745015 340045146497340319187773 := by
  unfold tailWord_745015
  simp only [CollatzResearch.WordTrace]
  refine ⟨27172929395945368277140499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18115286263963578851426999 27172929395945368277140499)
  ·
    refine ⟨40759394093918052415710749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27172929395945368277140499 40759394093918052415710749)
    ·
      refine ⟨15284772785219269655891531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40759394093918052415710749 15284772785219269655891531)
      ·
        refine ⟨22927159177828904483837297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15284772785219269655891531 22927159177828904483837297)
        ·
          refine ⟨17195369383371678362877973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22927159177828904483837297 17195369383371678362877973)
          ·
            refine ⟨806032939845547423259905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17195369383371678362877973 806032939845547423259905)
            ·
              refine ⟨604524704884160567444929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806032939845547423259905 604524704884160567444929)
              ·
                refine ⟨453393528663120425583697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604524704884160567444929 453393528663120425583697)
                ·
                  refine ⟨340045146497340319187773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453393528663120425583697 340045146497340319187773)
                  ·
                    rfl

theorem cell20_745015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 2].length) (baseStart_745015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745015 prefixEnd_745015 := by exact prefixLift 745015
  have htrace : WordTrace (prefixWord ++ tailWord_745015) baseStart_745015 baseEnd_745015 := by
    simpa [prefixWord, tailWord_745015, baseEnd_745015] using wordTrace_append hprefix tailTrace_745015
  have hstable : (prefixWord ++ tailWord_745015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745015).length < 2 ^ (prefixWord ++ tailWord_745015).sum := by decide
  have hdescent : baseEnd_745015 < baseStart_745015 := by decide
  rcases family_descends (prefixWord ++ tailWord_745015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745040 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_745040 : Nat := 118140960795 + 745040 * 2 ^ 59
def prefixEnd_745040 : Nat := 4983230072969 + 3 ^ 40 * 745040 * 2
def baseEnd_745040 : Nat := 340056557178551343354337

theorem tailTrace_745040 : CollatzResearch.WordTrace tailWord_745040 prefixEnd_745040 340056557178551343354337 := by
  unfold tailWord_745040
  simp only [CollatzResearch.WordTrace]
  refine ⟨13586920610427398773400287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18115894147236531697867049 13586920610427398773400287)
  ·
    refine ⟨20380380915641098160100431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13586920610427398773400287 20380380915641098160100431)
    ·
      refine ⟨30570571373461647240150647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20380380915641098160100431 30570571373461647240150647)
      ·
        refine ⟨45855857060192470860225971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30570571373461647240150647 45855857060192470860225971)
        ·
          refine ⟨68783785590288706290338957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45855857060192470860225971 68783785590288706290338957)
          ·
            refine ⟨25793919596358264858877109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68783785590288706290338957 25793919596358264858877109)
            ·
              refine ⟨2418179962158587330519729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25793919596358264858877109 2418179962158587330519729)
              ·
                refine ⟨1813634971618940497889797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2418179962158587330519729 1813634971618940497889797)
                ·
                  refine ⟨340056557178551343354337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1813634971618940497889797 340056557178551343354337)
                  ·
                    rfl

theorem cell20_745040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_745040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745040 prefixEnd_745040 := by exact prefixLift 745040
  have htrace : WordTrace (prefixWord ++ tailWord_745040) baseStart_745040 baseEnd_745040 := by
    simpa [prefixWord, tailWord_745040, baseEnd_745040] using wordTrace_append hprefix tailTrace_745040
  have hstable : (prefixWord ++ tailWord_745040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745040).length < 2 ^ (prefixWord ++ tailWord_745040).sum := by decide
  have hdescent : baseEnd_745040 < baseStart_745040 := by decide
  rcases family_descends (prefixWord ++ tailWord_745040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745064 : List Nat := [2, 1, 4, 3, 1, 2, 7]
def baseStart_745064 : Nat := 118140960795 + 745064 * 2 ^ 59
def prefixEnd_745064 : Nat := 4983230072969 + 3 ^ 40 * 745064 * 2
def baseEnd_745064 : Nat := 37785279048057102950471

theorem tailTrace_745064 : CollatzResearch.WordTrace tailWord_745064 prefixEnd_745064 37785279048057102950471 := by
  unfold tailWord_745064
  simp only [CollatzResearch.WordTrace]
  refine ⟨13587358286383924822837123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18116477715178566430449497 13587358286383924822837123)
  ·
    refine ⟨20381037429575887234255685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13587358286383924822837123 20381037429575887234255685)
    ·
      refine ⟨3821444518045478856422941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20381037429575887234255685 3821444518045478856422941)
      ·
        refine ⟨1433041694267054571158603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3821444518045478856422941 1433041694267054571158603)
        ·
          refine ⟨2149562541400581856737905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433041694267054571158603 2149562541400581856737905)
          ·
            refine ⟨1612171906050436392553429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2149562541400581856737905 1612171906050436392553429)
            ·
              refine ⟨37785279048057102950471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1612171906050436392553429 37785279048057102950471)
              ·
                rfl

theorem cell20_745064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 7].length) (baseStart_745064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745064 prefixEnd_745064 := by exact prefixLift 745064
  have htrace : WordTrace (prefixWord ++ tailWord_745064) baseStart_745064 baseEnd_745064 := by
    simpa [prefixWord, tailWord_745064, baseEnd_745064] using wordTrace_append hprefix tailTrace_745064
  have hstable : (prefixWord ++ tailWord_745064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745064).length < 2 ^ (prefixWord ++ tailWord_745064).sum := by decide
  have hdescent : baseEnd_745064 < baseStart_745064 := by decide
  rcases family_descends (prefixWord ++ tailWord_745064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745074 : List Nat := [3, 2, 1, 2, 3, 1, 2, 4, 2]
def baseStart_745074 : Nat := 118140960795 + 745074 * 2 ^ 59
def prefixEnd_745074 : Nat := 4983230072969 + 3 ^ 40 * 745074 * 2
def baseEnd_745074 : Nat := 340072075704998336220865

theorem tailTrace_745074 : CollatzResearch.WordTrace tailWord_745074 prefixEnd_745074 340072075704998336220865 := by
  unfold tailWord_745074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793770325682905338384569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18116720868487747569025517 6793770325682905338384569)
  ·
    refine ⟨5095327744262179003788427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6793770325682905338384569 5095327744262179003788427)
    ·
      refine ⟨7642991616393268505682641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5095327744262179003788427 7642991616393268505682641)
      ·
        refine ⟨5732243712294951379261981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7642991616393268505682641 5732243712294951379261981)
        ·
          refine ⟨2149591392110606767223243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5732243712294951379261981 2149591392110606767223243)
          ·
            refine ⟨3224387088165910150834865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149591392110606767223243 3224387088165910150834865)
            ·
              refine ⟨2418290316124432613126149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3224387088165910150834865 2418290316124432613126149)
              ·
                refine ⟨453429434273331114961153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2418290316124432613126149 453429434273331114961153)
                ·
                  refine ⟨340072075704998336220865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453429434273331114961153 340072075704998336220865)
                  ·
                    rfl

theorem cell20_745074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_745074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745074 prefixEnd_745074 := by exact prefixLift 745074
  have htrace : WordTrace (prefixWord ++ tailWord_745074) baseStart_745074 baseEnd_745074 := by
    simpa [prefixWord, tailWord_745074, baseEnd_745074] using wordTrace_append hprefix tailTrace_745074
  have hstable : (prefixWord ++ tailWord_745074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745074).length < 2 ^ (prefixWord ++ tailWord_745074).sum := by decide
  have hdescent : baseEnd_745074 < baseStart_745074 := by decide
  rcases family_descends (prefixWord ++ tailWord_745074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745088 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 3]
def baseStart_745088 : Nat := 118140960795 + 745088 * 2 ^ 59
def prefixEnd_745088 : Nat := 4983230072969 + 3 ^ 40 * 745088 * 2
def baseEnd_745088 : Nat := 340078465686476509754141

theorem tailTrace_745088 : CollatzResearch.WordTrace tailWord_745088 prefixEnd_745088 340078465686476509754141 := by
  unfold tailWord_745088
  simp only [CollatzResearch.WordTrace]
  refine ⟨13587795962340450872273959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18117061283120601163031945 13587795962340450872273959)
  ·
    refine ⟨20381693943510676308410939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13587795962340450872273959 20381693943510676308410939)
    ·
      refine ⟨30572540915266014462616409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20381693943510676308410939 30572540915266014462616409)
      ·
        refine ⟨22929405686449510846962307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30572540915266014462616409 22929405686449510846962307)
        ·
          refine ⟨34394108529674266270443461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22929405686449510846962307 34394108529674266270443461)
          ·
            refine ⟨6448895349313924925708149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34394108529674266270443461 6448895349313924925708149)
            ·
              refine ⟨604583938998180461785139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6448895349313924925708149 604583938998180461785139)
              ·
                refine ⟨906875908497270692677709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604583938998180461785139 906875908497270692677709)
                ·
                  refine ⟨340078465686476509754141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906875908497270692677709 340078465686476509754141)
                  ·
                    rfl

theorem cell20_745088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_745088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745088 prefixEnd_745088 := by exact prefixLift 745088
  have htrace : WordTrace (prefixWord ++ tailWord_745088) baseStart_745088 baseEnd_745088 := by
    simpa [prefixWord, tailWord_745088, baseEnd_745088] using wordTrace_append hprefix tailTrace_745088
  have hstable : (prefixWord ++ tailWord_745088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745088).length < 2 ^ (prefixWord ++ tailWord_745088).sum := by decide
  have hdescent : baseEnd_745088 < baseStart_745088 := by decide
  rcases family_descends (prefixWord ++ tailWord_745088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745102 : List Nat := [4, 1, 1, 3, 1, 3, 1, 6]
def baseStart_745102 : Nat := 118140960795 + 745102 * 2 ^ 59
def prefixEnd_745102 : Nat := 4983230072969 + 3 ^ 40 * 745102 * 2
def baseEnd_745102 : Nat := 113361618555984894429139

theorem tailTrace_745102 : CollatzResearch.WordTrace tailWord_745102 prefixEnd_745102 113361618555984894429139 := by
  unfold tailWord_745102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3397012818328772766944695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18117401697753454757038373 3397012818328772766944695)
  ·
    refine ⟨5095519227493159150417043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3397012818328772766944695 5095519227493159150417043)
    ·
      refine ⟨7643278841239738725625565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5095519227493159150417043 7643278841239738725625565)
      ·
        refine ⟨2866229565464902022109587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7643278841239738725625565 2866229565464902022109587)
        ·
          refine ⟨4299344348197353033164381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866229565464902022109587 4299344348197353033164381)
          ·
            refine ⟨1612254130574007387436643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4299344348197353033164381 1612254130574007387436643)
            ·
              refine ⟨2418381195861011081154965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612254130574007387436643 2418381195861011081154965)
              ·
                refine ⟨113361618555984894429139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2418381195861011081154965 113361618555984894429139)
                ·
                  rfl

theorem cell20_745102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_745102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745102 prefixEnd_745102 := by exact prefixLift 745102
  have htrace : WordTrace (prefixWord ++ tailWord_745102) baseStart_745102 baseEnd_745102 := by
    simpa [prefixWord, tailWord_745102, baseEnd_745102] using wordTrace_append hprefix tailTrace_745102
  have hstable : (prefixWord ++ tailWord_745102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745102).length < 2 ^ (prefixWord ++ tailWord_745102).sum := by decide
  have hdescent : baseEnd_745102 < baseStart_745102 := by decide
  rcases family_descends (prefixWord ++ tailWord_745102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745108 : List Nat := [2, 4, 2, 2, 2, 2, 1, 3, 2]
def baseStart_745108 : Nat := 118140960795 + 745108 * 2 ^ 59
def prefixEnd_745108 : Nat := 4983230072969 + 3 ^ 40 * 745108 * 2
def baseEnd_745108 : Nat := 340087594231445329087393

theorem tailTrace_745108 : CollatzResearch.WordTrace tailWord_745108 prefixEnd_745108 340087594231445329087393 := by
  unfold tailWord_745108
  simp only [CollatzResearch.WordTrace]
  refine ⟨13588160692304222580137989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18117547589738963440183985 13588160692304222580137989)
  ·
    refine ⟨2547780129807041733775873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13588160692304222580137989 2547780129807041733775873)
    ·
      refine ⟨1910835097355281300331905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2547780129807041733775873 1910835097355281300331905)
      ·
        refine ⟨1433126323016460975248929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1910835097355281300331905 1433126323016460975248929)
        ·
          refine ⟨1074844742262345731436697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1433126323016460975248929 1074844742262345731436697)
          ·
            refine ⟨806133556696759298577523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1074844742262345731436697 806133556696759298577523)
            ·
              refine ⟨1209200335045138947866285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806133556696759298577523 1209200335045138947866285)
              ·
                refine ⟨453450125641927105449857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1209200335045138947866285 453450125641927105449857)
                ·
                  refine ⟨340087594231445329087393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453450125641927105449857 340087594231445329087393)
                  ·
                    rfl

theorem cell20_745108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_745108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745108 prefixEnd_745108 := by exact prefixLift 745108
  have htrace : WordTrace (prefixWord ++ tailWord_745108) baseStart_745108 baseEnd_745108 := by
    simpa [prefixWord, tailWord_745108, baseEnd_745108] using wordTrace_append hprefix tailTrace_745108
  have hstable : (prefixWord ++ tailWord_745108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745108).length < 2 ^ (prefixWord ++ tailWord_745108).sum := by decide
  have hdescent : baseEnd_745108 < baseStart_745108 := by decide
  rcases family_descends (prefixWord ++ tailWord_745108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745112 : List Nat := [2, 1, 2, 4, 1, 2, 3, 3, 2]
def baseStart_745112 : Nat := 118140960795 + 745112 * 2 ^ 59
def prefixEnd_745112 : Nat := 4983230072969 + 3 ^ 40 * 745112 * 2
def baseEnd_745112 : Nat := 340089419940439092954043

theorem tailTrace_745112 : CollatzResearch.WordTrace tailWord_745112 prefixEnd_745112 340089419940439092954043 := by
  unfold tailWord_745112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13588233638296976921710795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18117644851062635895614393 13588233638296976921710795)
  ·
    refine ⟨20382350457445465382566193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13588233638296976921710795 20382350457445465382566193)
    ·
      refine ⟨15286762843084099036924645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20382350457445465382566193 15286762843084099036924645)
      ·
        refine ⟨2866268033078268569423371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15286762843084099036924645 2866268033078268569423371)
        ·
          refine ⟨4299402049617402854135057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866268033078268569423371 4299402049617402854135057)
          ·
            refine ⟨3224551537213052140601293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4299402049617402854135057 3224551537213052140601293)
            ·
              refine ⟨1209206826454894552725485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3224551537213052140601293 1209206826454894552725485)
              ·
                refine ⟨453452559920585457272057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1209206826454894552725485 453452559920585457272057)
                ·
                  refine ⟨340089419940439092954043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453452559920585457272057 340089419940439092954043)
                  ·
                    rfl

theorem cell20_745112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 2].length) (baseStart_745112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745112 prefixEnd_745112 := by exact prefixLift 745112
  have htrace : WordTrace (prefixWord ++ tailWord_745112) baseStart_745112 baseEnd_745112 := by
    simpa [prefixWord, tailWord_745112, baseEnd_745112] using wordTrace_append hprefix tailTrace_745112
  have hstable : (prefixWord ++ tailWord_745112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745112).length < 2 ^ (prefixWord ++ tailWord_745112).sum := by decide
  have hdescent : baseEnd_745112 < baseStart_745112 := by decide
  rcases family_descends (prefixWord ++ tailWord_745112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745119 : List Nat := [1, 1, 2, 7, 1, 2, 6]
def baseStart_745119 : Nat := 118140960795 + 745119 * 2 ^ 59
def prefixEnd_745119 : Nat := 4983230072969 + 3 ^ 40 * 745119 * 2
def baseEnd_745119 : Nat := 37788068325686464413409

theorem tailTrace_745119 : CollatzResearch.WordTrace tailWord_745119 prefixEnd_745119 37788068325686464413409 := by
  unfold tailWord_745119
  simp only [CollatzResearch.WordTrace]
  refine ⟨27176722587568594038926411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18117815058379062692617607 27176722587568594038926411)
  ·
    refine ⟨40765083881352891058389617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27176722587568594038926411 40765083881352891058389617)
    ·
      refine ⟨30573812911014668293792213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40765083881352891058389617 30573812911014668293792213)
      ·
        refine ⟨716573740101906288135755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 30573812911014668293792213 716573740101906288135755)
        ·
          refine ⟨1074860610152859432203633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716573740101906288135755 1074860610152859432203633)
          ·
            refine ⟨806145457614644574152725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1074860610152859432203633 806145457614644574152725)
            ·
              refine ⟨37788068325686464413409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 806145457614644574152725 37788068325686464413409)
              ·
                rfl

theorem cell20_745119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 6].length) (baseStart_745119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745119 prefixEnd_745119 := by exact prefixLift 745119
  have htrace : WordTrace (prefixWord ++ tailWord_745119) baseStart_745119 baseEnd_745119 := by
    simpa [prefixWord, tailWord_745119, baseEnd_745119] using wordTrace_append hprefix tailTrace_745119
  have hstable : (prefixWord ++ tailWord_745119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745119).length < 2 ^ (prefixWord ++ tailWord_745119).sum := by decide
  have hdescent : baseEnd_745119 < baseStart_745119 := by decide
  rcases family_descends (prefixWord ++ tailWord_745119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745143 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 3]
def baseStart_745143 : Nat := 118140960795 + 745143 * 2 ^ 59
def prefixEnd_745143 : Nat := 4983230072969 + 3 ^ 40 * 745143 * 2
def baseEnd_745143 : Nat := 340103569185140762920583

theorem tailTrace_745143 : CollatzResearch.WordTrace tailWord_745143 prefixEnd_745143 340103569185140762920583 := by
  unfold tailWord_745143
  simp only [CollatzResearch.WordTrace]
  refine ⟨27177597939481646137800083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18118398626321097425200055 27177597939481646137800083)
  ·
    refine ⟨40766396909222469206700125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27177597939481646137800083 40766396909222469206700125)
    ·
      refine ⟨15287398840958425952512547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40766396909222469206700125 15287398840958425952512547)
      ·
        refine ⟨22931098261437638928768821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15287398840958425952512547 22931098261437638928768821)
        ·
          refine ⟨2149790462009778649572077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22931098261437638928768821 2149790462009778649572077)
          ·
            refine ⟨806171423253666993589529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2149790462009778649572077 806171423253666993589529)
            ·
              refine ⟨604628567440250245192147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806171423253666993589529 604628567440250245192147)
              ·
                refine ⟨906942851160375367788221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604628567440250245192147 906942851160375367788221)
                ·
                  refine ⟨340103569185140762920583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 906942851160375367788221 340103569185140762920583)
                  ·
                    rfl

theorem cell20_745143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 3].length) (baseStart_745143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745143 prefixEnd_745143 := by exact prefixLift 745143
  have htrace : WordTrace (prefixWord ++ tailWord_745143) baseStart_745143 baseEnd_745143 := by
    simpa [prefixWord, tailWord_745143, baseEnd_745143] using wordTrace_append hprefix tailTrace_745143
  have hstable : (prefixWord ++ tailWord_745143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745143).length < 2 ^ (prefixWord ++ tailWord_745143).sum := by decide
  have hdescent : baseEnd_745143 < baseStart_745143 := by decide
  rcases family_descends (prefixWord ++ tailWord_745143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745168 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_745168 : Nat := 118140960795 + 745168 * 2 ^ 59
def prefixEnd_745168 : Nat := 4983230072969 + 3 ^ 40 * 745168 * 2
def baseEnd_745168 : Nat := 340114979866351787087147

theorem tailTrace_745168 : CollatzResearch.WordTrace tailWord_745168 prefixEnd_745168 340114979866351787087147 := by
  unfold tailWord_745168
  simp only [CollatzResearch.WordTrace]
  refine ⟨13589254882195537703730079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18119006509594050271640105 13589254882195537703730079)
  ·
    refine ⟨20383882323293306555595119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13589254882195537703730079 20383882323293306555595119)
    ·
      refine ⟨30575823484939959833392679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20383882323293306555595119 30575823484939959833392679)
      ·
        refine ⟨45863735227409939750089019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30575823484939959833392679 45863735227409939750089019)
        ·
          refine ⟨68795602841114909625133529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45863735227409939750089019 68795602841114909625133529)
          ·
            refine ⟨51596702130836182218850147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68795602841114909625133529 51596702130836182218850147)
            ·
              refine ⟨77395053196254273328275221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51596702130836182218850147 77395053196254273328275221)
              ·
                refine ⟨3627893118574419062262901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77395053196254273328275221 3627893118574419062262901)
                ·
                  refine ⟨340114979866351787087147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3627893118574419062262901 340114979866351787087147)
                  ·
                    rfl

theorem cell20_745168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_745168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745168 prefixEnd_745168 := by exact prefixLift 745168
  have htrace : WordTrace (prefixWord ++ tailWord_745168) baseStart_745168 baseEnd_745168 := by
    simpa [prefixWord, tailWord_745168, baseEnd_745168] using wordTrace_append hprefix tailTrace_745168
  have hstable : (prefixWord ++ tailWord_745168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745168).length < 2 ^ (prefixWord ++ tailWord_745168).sum := by decide
  have hdescent : baseEnd_745168 < baseStart_745168 := by decide
  rcases family_descends (prefixWord ++ tailWord_745168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745174 : List Nat := [5, 2, 1, 3, 2, 7]
def baseStart_745174 : Nat := 118140960795 + 745174 * 2 ^ 59
def prefixEnd_745174 : Nat := 4983230072969 + 3 ^ 40 * 745174 * 2
def baseEnd_745174 : Nat := 12596952534438608625449

theorem tailTrace_745174 : CollatzResearch.WordTrace tailWord_745174 prefixEnd_745174 12596952534438608625449 := by
  unfold tailWord_745174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698670537648083652011161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18119152401579558954785717 1698670537648083652011161)
  ·
    refine ⟨1274002903236062739008371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1698670537648083652011161 1274002903236062739008371)
    ·
      refine ⟨1911004354854094108512557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1274002903236062739008371 1911004354854094108512557)
      ·
        refine ⟨716626633070285290692209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1911004354854094108512557 716626633070285290692209)
        ·
          refine ⟨537469974802713968019157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716626633070285290692209 537469974802713968019157)
          ·
            refine ⟨12596952534438608625449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 537469974802713968019157 12596952534438608625449)
            ·
              rfl

theorem cell20_745174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 7].length) (baseStart_745174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745174 prefixEnd_745174 := by exact prefixLift 745174
  have htrace : WordTrace (prefixWord ++ tailWord_745174) baseStart_745174 baseEnd_745174 := by
    simpa [prefixWord, tailWord_745174, baseEnd_745174] using wordTrace_append hprefix tailTrace_745174
  have hstable : (prefixWord ++ tailWord_745174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745174).length < 2 ^ (prefixWord ++ tailWord_745174).sum := by decide
  have hdescent : baseEnd_745174 < baseStart_745174 := by decide
  rcases family_descends (prefixWord ++ tailWord_745174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745226 : List Nat := [3, 1, 2, 2, 1, 4, 2, 3, 2]
def baseStart_745226 : Nat := 118140960795 + 745226 * 2 ^ 59
def prefixEnd_745226 : Nat := 4983230072969 + 3 ^ 40 * 745226 * 2
def baseEnd_745226 : Nat := 340141452646761363153577

theorem tailTrace_745226 : CollatzResearch.WordTrace tailWord_745226 prefixEnd_745226 340141452646761363153577 := by
  unfold tailWord_745226
  simp only [CollatzResearch.WordTrace]
  refine ⟨6795156299545237828267883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18120416798787300875381021 6795156299545237828267883)
  ·
    refine ⟨10192734449317856742401825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6795156299545237828267883 10192734449317856742401825)
    ·
      refine ⟨7644550836988392556801369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10192734449317856742401825 7644550836988392556801369)
      ·
        refine ⟨5733413127741294417601027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7644550836988392556801369 5733413127741294417601027)
        ·
          refine ⟨8600119691611941626401541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5733413127741294417601027 8600119691611941626401541)
          ·
            refine ⟨1612522442177239054950289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8600119691611941626401541 1612522442177239054950289)
            ·
              refine ⟨1209391831632929291212717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1612522442177239054950289 1209391831632929291212717)
              ·
                refine ⟨453521936862348484204769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1209391831632929291212717 453521936862348484204769)
                ·
                  refine ⟨340141452646761363153577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453521936862348484204769 340141452646761363153577)
                  ·
                    rfl

theorem cell20_745226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_745226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745226 prefixEnd_745226 := by exact prefixLift 745226
  have htrace : WordTrace (prefixWord ++ tailWord_745226) baseStart_745226 baseEnd_745226 := by
    simpa [prefixWord, tailWord_745226, baseEnd_745226] using wordTrace_append hprefix tailTrace_745226
  have hstable : (prefixWord ++ tailWord_745226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745226).length < 2 ^ (prefixWord ++ tailWord_745226).sum := by decide
  have hdescent : baseEnd_745226 < baseStart_745226 := by decide
  rcases family_descends (prefixWord ++ tailWord_745226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745229 : List Nat := [1, 7, 2, 1, 1, 1, 7]
def baseStart_745229 : Nat := 118140960795 + 745229 * 2 ^ 59
def prefixEnd_745229 : Nat := 4983230072969 + 3 ^ 40 * 745229 * 2
def baseEnd_745229 : Nat := 37793646880945187339285

theorem tailTrace_745229 : CollatzResearch.WordTrace tailWord_745229 prefixEnd_745229 37793646880945187339285 := by
  unfold tailWord_745229
  simp only [CollatzResearch.WordTrace]
  refine ⟨27180734617170082825430741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18120489744780055216953827 27180734617170082825430741)
  ·
    refine ⟨637048467589923816221033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 27180734617170082825430741 637048467589923816221033)
    ·
      refine ⟨477786350692442862165775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 637048467589923816221033 477786350692442862165775)
      ·
        refine ⟨716679526038664293248663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477786350692442862165775 716679526038664293248663)
        ·
          refine ⟨1075019289057996439872995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716679526038664293248663 1075019289057996439872995)
          ·
            refine ⟨1612528933586994659809493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075019289057996439872995 1612528933586994659809493)
            ·
              refine ⟨37793646880945187339285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1612528933586994659809493 37793646880945187339285)
              ·
                rfl

theorem cell20_745229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 7].length) (baseStart_745229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745229 prefixEnd_745229 := by exact prefixLift 745229
  have htrace : WordTrace (prefixWord ++ tailWord_745229) baseStart_745229 baseEnd_745229 := by
    simpa [prefixWord, tailWord_745229, baseEnd_745229] using wordTrace_append hprefix tailTrace_745229
  have hstable : (prefixWord ++ tailWord_745229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745229).length < 2 ^ (prefixWord ++ tailWord_745229).sum := by decide
  have hdescent : baseEnd_745229 < baseStart_745229 := by decide
  rcases family_descends (prefixWord ++ tailWord_745229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745236 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 5]
def baseStart_745236 : Nat := 118140960795 + 745236 * 2 ^ 59
def prefixEnd_745236 : Nat := 4983230072969 + 3 ^ 40 * 745236 * 2
def baseEnd_745236 : Nat := 340146016919245772820203

theorem tailTrace_745236 : CollatzResearch.WordTrace tailWord_745236 prefixEnd_745236 340146016919245772820203 := by
  unfold tailWord_745236
  simp only [CollatzResearch.WordTrace]
  refine ⟨13590494964072361510467781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18120659952096482013957041 13590494964072361510467781)
  ·
    refine ⟨2548217805763567783212709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13590494964072361510467781 2548217805763567783212709)
    ·
      refine ⟨477790838580668959352383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2548217805763567783212709 477790838580668959352383)
      ·
        refine ⟨716686257871003439028575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477790838580668959352383 716686257871003439028575)
        ·
          refine ⟨1075029386806505158542863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716686257871003439028575 1075029386806505158542863)
          ·
            refine ⟨1612544080209757737814295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075029386806505158542863 1612544080209757737814295)
            ·
              refine ⟨2418816120314636606721443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612544080209757737814295 2418816120314636606721443)
              ·
                refine ⟨3628224180471954910082165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418816120314636606721443 3628224180471954910082165)
                ·
                  refine ⟨340146016919245772820203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3628224180471954910082165 340146016919245772820203)
                  ·
                    rfl

theorem cell20_745236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_745236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745236 prefixEnd_745236 := by exact prefixLift 745236
  have htrace : WordTrace (prefixWord ++ tailWord_745236) baseStart_745236 baseEnd_745236 := by
    simpa [prefixWord, tailWord_745236, baseEnd_745236] using wordTrace_append hprefix tailTrace_745236
  have hstable : (prefixWord ++ tailWord_745236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745236).length < 2 ^ (prefixWord ++ tailWord_745236).sum := by decide
  have hdescent : baseEnd_745236 < baseStart_745236 := by decide
  rcases family_descends (prefixWord ++ tailWord_745236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745237 : List Nat := [1, 3, 2, 1, 2, 4, 7]
def baseStart_745237 : Nat := 118140960795 + 745237 * 2 ^ 59
def prefixEnd_745237 : Nat := 4983230072969 + 3 ^ 40 * 745237 * 2
def baseEnd_745237 : Nat := 37794052594054912642985

theorem tailTrace_745237 : CollatzResearch.WordTrace tailWord_745237 prefixEnd_745237 37794052594054912642985 := by
  unfold tailWord_745237
  simp only [CollatzResearch.WordTrace]
  refine ⟨27181026401141100191721965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18120684267427400127814643 27181026401141100191721965)
  ·
    refine ⟨10192884900427912571895737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27181026401141100191721965 10192884900427912571895737)
    ·
      refine ⟨7644663675320934428921803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10192884900427912571895737 7644663675320934428921803)
      ·
        refine ⟨11466995512981401643382705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7644663675320934428921803 11466995512981401643382705)
        ·
          refine ⟨8600246634736051232537029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11466995512981401643382705 8600246634736051232537029)
          ·
            refine ⟨1612546244013009606100693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8600246634736051232537029 1612546244013009606100693)
            ·
              refine ⟨37794052594054912642985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1612546244013009606100693 37794052594054912642985)
              ·
                rfl

theorem cell20_745237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 7].length) (baseStart_745237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745237 prefixEnd_745237 := by exact prefixLift 745237
  have htrace : WordTrace (prefixWord ++ tailWord_745237) baseStart_745237 baseEnd_745237 := by
    simpa [prefixWord, tailWord_745237, baseEnd_745237] using wordTrace_append hprefix tailTrace_745237
  have hstable : (prefixWord ++ tailWord_745237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745237).length < 2 ^ (prefixWord ++ tailWord_745237).sum := by decide
  have hdescent : baseEnd_745237 < baseStart_745237 := by decide
  rcases family_descends (prefixWord ++ tailWord_745237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745247 : List Nat := [1, 1, 2, 4, 2, 1, 1, 6, 2]
def baseStart_745247 : Nat := 118140960795 + 745247 * 2 ^ 59
def prefixEnd_745247 : Nat := 4983230072969 + 3 ^ 40 * 745247 * 2
def baseEnd_745247 : Nat := 340151037618978623453491

theorem tailTrace_745247 : CollatzResearch.WordTrace tailWord_745247 prefixEnd_745247 340151037618978623453491 := by
  unfold tailWord_745247
  simp only [CollatzResearch.WordTrace]
  refine ⟨27181391131104871899585995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18120927420736581266390663 27181391131104871899585995)
  ·
    refine ⟨40772086696657307849378993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27181391131104871899585995 40772086696657307849378993)
    ·
      refine ⟨30579065022492980887034245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40772086696657307849378993 30579065022492980887034245)
      ·
        refine ⟨5733574691717433916318921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30579065022492980887034245 5733574691717433916318921)
        ·
          refine ⟨4300181018788075437239191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5733574691717433916318921 4300181018788075437239191)
          ·
            refine ⟨6450271528182113155858787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300181018788075437239191 6450271528182113155858787)
            ·
              refine ⟨9675407292273169733788181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6450271528182113155858787 9675407292273169733788181)
              ·
                refine ⟨453534716825304831271321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9675407292273169733788181 453534716825304831271321)
                ·
                  refine ⟨340151037618978623453491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453534716825304831271321 340151037618978623453491)
                  ·
                    rfl

theorem cell20_745247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 2].length) (baseStart_745247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745247 prefixEnd_745247 := by exact prefixLift 745247
  have htrace : WordTrace (prefixWord ++ tailWord_745247) baseStart_745247 baseEnd_745247 := by
    simpa [prefixWord, tailWord_745247, baseEnd_745247] using wordTrace_append hprefix tailTrace_745247
  have hstable : (prefixWord ++ tailWord_745247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745247).length < 2 ^ (prefixWord ++ tailWord_745247).sum := by decide
  have hdescent : baseEnd_745247 < baseStart_745247 := by decide
  rcases family_descends (prefixWord ++ tailWord_745247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745292 : List Nat := [2, 2, 1, 3, 4, 2, 6]
def baseStart_745292 : Nat := 118140960795 + 745292 * 2 ^ 59
def prefixEnd_745292 : Nat := 4983230072969 + 3 ^ 40 * 745292 * 2
def baseEnd_745292 : Nat := 37796841871684274105923

theorem tailTrace_745292 : CollatzResearch.WordTrace tailWord_745292 prefixEnd_745292 37796841871684274105923 := by
  unfold tailWord_745292
  simp only [CollatzResearch.WordTrace]
  refine ⟨13591516207970922292487065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18122021610627896389982753 13591516207970922292487065)
  ·
    refine ⟨10193637155978191719365299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13591516207970922292487065 10193637155978191719365299)
    ·
      refine ⟨15290455733967287579047949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10193637155978191719365299 15290455733967287579047949)
      ·
        refine ⟨5733920900237732842142981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15290455733967287579047949 5733920900237732842142981)
        ·
          refine ⟨1075110168794574907901809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5733920900237732842142981 1075110168794574907901809)
          ·
            refine ⟨806332626595931180926357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1075110168794574907901809 806332626595931180926357)
            ·
              refine ⟨37796841871684274105923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 806332626595931180926357 37796841871684274105923)
              ·
                rfl

theorem cell20_745292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 6].length) (baseStart_745292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745292 prefixEnd_745292 := by exact prefixLift 745292
  have htrace : WordTrace (prefixWord ++ tailWord_745292) baseStart_745292 baseEnd_745292 := by
    simpa [prefixWord, tailWord_745292, baseEnd_745292] using wordTrace_append hprefix tailTrace_745292
  have hstable : (prefixWord ++ tailWord_745292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745292).length < 2 ^ (prefixWord ++ tailWord_745292).sum := by decide
  have hdescent : baseEnd_745292 < baseStart_745292 := by decide
  rcases family_descends (prefixWord ++ tailWord_745292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745313 : List Nat := [1, 2, 3, 1, 1, 1, 6, 5]
def baseStart_745313 : Nat := 118140960795 + 745313 * 2 ^ 59
def prefixEnd_745313 : Nat := 4983230072969 + 3 ^ 40 * 745313 * 2
def baseEnd_745313 : Nat := 113393720605791909084407

theorem tailTrace_745313 : CollatzResearch.WordTrace tailWord_745313 prefixEnd_745313 113393720605791909084407 := by
  unfold tailWord_745313
  simp only [CollatzResearch.WordTrace]
  refine ⟨27183798348865765171488593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18122532232577176780992395 27183798348865765171488593)
  ·
    refine ⟨20387848761649323878616445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27183798348865765171488593 20387848761649323878616445)
    ·
      refine ⟨7645443285618496454481167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20387848761649323878616445 7645443285618496454481167)
      ·
        refine ⟨11468164928427744681721751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7645443285618496454481167 11468164928427744681721751)
        ·
          refine ⟨17202247392641617022582627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11468164928427744681721751 17202247392641617022582627)
          ·
            refine ⟨25803371088962425533873941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17202247392641617022582627 25803371088962425533873941)
            ·
              refine ⟨1209533019795113696900341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25803371088962425533873941 1209533019795113696900341)
              ·
                refine ⟨113393720605791909084407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1209533019795113696900341 113393720605791909084407)
                ·
                  rfl

theorem cell20_745313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_745313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745313 prefixEnd_745313 := by exact prefixLift 745313
  have htrace : WordTrace (prefixWord ++ tailWord_745313) baseStart_745313 baseEnd_745313 := by
    simpa [prefixWord, tailWord_745313, baseEnd_745313] using wordTrace_append hprefix tailTrace_745313
  have hstable : (prefixWord ++ tailWord_745313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745313).length < 2 ^ (prefixWord ++ tailWord_745313).sum := by decide
  have hdescent : baseEnd_745313 < baseStart_745313 := by decide
  rcases family_descends (prefixWord ++ tailWord_745313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745316 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 3]
def baseStart_745316 : Nat := 118140960795 + 745316 * 2 ^ 59
def prefixEnd_745316 : Nat := 4983230072969 + 3 ^ 40 * 745316 * 2
def baseEnd_745316 : Nat := 340182531099121050153209

theorem tailTrace_745316 : CollatzResearch.WordTrace tailWord_745316 prefixEnd_745316 340182531099121050153209 := by
  unfold tailWord_745316
  simp only [CollatzResearch.WordTrace]
  refine ⟨13591953883927448341923901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18122605178569931122565201 13591953883927448341923901)
  ·
    refine ⟨5096982706472793128221463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13591953883927448341923901 5096982706472793128221463)
    ·
      refine ⟨7645474059709189692332195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5096982706472793128221463 7645474059709189692332195)
      ·
        refine ⟨11468211089563784538498293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7645474059709189692332195 11468211089563784538498293)
        ·
          refine ⟨1075144789646604800484215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11468211089563784538498293 1075144789646604800484215)
          ·
            refine ⟨1612717184469907200726323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075144789646604800484215 1612717184469907200726323)
            ·
              refine ⟨2419075776704860801089485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612717184469907200726323 2419075776704860801089485)
              ·
                refine ⟨907153416264322800408557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2419075776704860801089485 907153416264322800408557)
                ·
                  refine ⟨340182531099121050153209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907153416264322800408557 340182531099121050153209)
                  ·
                    rfl

theorem cell20_745316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_745316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745316 prefixEnd_745316 := by exact prefixLift 745316
  have htrace : WordTrace (prefixWord ++ tailWord_745316) baseStart_745316 baseEnd_745316 := by
    simpa [prefixWord, tailWord_745316, baseEnd_745316] using wordTrace_append hprefix tailTrace_745316
  have hstable : (prefixWord ++ tailWord_745316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745316).length < 2 ^ (prefixWord ++ tailWord_745316).sum := by decide
  have hdescent : baseEnd_745316 < baseStart_745316 := by decide
  rcases family_descends (prefixWord ++ tailWord_745316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745351 : List Nat := [1, 1, 4, 2, 4, 8]
def baseStart_745351 : Nat := 118140960795 + 745351 * 2 ^ 59
def prefixEnd_745351 : Nat := 4983230072969 + 3 ^ 40 * 745351 * 2
def baseEnd_745351 : Nat := 12599944668622832740237

theorem tailTrace_745351 : CollatzResearch.WordTrace tailWord_745351 prefixEnd_745351 12599944668622832740237 := by
  unfold tailWord_745351
  simp only [CollatzResearch.WordTrace]
  refine ⟨27185184322728097661371907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18123456215152065107581271 27185184322728097661371907)
  ·
    refine ⟨40777776484092146492057861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27185184322728097661371907 40777776484092146492057861)
    ·
      refine ⟨7645833090767277467260849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40777776484092146492057861 7645833090767277467260849)
      ·
        refine ⟨5734374818075458100445637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7645833090767277467260849 5734374818075458100445637)
        ·
          refine ⟨1075195278389148393833557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5734374818075458100445637 1075195278389148393833557)
          ·
            refine ⟨12599944668622832740237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1075195278389148393833557 12599944668622832740237)
            ·
              rfl

theorem cell20_745351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 8].length) (baseStart_745351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745351 prefixEnd_745351 := by exact prefixLift 745351
  have htrace : WordTrace (prefixWord ++ tailWord_745351) baseStart_745351 baseEnd_745351 := by
    simpa [prefixWord, tailWord_745351, baseEnd_745351] using wordTrace_append hprefix tailTrace_745351
  have hstable : (prefixWord ++ tailWord_745351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745351).length < 2 ^ (prefixWord ++ tailWord_745351).sum := by decide
  have hdescent : baseEnd_745351 < baseStart_745351 := by decide
  rcases family_descends (prefixWord ++ tailWord_745351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745420 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_745420 : Nat := 118140960795 + 745420 * 2 ^ 59
def prefixEnd_745420 : Nat := 4983230072969 + 3 ^ 40 * 745420 * 2
def baseEnd_745420 : Nat := 340229999532958910686117

theorem tailTrace_745420 : CollatzResearch.WordTrace tailWord_745420 prefixEnd_745420 340229999532958910686117 := by
  unfold tailWord_745420
  simp only [CollatzResearch.WordTrace]
  refine ⟨13593850479739061222816857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18125133972985414963755809 13593850479739061222816857)
  ·
    refine ⟨10195387859804295917112643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13593850479739061222816857 10195387859804295917112643)
    ·
      refine ⟨15293081789706443875668965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10195387859804295917112643 15293081789706443875668965)
      ·
        refine ⟨2867452835569958226687931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15293081789706443875668965 2867452835569958226687931)
        ·
          refine ⟨4301179253354937340031897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2867452835569958226687931 4301179253354937340031897)
          ·
            refine ⟨3225884440016203005023923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4301179253354937340031897 3225884440016203005023923)
            ·
              refine ⟨4838826660024304507535885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3225884440016203005023923 4838826660024304507535885)
              ·
                refine ⟨1814559997509114190325957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4838826660024304507535885 1814559997509114190325957)
                ·
                  refine ⟨340229999532958910686117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1814559997509114190325957 340229999532958910686117)
                  ·
                    rfl

theorem cell20_745420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_745420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745420 prefixEnd_745420 := by exact prefixLift 745420
  have htrace : WordTrace (prefixWord ++ tailWord_745420) baseStart_745420 baseEnd_745420 := by
    simpa [prefixWord, tailWord_745420, baseEnd_745420] using wordTrace_append hprefix tailTrace_745420
  have hstable : (prefixWord ++ tailWord_745420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745420).length < 2 ^ (prefixWord ++ tailWord_745420).sum := by decide
  have hdescent : baseEnd_745420 < baseStart_745420 := by decide
  rcases family_descends (prefixWord ++ tailWord_745420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745436 : List Nat := [2, 2, 6, 1, 2, 1, 2, 4]
def baseStart_745436 : Nat := 118140960795 + 745436 * 2 ^ 59
def prefixEnd_745436 : Nat := 4983230072969 + 3 ^ 40 * 745436 * 2
def baseEnd_745436 : Nat := 113412434122977988717573

theorem tailTrace_745436 : CollatzResearch.WordTrace tailWord_745436 prefixEnd_745436 113412434122977988717573 := by
  unfold tailWord_745436
  simp only [CollatzResearch.WordTrace]
  refine ⟨13594142263710078589108081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18125523018280104785477441 13594142263710078589108081)
  ·
    refine ⟨10195606697782558941831061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13594142263710078589108081 10195606697782558941831061)
    ·
      refine ⟨477919063958557450398331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10195606697782558941831061 477919063958557450398331)
      ·
        refine ⟨716878595937836175597497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477919063958557450398331 716878595937836175597497)
        ·
          refine ⟨537658946953377131698123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716878595937836175597497 537658946953377131698123)
          ·
            refine ⟨806488420430065697547185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537658946953377131698123 806488420430065697547185)
            ·
              refine ⟨604866315322549273160389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806488420430065697547185 604866315322549273160389)
              ·
                refine ⟨113412434122977988717573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 604866315322549273160389 113412434122977988717573)
                ·
                  rfl

theorem cell20_745436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_745436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745436 prefixEnd_745436 := by exact prefixLift 745436
  have htrace : WordTrace (prefixWord ++ tailWord_745436) baseStart_745436 baseEnd_745436 := by
    simpa [prefixWord, tailWord_745436, baseEnd_745436] using wordTrace_append hprefix tailTrace_745436
  have hstable : (prefixWord ++ tailWord_745436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745436).length < 2 ^ (prefixWord ++ tailWord_745436).sum := by decide
  have hdescent : baseEnd_745436 < baseStart_745436 := by decide
  rcases family_descends (prefixWord ++ tailWord_745436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745454 : List Nat := [4, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_745454 : Nat := 118140960795 + 745454 * 2 ^ 59
def prefixEnd_745454 : Nat := 4983230072969 + 3 ^ 40 * 745454 * 2
def baseEnd_745454 : Nat := 340245518059405903552645

theorem tailTrace_745454 : CollatzResearch.WordTrace tailWord_745454 prefixEnd_745454 340245518059405903552645 := by
  unfold tailWord_745454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3398617630169368281546427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18125960694236630834914277 3398617630169368281546427)
  ·
    refine ⟨5097926445254052422319641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3398617630169368281546427 5097926445254052422319641)
    ·
      refine ⟨3823444833940539316739731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5097926445254052422319641 3823444833940539316739731)
      ·
        refine ⟨5735167250910808975109597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3823444833940539316739731 5735167250910808975109597)
        ·
          refine ⟨2150687719091553365666099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5735167250910808975109597 2150687719091553365666099)
          ·
            refine ⟨3226031578637330048499149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150687719091553365666099 3226031578637330048499149)
            ·
              refine ⟨1209761841988998768187181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3226031578637330048499149 1209761841988998768187181)
              ·
                refine ⟨453660690745874538070193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1209761841988998768187181 453660690745874538070193)
                ·
                  refine ⟨340245518059405903552645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453660690745874538070193 340245518059405903552645)
                  ·
                    rfl

theorem cell20_745454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_745454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745454 prefixEnd_745454 := by exact prefixLift 745454
  have htrace : WordTrace (prefixWord ++ tailWord_745454) baseStart_745454 baseEnd_745454 := by
    simpa [prefixWord, tailWord_745454, baseEnd_745454] using wordTrace_append hprefix tailTrace_745454
  have hstable : (prefixWord ++ tailWord_745454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745454).length < 2 ^ (prefixWord ++ tailWord_745454).sum := by decide
  have hdescent : baseEnd_745454 < baseStart_745454 := by decide
  rcases family_descends (prefixWord ++ tailWord_745454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745465 : List Nat := [1, 2, 1, 3, 1, 6, 6]
def baseStart_745465 : Nat := 118140960795 + 745465 * 2 ^ 59
def prefixEnd_745465 : Nat := 4983230072969 + 3 ^ 40 * 745465 * 2
def baseEnd_745465 : Nat := 37805615417682083798437

theorem tailTrace_745465 : CollatzResearch.WordTrace tailWord_745465 prefixEnd_745465 37805615417682083798437 := by
  unfold tailWord_745465
  simp only [CollatzResearch.WordTrace]
  refine ⟨27189342244315095131021849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18126228162876730087347899 27189342244315095131021849)
  ·
    refine ⟨20392006683236321348266387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27189342244315095131021849 20392006683236321348266387)
    ·
      refine ⟨30588010024854482022399581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20392006683236321348266387 30588010024854482022399581)
      ·
        refine ⟨11470503759320430758399843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30588010024854482022399581 11470503759320430758399843)
        ·
          refine ⟨17205755638980646137599765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11470503759320430758399843 17205755638980646137599765)
          ·
            refine ⟨806519795577217787699989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17205755638980646137599765 806519795577217787699989)
            ·
              refine ⟨37805615417682083798437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 806519795577217787699989 37805615417682083798437)
              ·
                rfl

theorem cell20_745465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 6].length) (baseStart_745465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745465 prefixEnd_745465 := by exact prefixLift 745465
  have htrace : WordTrace (prefixWord ++ tailWord_745465) baseStart_745465 baseEnd_745465 := by
    simpa [prefixWord, tailWord_745465, baseEnd_745465] using wordTrace_append hprefix tailTrace_745465
  have hstable : (prefixWord ++ tailWord_745465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745465).length < 2 ^ (prefixWord ++ tailWord_745465).sum := by decide
  have hdescent : baseEnd_745465 < baseStart_745465 := by decide
  rcases family_descends (prefixWord ++ tailWord_745465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745482 : List Nat := [3, 1, 2, 2, 4, 1, 2, 5]
def baseStart_745482 : Nat := 118140960795 + 745482 * 2 ^ 59
def prefixEnd_745482 : Nat := 4983230072969 + 3 ^ 40 * 745482 * 2
def baseEnd_745482 : Nat := 113419432674120750206399

theorem tailTrace_745482 : CollatzResearch.WordTrace tailWord_745482 prefixEnd_745482 113419432674120750206399 := by
  unfold tailWord_745482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797490571313376758597675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18126641523502338022927133 6797490571313376758597675)
  ·
    refine ⟨10196235856970065137896513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6797490571313376758597675 10196235856970065137896513)
    ·
      refine ⟨7647176892727548853422385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10196235856970065137896513 7647176892727548853422385)
      ·
        refine ⟨5735382669545661640066789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7647176892727548853422385 5735382669545661640066789)
        ·
          refine ⟨1075384250539811557512523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5735382669545661640066789 1075384250539811557512523)
          ·
            refine ⟨1613076375809717336268785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075384250539811557512523 1613076375809717336268785)
            ·
              refine ⟨1209807281857288002201589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613076375809717336268785 1209807281857288002201589)
              ·
                refine ⟨113419432674120750206399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1209807281857288002201589 113419432674120750206399)
                ·
                  rfl

theorem cell20_745482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_745482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745482 prefixEnd_745482 := by exact prefixLift 745482
  have htrace : WordTrace (prefixWord ++ tailWord_745482) baseStart_745482 baseEnd_745482 := by
    simpa [prefixWord, tailWord_745482, baseEnd_745482] using wordTrace_append hprefix tailTrace_745482
  have hstable : (prefixWord ++ tailWord_745482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745482).length < 2 ^ (prefixWord ++ tailWord_745482).sum := by decide
  have hdescent : baseEnd_745482 < baseStart_745482 := by decide
  rcases family_descends (prefixWord ++ tailWord_745482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745600 : List Nat := [2, 1, 1, 2, 1, 3, 1, 9]
def baseStart_745600 : Nat := 118140960795 + 745600 * 2 ^ 59
def prefixEnd_745600 : Nat := 4983230072969 + 3 ^ 40 * 745600 * 2
def baseEnd_745600 : Nat := 113437385479226094895127

theorem tailTrace_745600 : CollatzResearch.WordTrace tailWord_745600 prefixEnd_745600 113437385479226094895127 := by
  unfold tailWord_745600
  simp only [CollatzResearch.WordTrace]
  refine ⟨13597133049413006593593127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18129510732550675458124169 13597133049413006593593127)
  ·
    refine ⟨20395699574119509890389691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13597133049413006593593127 20395699574119509890389691)
    ·
      refine ⟨30593549361179264835584537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20395699574119509890389691 30593549361179264835584537)
      ·
        refine ⟨22945162020884448626688403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30593549361179264835584537 22945162020884448626688403)
        ·
          refine ⟨34417743031326672940032605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22945162020884448626688403 34417743031326672940032605)
          ·
            refine ⟨12906653636747502352512227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34417743031326672940032605 12906653636747502352512227)
            ·
              refine ⟨19359980455121253528768341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12906653636747502352512227 19359980455121253528768341)
              ·
                refine ⟨113437385479226094895127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19359980455121253528768341 113437385479226094895127)
                ·
                  rfl

theorem cell20_745600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_745600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745600 prefixEnd_745600 := by exact prefixLift 745600
  have htrace : WordTrace (prefixWord ++ tailWord_745600) baseStart_745600 baseEnd_745600 := by
    simpa [prefixWord, tailWord_745600, baseEnd_745600] using wordTrace_append hprefix tailTrace_745600
  have hstable : (prefixWord ++ tailWord_745600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745600).length < 2 ^ (prefixWord ++ tailWord_745600).sum := by decide
  have hdescent : baseEnd_745600 < baseStart_745600 := by decide
  rcases family_descends (prefixWord ++ tailWord_745600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745610 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_745610 : Nat := 118140960795 + 745610 * 2 ^ 59
def prefixEnd_745610 : Nat := 4983230072969 + 3 ^ 40 * 745610 * 2
def baseEnd_745610 : Nat := 340316720710162694352007

theorem tailTrace_745610 : CollatzResearch.WordTrace tailWord_745610 prefixEnd_745610 340316720710162694352007 := by
  unfold tailWord_745610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6798657707197446223762571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18129753885859856596700189 6798657707197446223762571)
  ·
    refine ⟨10197986560796169335643857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6798657707197446223762571 10197986560796169335643857)
    ·
      refine ⟨7648489920597127001732893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10197986560796169335643857 7648489920597127001732893)
      ·
        refine ⟨2868183720223922625649835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7648489920597127001732893 2868183720223922625649835)
        ·
          refine ⟨4302275580335883938474753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2868183720223922625649835 4302275580335883938474753)
          ·
            refine ⟨3226706685251912953856065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4302275580335883938474753 3226706685251912953856065)
            ·
              refine ⟨2420030013938934715392049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3226706685251912953856065 2420030013938934715392049)
              ·
                refine ⟨1815022510454201036544037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2420030013938934715392049 1815022510454201036544037)
                ·
                  refine ⟨340316720710162694352007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815022510454201036544037 340316720710162694352007)
                  ·
                    rfl

theorem cell20_745610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_745610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745610 prefixEnd_745610 := by exact prefixLift 745610
  have htrace : WordTrace (prefixWord ++ tailWord_745610) baseStart_745610 baseEnd_745610 := by
    simpa [prefixWord, tailWord_745610, baseEnd_745610] using wordTrace_append hprefix tailTrace_745610
  have hstable : (prefixWord ++ tailWord_745610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745610).length < 2 ^ (prefixWord ++ tailWord_745610).sum := by decide
  have hdescent : baseEnd_745610 < baseStart_745610 := by decide
  rcases family_descends (prefixWord ++ tailWord_745610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745623 : List Nat := [1, 1, 3, 3, 5, 1, 1, 3, 2]
def baseStart_745623 : Nat := 118140960795 + 745623 * 2 ^ 59
def prefixEnd_745623 : Nat := 4983230072969 + 3 ^ 40 * 745623 * 2
def baseEnd_745623 : Nat := 340322654264392426918621

theorem tailTrace_745623 : CollatzResearch.WordTrace tailWord_745623 prefixEnd_745623 340322654264392426918621 := by
  unfold tailWord_745623
  simp only [CollatzResearch.WordTrace]
  refine ⟨27195104977742688115273523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18130069985161792076849015 27195104977742688115273523)
  ·
    refine ⟨40792657466614032172910285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27195104977742688115273523 40792657466614032172910285)
    ·
      refine ⟨15297246549980262064841357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40792657466614032172910285 15297246549980262064841357)
      ·
        refine ⟨5736467456242598274315509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15297246549980262064841357 5736467456242598274315509)
        ·
          refine ⟨537793824022743588217079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5736467456242598274315509 537793824022743588217079)
          ·
            refine ⟨806690736034115382325619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537793824022743588217079 806690736034115382325619)
            ·
              refine ⟨1210036104051173073488429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806690736034115382325619 1210036104051173073488429)
              ·
                refine ⟨453763539019189902558161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1210036104051173073488429 453763539019189902558161)
                ·
                  refine ⟨340322654264392426918621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453763539019189902558161 340322654264392426918621)
                  ·
                    rfl

theorem cell20_745623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 2].length) (baseStart_745623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745623 prefixEnd_745623 := by exact prefixLift 745623
  have htrace : WordTrace (prefixWord ++ tailWord_745623) baseStart_745623 baseEnd_745623 := by
    simpa [prefixWord, tailWord_745623, baseEnd_745623] using wordTrace_append hprefix tailTrace_745623
  have hstable : (prefixWord ++ tailWord_745623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745623).length < 2 ^ (prefixWord ++ tailWord_745623).sum := by decide
  have hdescent : baseEnd_745623 < baseStart_745623 := by decide
  rcases family_descends (prefixWord ++ tailWord_745623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745634 : List Nat := [3, 3, 1, 3, 1, 3, 6]
def baseStart_745634 : Nat := 118140960795 + 745634 * 2 ^ 59
def prefixEnd_745634 : Nat := 4983230072969 + 3 ^ 40 * 745634 * 2
def baseEnd_745634 : Nat := 37814186107125030839101

theorem tailTrace_745634 : CollatzResearch.WordTrace tailWord_745634 prefixEnd_745634 37814186107125030839101 := by
  unfold tailWord_745634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6798876545175709248480989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18130337453801891329282637 6798876545175709248480989)
  ·
    refine ⟨2549578704440890968180371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6798876545175709248480989 2549578704440890968180371)
    ·
      refine ⟨3824368056661336452270557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2549578704440890968180371 3824368056661336452270557)
      ·
        refine ⟨1434138021248001169601459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3824368056661336452270557 1434138021248001169601459)
        ·
          refine ⟨2151207031872001754402189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434138021248001169601459 2151207031872001754402189)
          ·
            refine ⟨806702636952000657900821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2151207031872001754402189 806702636952000657900821)
            ·
              refine ⟨37814186107125030839101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 806702636952000657900821 37814186107125030839101)
              ·
                rfl

theorem cell20_745634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 6].length) (baseStart_745634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745634 prefixEnd_745634 := by exact prefixLift 745634
  have htrace : WordTrace (prefixWord ++ tailWord_745634) baseStart_745634 baseEnd_745634 := by
    simpa [prefixWord, tailWord_745634, baseEnd_745634] using wordTrace_append hprefix tailTrace_745634
  have hstable : (prefixWord ++ tailWord_745634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745634).length < 2 ^ (prefixWord ++ tailWord_745634).sum := by decide
  have hdescent : baseEnd_745634 < baseStart_745634 := by decide
  rcases family_descends (prefixWord ++ tailWord_745634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745655 : List Nat := [1, 1, 3, 1, 4, 3, 2, 5]
def baseStart_745655 : Nat := 118140960795 + 745655 * 2 ^ 59
def prefixEnd_745655 : Nat := 4983230072969 + 3 ^ 40 * 745655 * 2
def baseEnd_745655 : Nat := 113445753312114179283941

theorem tailTrace_745655 : CollatzResearch.WordTrace tailWord_745655 prefixEnd_745655 113445753312114179283941 := by
  unfold tailWord_745655
  simp only [CollatzResearch.WordTrace]
  refine ⟨27196272113626757580438419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18130848075751171720292279 27196272113626757580438419)
  ·
    refine ⟨40794408170440136370657629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27196272113626757580438419 40794408170440136370657629)
    ·
      refine ⟨15297903063915051138996611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40794408170440136370657629 15297903063915051138996611)
      ·
        refine ⟨22946854595872576708494917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15297903063915051138996611 22946854595872576708494917)
        ·
          refine ⟨4302535236726108132842797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22946854595872576708494917 4302535236726108132842797)
          ·
            refine ⟨1613450713772290549816049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4302535236726108132842797 1613450713772290549816049)
            ·
              refine ⟨1210088035329217912362037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613450713772290549816049 1210088035329217912362037)
              ·
                refine ⟨113445753312114179283941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1210088035329217912362037 113445753312114179283941)
                ·
                  rfl

theorem cell20_745655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_745655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745655 prefixEnd_745655 := by exact prefixLift 745655
  have htrace : WordTrace (prefixWord ++ tailWord_745655) baseStart_745655 baseEnd_745655 := by
    simpa [prefixWord, tailWord_745655, baseEnd_745655] using wordTrace_append hprefix tailTrace_745655
  have hstable : (prefixWord ++ tailWord_745655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745655).length < 2 ^ (prefixWord ++ tailWord_745655).sum := by decide
  have hdescent : baseEnd_745655 < baseStart_745655 := by decide
  rcases family_descends (prefixWord ++ tailWord_745655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745669 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 4]
def baseStart_745669 : Nat := 118140960795 + 745669 * 2 ^ 59
def prefixEnd_745669 : Nat := 4983230072969 + 3 ^ 40 * 745669 * 2
def baseEnd_745669 : Nat := 340343649917820711385099

theorem tailTrace_745669 : CollatzResearch.WordTrace tailWord_745669 prefixEnd_745669 340343649917820711385099 := by
  unfold tailWord_745669
  simp only [CollatzResearch.WordTrace]
  refine ⟨27196782735576037971448061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18131188490384025314298707 27196782735576037971448061)
  ·
    refine ⟨10198793525841014239293023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27196782735576037971448061 10198793525841014239293023)
    ·
      refine ⟨15298190288761521358939535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10198793525841014239293023 15298190288761521358939535)
      ·
        refine ⟨22947285433142282038409303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15298190288761521358939535 22947285433142282038409303)
        ·
          refine ⟨34420928149713423057613955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22947285433142282038409303 34420928149713423057613955)
          ·
            refine ⟨51631392224570134586420933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34420928149713423057613955 51631392224570134586420933)
            ·
              refine ⟨9680886042106900234953925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51631392224570134586420933 9680886042106900234953925)
              ·
                refine ⟨1815166132895043794053861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9680886042106900234953925 1815166132895043794053861)
                ·
                  refine ⟨340343649917820711385099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815166132895043794053861 340343649917820711385099)
                  ·
                    rfl

theorem cell20_745669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_745669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745669 prefixEnd_745669 := by exact prefixLift 745669
  have htrace : WordTrace (prefixWord ++ tailWord_745669) baseStart_745669 baseEnd_745669 := by
    simpa [prefixWord, tailWord_745669, baseEnd_745669] using wordTrace_append hprefix tailTrace_745669
  have hstable : (prefixWord ++ tailWord_745669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745669).length < 2 ^ (prefixWord ++ tailWord_745669).sum := by decide
  have hdescent : baseEnd_745669 < baseStart_745669 := by decide
  rcases family_descends (prefixWord ++ tailWord_745669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745693 : List Nat := [1, 4, 3, 2, 1, 9]
def baseStart_745693 : Nat := 118140960795 + 745693 * 2 ^ 59
def prefixEnd_745693 : Nat := 4983230072969 + 3 ^ 40 * 745693 * 2
def baseEnd_745693 : Nat := 12605726080436418317963

theorem tailTrace_745693 : CollatzResearch.WordTrace tailWord_745693 prefixEnd_745693 12605726080436418317963 := by
  unfold tailWord_745693
  simp only [CollatzResearch.WordTrace]
  refine ⟨27197658087489090070321733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18131772058326060046881155 27197658087489090070321733)
  ·
    refine ⟨5099560891404204388185325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27197658087489090070321733 5099560891404204388185325)
    ·
      refine ⟨1912335334276576645569497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5099560891404204388185325 1912335334276576645569497)
      ·
        refine ⟨1434251500707432484177123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1912335334276576645569497 1434251500707432484177123)
        ·
          refine ⟨2151377251061148726265685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434251500707432484177123 2151377251061148726265685)
          ·
            refine ⟨12605726080436418317963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2151377251061148726265685 12605726080436418317963)
            ·
              rfl

theorem cell20_745693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 9].length) (baseStart_745693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745693 prefixEnd_745693 := by exact prefixLift 745693
  have htrace : WordTrace (prefixWord ++ tailWord_745693) baseStart_745693 baseEnd_745693 := by
    simpa [prefixWord, tailWord_745693, baseEnd_745693] using wordTrace_append hprefix tailTrace_745693
  have hstable : (prefixWord ++ tailWord_745693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745693).length < 2 ^ (prefixWord ++ tailWord_745693).sum := by decide
  have hdescent : baseEnd_745693 < baseStart_745693 := by decide
  rcases family_descends (prefixWord ++ tailWord_745693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745707 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 4]
def baseStart_745707 : Nat := 118140960795 + 745707 * 2 ^ 59
def prefixEnd_745707 : Nat := 4983230072969 + 3 ^ 40 * 745707 * 2
def baseEnd_745707 : Nat := 340360994153261468118277

theorem tailTrace_745707 : CollatzResearch.WordTrace tailWord_745707 prefixEnd_745707 340360994153261468118277 := by
  unfold tailWord_745707
  simp only [CollatzResearch.WordTrace]
  refine ⟨27198168709438370461331375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18132112472958913640887583 27198168709438370461331375)
  ·
    refine ⟨40797253064157555691997063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27198168709438370461331375 40797253064157555691997063)
    ·
      refine ⟨61195879596236333537995595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40797253064157555691997063 61195879596236333537995595)
      ·
        refine ⟨91793819394354500306993393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61195879596236333537995595 91793819394354500306993393)
        ·
          refine ⟨68845364545765875230245045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91793819394354500306993393 68845364545765875230245045)
          ·
            refine ⟨6454252926165550802835473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68845364545765875230245045 6454252926165550802835473)
            ·
              refine ⟨4840689694624163102126605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6454252926165550802835473 4840689694624163102126605)
              ·
                refine ⟨1815258635484061163297477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4840689694624163102126605 1815258635484061163297477)
                ·
                  refine ⟨340360994153261468118277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815258635484061163297477 340360994153261468118277)
                  ·
                    rfl

theorem cell20_745707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_745707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745707 prefixEnd_745707 := by exact prefixLift 745707
  have htrace : WordTrace (prefixWord ++ tailWord_745707) baseStart_745707 baseEnd_745707 := by
    simpa [prefixWord, tailWord_745707, baseEnd_745707] using wordTrace_append hprefix tailTrace_745707
  have hstable : (prefixWord ++ tailWord_745707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745707).length < 2 ^ (prefixWord ++ tailWord_745707).sum := by decide
  have hdescent : baseEnd_745707 < baseStart_745707 := by decide
  rcases family_descends (prefixWord ++ tailWord_745707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745724 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_745724 : Nat := 118140960795 + 745724 * 2 ^ 59
def prefixEnd_745724 : Nat := 4983230072969 + 3 ^ 40 * 745724 * 2
def baseEnd_745724 : Nat := 340368753416484964551541

theorem tailTrace_745724 : CollatzResearch.WordTrace tailWord_745724 prefixEnd_745724 340368753416484964551541 := by
  unfold tailWord_745724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13599394375188391182350113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18132525833584521576466817 13599394375188391182350113)
  ·
    refine ⟨10199545781391293386762585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13599394375188391182350113 10199545781391293386762585)
    ·
      refine ⟨7649659336043470040071939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10199545781391293386762585 7649659336043470040071939)
      ·
        refine ⟨11474489004065205060107909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7649659336043470040071939 11474489004065205060107909)
        ·
          refine ⟨2151466688262225948770233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11474489004065205060107909 2151466688262225948770233)
          ·
            refine ⟨1613600016196669461577675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151466688262225948770233 1613600016196669461577675)
            ·
              refine ⟨2420400024295004192366513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613600016196669461577675 2420400024295004192366513)
              ·
                refine ⟨1815300018221253144274885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2420400024295004192366513 1815300018221253144274885)
                ·
                  refine ⟨340368753416484964551541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815300018221253144274885 340368753416484964551541)
                  ·
                    rfl

theorem cell20_745724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_745724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745724 prefixEnd_745724 := by exact prefixLift 745724
  have htrace : WordTrace (prefixWord ++ tailWord_745724) baseStart_745724 baseEnd_745724 := by
    simpa [prefixWord, tailWord_745724, baseEnd_745724] using wordTrace_append hprefix tailTrace_745724
  have hstable : (prefixWord ++ tailWord_745724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745724).length < 2 ^ (prefixWord ++ tailWord_745724).sum := by decide
  have hdescent : baseEnd_745724 < baseStart_745724 := by decide
  rcases family_descends (prefixWord ++ tailWord_745724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745731 : List Nat := [1, 1, 1, 3, 2, 3, 5, 4]
def baseStart_745731 : Nat := 118140960795 + 745731 * 2 ^ 59
def prefixEnd_745731 : Nat := 4983230072969 + 3 ^ 40 * 745731 * 2
def baseEnd_745731 : Nat := 113457316135741350439393

theorem tailTrace_745731 : CollatzResearch.WordTrace tailWord_745731 prefixEnd_745731 113457316135741350439393 := by
  unfold tailWord_745731
  simp only [CollatzResearch.WordTrace]
  refine ⟨27199044061351422560205047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18132696040900948373470031 27199044061351422560205047)
  ·
    refine ⟨40798566092027133840307571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27199044061351422560205047 40798566092027133840307571)
    ·
      refine ⟨61197849138040700760461357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40798566092027133840307571 61197849138040700760461357)
      ·
        refine ⟨22949193426765262785173009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61197849138040700760461357 22949193426765262785173009)
        ·
          refine ⟨17211895070073947088879757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22949193426765262785173009 17211895070073947088879757)
          ·
            refine ⟨6454460651277730158329909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17211895070073947088879757 6454460651277730158329909)
            ·
              refine ⟨605105686057287202343429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6454460651277730158329909 605105686057287202343429)
              ·
                refine ⟨113457316135741350439393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 605105686057287202343429 113457316135741350439393)
                ·
                  rfl

theorem cell20_745731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 4].length) (baseStart_745731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745731 prefixEnd_745731 := by exact prefixLift 745731
  have htrace : WordTrace (prefixWord ++ tailWord_745731) baseStart_745731 baseEnd_745731 := by
    simpa [prefixWord, tailWord_745731, baseEnd_745731] using wordTrace_append hprefix tailTrace_745731
  have hstable : (prefixWord ++ tailWord_745731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745731).length < 2 ^ (prefixWord ++ tailWord_745731).sum := by decide
  have hdescent : baseEnd_745731 < baseStart_745731 := by decide
  rcases family_descends (prefixWord ++ tailWord_745731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745752 : List Nat := [2, 1, 2, 3, 1, 2, 9]
def baseStart_745752 : Nat := 118140960795 + 745752 * 2 ^ 59
def prefixEnd_745752 : Nat := 4983230072969 + 3 ^ 40 * 745752 * 2
def baseEnd_745752 : Nat := 37820170375493479068677

theorem tailTrace_745752 : CollatzResearch.WordTrace tailWord_745752 prefixEnd_745752 37820170375493479068677 := by
  unfold tailWord_745752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13599904997137671573359755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18133206662850228764479673 13599904997137671573359755)
  ·
    refine ⟨20399857495706507360039633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13599904997137671573359755 20399857495706507360039633)
    ·
      refine ⟨15299893121779880520029725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20399857495706507360039633 15299893121779880520029725)
      ·
        refine ⟨5737459920667455195011147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15299893121779880520029725 5737459920667455195011147)
        ·
          refine ⟨8606189881001182792516721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5737459920667455195011147 8606189881001182792516721)
          ·
            refine ⟨6454642410750887094387541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8606189881001182792516721 6454642410750887094387541)
            ·
              refine ⟨37820170375493479068677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6454642410750887094387541 37820170375493479068677)
              ·
                rfl

theorem cell20_745752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 9].length) (baseStart_745752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745752 prefixEnd_745752 := by exact prefixLift 745752
  have htrace : WordTrace (prefixWord ++ tailWord_745752) baseStart_745752 baseEnd_745752 := by
    simpa [prefixWord, tailWord_745752, baseEnd_745752] using wordTrace_append hprefix tailTrace_745752
  have hstable : (prefixWord ++ tailWord_745752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745752).length < 2 ^ (prefixWord ++ tailWord_745752).sum := by decide
  have hdescent : baseEnd_745752 < baseStart_745752 := by decide
  rcases family_descends (prefixWord ++ tailWord_745752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745758 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_745758 : Nat := 118140960795 + 745758 * 2 ^ 59
def prefixEnd_745758 : Nat := 4983230072969 + 3 ^ 40 * 745758 * 2
def baseEnd_745758 : Nat := 340384271942931957418069

theorem tailTrace_745758 : CollatzResearch.WordTrace tailWord_745758 prefixEnd_745758 340384271942931957418069 := by
  unfold tailWord_745758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400003604031700771429741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18133352554835737447625285 3400003604031700771429741)
  ·
    refine ⟨1275001351511887789286153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3400003604031700771429741 1275001351511887789286153)
    ·
      refine ⟨956251013633915841964615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1275001351511887789286153 956251013633915841964615)
      ·
        refine ⟨1434376520450873762946923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956251013633915841964615 1434376520450873762946923)
        ·
          refine ⟨2151564780676310644420385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434376520450873762946923 2151564780676310644420385)
          ·
            refine ⟨1613673585507232983315289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151564780676310644420385 1613673585507232983315289)
            ·
              refine ⟨1210255189130424737486467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613673585507232983315289 1210255189130424737486467)
              ·
                refine ⟨1815382783695637106229701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210255189130424737486467 1815382783695637106229701)
                ·
                  refine ⟨340384271942931957418069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815382783695637106229701 340384271942931957418069)
                  ·
                    rfl

theorem cell20_745758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_745758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745758 prefixEnd_745758 := by exact prefixLift 745758
  have htrace : WordTrace (prefixWord ++ tailWord_745758) baseStart_745758 baseEnd_745758 := by
    simpa [prefixWord, tailWord_745758, baseEnd_745758] using wordTrace_append hprefix tailTrace_745758
  have hstable : (prefixWord ++ tailWord_745758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745758).length < 2 ^ (prefixWord ++ tailWord_745758).sum := by decide
  have hdescent : baseEnd_745758 < baseStart_745758 := by decide
  rcases family_descends (prefixWord ++ tailWord_745758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745762 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_745762 : Nat := 118140960795 + 745762 * 2 ^ 59
def prefixEnd_745762 : Nat := 4983230072969 + 3 ^ 40 * 745762 * 2
def baseEnd_745762 : Nat := 340386097651925721284719

theorem tailTrace_745762 : CollatzResearch.WordTrace tailWord_745762 prefixEnd_745762 340386097651925721284719 := by
  unfold tailWord_745762
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800043681059778713645885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18133449816159409903055693 6800043681059778713645885)
  ·
    refine ⟨2550016380397417017617207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6800043681059778713645885 2550016380397417017617207)
    ·
      refine ⟨3825024570596125526425811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2550016380397417017617207 3825024570596125526425811)
      ·
        refine ⟨5737536855894188289638717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825024570596125526425811 5737536855894188289638717)
        ·
          refine ⟨2151576320960320608614519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5737536855894188289638717 2151576320960320608614519)
          ·
            refine ⟨3227364481440480912921779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151576320960320608614519 3227364481440480912921779)
            ·
              refine ⟨4841046722160721369382669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227364481440480912921779 4841046722160721369382669)
              ·
                refine ⟨1815392520810270513518501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4841046722160721369382669 1815392520810270513518501)
                ·
                  refine ⟨340386097651925721284719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815392520810270513518501 340386097651925721284719)
                  ·
                    rfl

theorem cell20_745762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_745762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745762 prefixEnd_745762 := by exact prefixLift 745762
  have htrace : WordTrace (prefixWord ++ tailWord_745762) baseStart_745762 baseEnd_745762 := by
    simpa [prefixWord, tailWord_745762, baseEnd_745762] using wordTrace_append hprefix tailTrace_745762
  have hstable : (prefixWord ++ tailWord_745762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745762).length < 2 ^ (prefixWord ++ tailWord_745762).sum := by decide
  have hdescent : baseEnd_745762 < baseStart_745762 := by decide
  rcases family_descends (prefixWord ++ tailWord_745762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745786 : List Nat := [3, 1, 1, 1, 4, 4, 2, 4]
def baseStart_745786 : Nat := 118140960795 + 745786 * 2 ^ 59
def prefixEnd_745786 : Nat := 4983230072969 + 3 ^ 40 * 745786 * 2
def baseEnd_745786 : Nat := 113465683968629434828207

theorem tailTrace_745786 : CollatzResearch.WordTrace tailWord_745786 prefixEnd_745786 113465683968629434828207 := by
  unfold tailWord_745786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800262519038041738364303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18134033384101444635638141 6800262519038041738364303)
  ·
    refine ⟨10200393778557062607546455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6800262519038041738364303 10200393778557062607546455)
    ·
      refine ⟨15300590667835593911319683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10200393778557062607546455 15300590667835593911319683)
      ·
        refine ⟨22950886001753390866979525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15300590667835593911319683 22950886001753390866979525)
        ·
          refine ⟨4303291125328760787558661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22950886001753390866979525 4303291125328760787558661)
          ·
            refine ⟨806867085999142647667249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4303291125328760787558661 806867085999142647667249)
            ·
              refine ⟨605150314499356985750437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806867085999142647667249 605150314499356985750437)
              ·
                refine ⟨113465683968629434828207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 605150314499356985750437 113465683968629434828207)
                ·
                  rfl

theorem cell20_745786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_745786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745786 prefixEnd_745786 := by exact prefixLift 745786
  have htrace : WordTrace (prefixWord ++ tailWord_745786) baseStart_745786 baseEnd_745786 := by
    simpa [prefixWord, tailWord_745786, baseEnd_745786] using wordTrace_append hprefix tailTrace_745786
  have hstable : (prefixWord ++ tailWord_745786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745786).length < 2 ^ (prefixWord ++ tailWord_745786).sum := by decide
  have hdescent : baseEnd_745786 < baseStart_745786 := by decide
  rcases family_descends (prefixWord ++ tailWord_745786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745831 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 3]
def baseStart_745831 : Nat := 118140960795 + 745831 * 2 ^ 59
def prefixEnd_745831 : Nat := 4983230072969 + 3 ^ 40 * 745831 * 2
def baseEnd_745831 : Nat := 340417591132068147984437

theorem tailTrace_745831 : CollatzResearch.WordTrace tailWord_745831 prefixEnd_745831 340417591132068147984437 := by
  unfold tailWord_745831
  simp only [CollatzResearch.WordTrace]
  refine ⟨27202691360989139638845347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18135127573992759759230231 27202691360989139638845347)
  ·
    refine ⟨40804037041483709458268021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27202691360989139638845347 40804037041483709458268021)
    ·
      refine ⟨3825378472639097761712627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40804037041483709458268021 3825378472639097761712627)
      ·
        refine ⟨5738067708958646642568941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825378472639097761712627 5738067708958646642568941)
        ·
          refine ⟨2151775390859492490963353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5738067708958646642568941 2151775390859492490963353)
          ·
            refine ⟨1613831543144619368222515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151775390859492490963353 1613831543144619368222515)
            ·
              refine ⟨2420747314716929052333773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613831543144619368222515 2420747314716929052333773)
              ·
                refine ⟨907780243018848394625165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2420747314716929052333773 907780243018848394625165)
                ·
                  refine ⟨340417591132068147984437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907780243018848394625165 340417591132068147984437)
                  ·
                    rfl

theorem cell20_745831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 3].length) (baseStart_745831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745831 prefixEnd_745831 := by exact prefixLift 745831
  have htrace : WordTrace (prefixWord ++ tailWord_745831) baseStart_745831 baseEnd_745831 := by
    simpa [prefixWord, tailWord_745831, baseEnd_745831] using wordTrace_append hprefix tailTrace_745831
  have hstable : (prefixWord ++ tailWord_745831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745831).length < 2 ^ (prefixWord ++ tailWord_745831).sum := by decide
  have hdescent : baseEnd_745831 < baseStart_745831 := by decide
  rcases family_descends (prefixWord ++ tailWord_745831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745845 : List Nat := [1, 3, 4, 1, 2, 1, 2, 6]
def baseStart_745845 : Nat := 118140960795 + 745845 * 2 ^ 59
def prefixEnd_745845 : Nat := 4983230072969 + 3 ^ 40 * 745845 * 2
def baseEnd_745845 : Nat := 113474660371182107172571

theorem tailTrace_745845 : CollatzResearch.WordTrace tailWord_745845 prefixEnd_745845 113474660371182107172571 := by
  unfold tailWord_745845
  simp only [CollatzResearch.WordTrace]
  refine ⟨27203201982938420029854989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18135467988625613353236659 27203201982938420029854989)
  ·
    refine ⟨10201200743601907511195621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27203201982938420029854989 10201200743601907511195621)
    ·
      refine ⟨1912725139425357658349179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10201200743601907511195621 1912725139425357658349179)
      ·
        refine ⟨2869087709138036487523769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912725139425357658349179 2869087709138036487523769)
        ·
          refine ⟨2151815781853527365642827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2869087709138036487523769 2151815781853527365642827)
          ·
            refine ⟨3227723672780291048464241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151815781853527365642827 3227723672780291048464241)
            ·
              refine ⟨2420792754585218286348181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3227723672780291048464241 2420792754585218286348181)
              ·
                refine ⟨113474660371182107172571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2420792754585218286348181 113474660371182107172571)
                ·
                  rfl

theorem cell20_745845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_745845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745845 prefixEnd_745845 := by exact prefixLift 745845
  have htrace : WordTrace (prefixWord ++ tailWord_745845) baseStart_745845 baseEnd_745845 := by
    simpa [prefixWord, tailWord_745845, baseEnd_745845] using wordTrace_append hprefix tailTrace_745845
  have hstable : (prefixWord ++ tailWord_745845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745845).length < 2 ^ (prefixWord ++ tailWord_745845).sum := by decide
  have hdescent : baseEnd_745845 < baseStart_745845 := by decide
  rcases family_descends (prefixWord ++ tailWord_745845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745886 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_745886 : Nat := 118140960795 + 745886 * 2 ^ 59
def prefixEnd_745886 : Nat := 4983230072969 + 3 ^ 40 * 745886 * 2
def baseEnd_745886 : Nat := 340442694630732401150879

theorem tailTrace_745886 : CollatzResearch.WordTrace tailWord_745886 prefixEnd_745886 340442694630732401150879 := by
  unfold tailWord_745886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400587171973735504012189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18136464917193256021398341 3400587171973735504012189)
  ·
    refine ⟨1275220189490150814004571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3400587171973735504012189 1275220189490150814004571)
    ·
      refine ⟨1912830284235226221006857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275220189490150814004571 1912830284235226221006857)
      ·
        refine ⟨1434622713176419665755143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1912830284235226221006857 1434622713176419665755143)
        ·
          refine ⟨2151934069764629498632715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434622713176419665755143 2151934069764629498632715)
          ·
            refine ⟨3227901104646944247949073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151934069764629498632715 3227901104646944247949073)
            ·
              refine ⟨2420925828485208185961805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3227901104646944247949073 2420925828485208185961805)
              ·
                refine ⟨907847185681953069735677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2420925828485208185961805 907847185681953069735677)
                ·
                  refine ⟨340442694630732401150879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907847185681953069735677 340442694630732401150879)
                  ·
                    rfl

theorem cell20_745886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_745886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745886 prefixEnd_745886 := by exact prefixLift 745886
  have htrace : WordTrace (prefixWord ++ tailWord_745886) baseStart_745886 baseEnd_745886 := by
    simpa [prefixWord, tailWord_745886, baseEnd_745886] using wordTrace_append hprefix tailTrace_745886
  have hstable : (prefixWord ++ tailWord_745886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745886).length < 2 ^ (prefixWord ++ tailWord_745886).sum := by decide
  have hdescent : baseEnd_745886 < baseStart_745886 := by decide
  rcases family_descends (prefixWord ++ tailWord_745886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745928 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_745928 : Nat := 118140960795 + 745928 * 2 ^ 59
def prefixEnd_745928 : Nat := 4983230072969 + 3 ^ 40 * 745928 * 2
def baseEnd_745928 : Nat := 340461864575166921750707

theorem tailTrace_745928 : CollatzResearch.WordTrace tailWord_745928 prefixEnd_745928 340461864575166921750707 := by
  unfold tailWord_745928
  simp only [CollatzResearch.WordTrace]
  refine ⟨13603114620818862602563219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18137486161091816803417625 13603114620818862602563219)
  ·
    refine ⟨20404671931228293903844829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13603114620818862602563219 20404671931228293903844829)
    ·
      refine ⟨7651751974210610213941811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20404671931228293903844829 7651751974210610213941811)
      ·
        refine ⟨11477627961315915320912717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7651751974210610213941811 11477627961315915320912717)
        ·
          refine ⟨4304110485493468245342269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11477627961315915320912717 4304110485493468245342269)
          ·
            refine ⟨1614041432060050592003351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4304110485493468245342269 1614041432060050592003351)
            ·
              refine ⟨2421062148090075888005027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614041432060050592003351 2421062148090075888005027)
              ·
                refine ⟨3631593222135113832007541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421062148090075888005027 3631593222135113832007541)
                ·
                  refine ⟨340461864575166921750707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3631593222135113832007541 340461864575166921750707)
                  ·
                    rfl

theorem cell20_745928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_745928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745928 prefixEnd_745928 := by exact prefixLift 745928
  have htrace : WordTrace (prefixWord ++ tailWord_745928) baseStart_745928 baseEnd_745928 := by
    simpa [prefixWord, tailWord_745928, baseEnd_745928] using wordTrace_append hprefix tailTrace_745928
  have hstable : (prefixWord ++ tailWord_745928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745928).length < 2 ^ (prefixWord ++ tailWord_745928).sum := by decide
  have hdescent : baseEnd_745928 < baseStart_745928 := by decide
  rcases family_descends (prefixWord ++ tailWord_745928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745945 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 3]
def baseStart_745945 : Nat := 118140960795 + 745945 * 2 ^ 59
def prefixEnd_745945 : Nat := 4983230072969 + 3 ^ 40 * 745945 * 2
def baseEnd_745945 : Nat := 340469623838390418183971

theorem tailTrace_745945 : CollatzResearch.WordTrace tailWord_745945 prefixEnd_745945 340469623838390418183971 := by
  unfold tailWord_745945
  simp only [CollatzResearch.WordTrace]
  refine ⟨27206849282576137108495289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18137899521717424738996859 27206849282576137108495289)
  ·
    refine ⟨20405136961932102831371467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27206849282576137108495289 20405136961932102831371467)
    ·
      refine ⟨30607705442898154247057201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20405136961932102831371467 30607705442898154247057201)
      ·
        refine ⟨22955779082173615685292901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30607705442898154247057201 22955779082173615685292901)
        ·
          refine ⟨4304208577907552940992419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22955779082173615685292901 4304208577907552940992419)
          ·
            refine ⟨6456312866861329411488629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304208577907552940992419 6456312866861329411488629)
            ·
              refine ⟨605279331268249632327059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6456312866861329411488629 605279331268249632327059)
              ·
                refine ⟨907918996902374448490589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605279331268249632327059 907918996902374448490589)
                ·
                  refine ⟨340469623838390418183971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 907918996902374448490589 340469623838390418183971)
                  ·
                    rfl

theorem cell20_745945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_745945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745945 prefixEnd_745945 := by exact prefixLift 745945
  have htrace : WordTrace (prefixWord ++ tailWord_745945) baseStart_745945 baseEnd_745945 := by
    simpa [prefixWord, tailWord_745945, baseEnd_745945] using wordTrace_append hprefix tailTrace_745945
  have hstable : (prefixWord ++ tailWord_745945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745945).length < 2 ^ (prefixWord ++ tailWord_745945).sum := by decide
  have hdescent : baseEnd_745945 < baseStart_745945 := by decide
  rcases family_descends (prefixWord ++ tailWord_745945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745955 : List Nat := [1, 1, 1, 6, 4, 1, 2, 4]
def baseStart_745955 : Nat := 118140960795 + 745955 * 2 ^ 59
def prefixEnd_745955 : Nat := 4983230072969 + 3 ^ 40 * 745955 * 2
def baseEnd_745955 : Nat := 113491396036958275950199

theorem tailTrace_745955 : CollatzResearch.WordTrace tailWord_745955 prefixEnd_745955 113491396036958275950199 := by
  unfold tailWord_745955
  simp only [CollatzResearch.WordTrace]
  refine ⟨27207214012539908816359319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18138142675026605877572879 27207214012539908816359319)
  ·
    refine ⟨40810821018809863224538979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27207214012539908816359319 40810821018809863224538979)
    ·
      refine ⟨61216231528214794836808469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40810821018809863224538979 61216231528214794836808469)
      ·
        refine ⟨2869510852885068507975397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61216231528214794836808469 2869510852885068507975397)
        ·
          refine ⟨538033284915950345245387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2869510852885068507975397 538033284915950345245387)
          ·
            refine ⟨807049927373925517868081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538033284915950345245387 807049927373925517868081)
            ·
              refine ⟨605287445530444138401061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 807049927373925517868081 605287445530444138401061)
              ·
                refine ⟨113491396036958275950199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 605287445530444138401061 113491396036958275950199)
                ·
                  rfl

theorem cell20_745955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 4].length) (baseStart_745955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745955 prefixEnd_745955 := by exact prefixLift 745955
  have htrace : WordTrace (prefixWord ++ tailWord_745955) baseStart_745955 baseEnd_745955 := by
    simpa [prefixWord, tailWord_745955, baseEnd_745955] using wordTrace_append hprefix tailTrace_745955
  have hstable : (prefixWord ++ tailWord_745955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745955).length < 2 ^ (prefixWord ++ tailWord_745955).sum := by decide
  have hdescent : baseEnd_745955 < baseStart_745955 := by decide
  rcases family_descends (prefixWord ++ tailWord_745955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745966 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_745966 : Nat := 118140960795 + 745966 * 2 ^ 59
def prefixEnd_745966 : Nat := 4983230072969 + 3 ^ 40 * 745966 * 2
def baseEnd_745966 : Nat := 340479208810607678483885

theorem tailTrace_745966 : CollatzResearch.WordTrace tailWord_745966 prefixEnd_745966 340479208810607678483885 := by
  unfold tailWord_745966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400951901937507211876219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18138410143666705130006501 3400951901937507211876219)
  ·
    refine ⟨5101427852906260817814329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3400951901937507211876219 5101427852906260817814329)
    ·
      refine ⟨3826070889679695613360747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5101427852906260817814329 3826070889679695613360747)
      ·
        refine ⟨5739106334519543420041121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3826070889679695613360747 5739106334519543420041121)
        ·
          refine ⟨4304329750889657565030841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5739106334519543420041121 4304329750889657565030841)
          ·
            refine ⟨3228247313167243173773131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4304329750889657565030841 3228247313167243173773131)
            ·
              refine ⟨4842370969750864760659697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228247313167243173773131 4842370969750864760659697)
              ·
                refine ⟨3631778227313148570494773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4842370969750864760659697 3631778227313148570494773)
                ·
                  refine ⟨340479208810607678483885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3631778227313148570494773 340479208810607678483885)
                  ·
                    rfl

theorem cell20_745966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_745966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745966 prefixEnd_745966 := by exact prefixLift 745966
  have htrace : WordTrace (prefixWord ++ tailWord_745966) baseStart_745966 baseEnd_745966 := by
    simpa [prefixWord, tailWord_745966, baseEnd_745966] using wordTrace_append hprefix tailTrace_745966
  have hstable : (prefixWord ++ tailWord_745966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745966).length < 2 ^ (prefixWord ++ tailWord_745966).sum := by decide
  have hdescent : baseEnd_745966 < baseStart_745966 := by decide
  rcases family_descends (prefixWord ++ tailWord_745966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745986 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_745986 : Nat := 118140960795 + 745986 * 2 ^ 59
def prefixEnd_745986 : Nat := 4983230072969 + 3 ^ 40 * 745986 * 2
def baseEnd_745986 : Nat := 340488337355576497817137

theorem tailTrace_745986 : CollatzResearch.WordTrace tailWord_745986 prefixEnd_745986 340488337355576497817137 := by
  unfold tailWord_745986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6802086168856900277684453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18138896450285067407158541 6802086168856900277684453)
  ·
    refine ⟨1275391156660668802065835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6802086168856900277684453 1275391156660668802065835)
    ·
      refine ⟨1913086734991003203098753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275391156660668802065835 1913086734991003203098753)
      ·
        refine ⟨1434815051243252402324065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1913086734991003203098753 1434815051243252402324065)
        ·
          refine ⟨1076111288432439301743049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1434815051243252402324065 1076111288432439301743049)
          ·
            refine ⟨807083466324329476307287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1076111288432439301743049 807083466324329476307287)
            ·
              refine ⟨1210625199486494214460931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807083466324329476307287 1210625199486494214460931)
              ·
                refine ⟨1815937799229741321691397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210625199486494214460931 1815937799229741321691397)
                ·
                  refine ⟨340488337355576497817137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815937799229741321691397 340488337355576497817137)
                  ·
                    rfl

theorem cell20_745986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_745986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745986 prefixEnd_745986 := by exact prefixLift 745986
  have htrace : WordTrace (prefixWord ++ tailWord_745986) baseStart_745986 baseEnd_745986 := by
    simpa [prefixWord, tailWord_745986, baseEnd_745986] using wordTrace_append hprefix tailTrace_745986
  have hstable : (prefixWord ++ tailWord_745986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745986).length < 2 ^ (prefixWord ++ tailWord_745986).sum := by decide
  have hdescent : baseEnd_745986 < baseStart_745986 := by decide
  rcases family_descends (prefixWord ++ tailWord_745986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745987 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_745987 : Nat := 118140960795 + 745987 * 2 ^ 59
def prefixEnd_745987 : Nat := 4983230072969 + 3 ^ 40 * 745987 * 2
def baseEnd_745987 : Nat := 340488793782824938783799

theorem tailTrace_745987 : CollatzResearch.WordTrace tailWord_745987 prefixEnd_745987 340488793782824938783799 := by
  unfold tailWord_745987
  simp only [CollatzResearch.WordTrace]
  refine ⟨27208381148423978281524215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18138920765615985521016143 27208381148423978281524215)
  ·
    refine ⟨40812571722635967422286323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27208381148423978281524215 40812571722635967422286323)
    ·
      refine ⟨61218857583953951133429485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40812571722635967422286323 61218857583953951133429485)
      ·
        refine ⟨22957071593982731675036057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61218857583953951133429485 22957071593982731675036057)
        ·
          refine ⟨17217803695487048756277043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22957071593982731675036057 17217803695487048756277043)
          ·
            refine ⟨25826705543230573134415565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17217803695487048756277043 25826705543230573134415565)
            ·
              refine ⟨9685014578711464925405837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25826705543230573134415565 9685014578711464925405837)
              ·
                refine ⟨3631880467016799347027189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9685014578711464925405837 3631880467016799347027189)
                ·
                  refine ⟨340488793782824938783799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3631880467016799347027189 340488793782824938783799)
                  ·
                    rfl

theorem cell20_745987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_745987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_745987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_745987 prefixEnd_745987 := by exact prefixLift 745987
  have htrace : WordTrace (prefixWord ++ tailWord_745987) baseStart_745987 baseEnd_745987 := by
    simpa [prefixWord, tailWord_745987, baseEnd_745987] using wordTrace_append hprefix tailTrace_745987
  have hstable : (prefixWord ++ tailWord_745987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745987).length < 2 ^ (prefixWord ++ tailWord_745987).sum := by decide
  have hdescent : baseEnd_745987 < baseStart_745987 := by decide
  rcases family_descends (prefixWord ++ tailWord_745987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746038 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_746038 : Nat := 118140960795 + 746038 * 2 ^ 59
def prefixEnd_746038 : Nat := 4983230072969 + 3 ^ 40 * 746038 * 2
def baseEnd_746038 : Nat := 340512071572495428083591

theorem tailTrace_746038 : CollatzResearch.WordTrace tailWord_746038 prefixEnd_746038 340512071572495428083591 := by
  unfold tailWord_746038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1700640079452450874476923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18140160847492809327753845 1700640079452450874476923)
  ·
    refine ⟨2550960119178676311715385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1700640079452450874476923 2550960119178676311715385)
    ·
      refine ⟨1913220089384007233786539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2550960119178676311715385 1913220089384007233786539)
      ·
        refine ⟨2869830134076010850679809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913220089384007233786539 2869830134076010850679809)
        ·
          refine ⟨2152372600557008138009857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2869830134076010850679809 2152372600557008138009857)
          ·
            refine ⟨1614279450417756103507393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2152372600557008138009857 1614279450417756103507393)
            ·
              refine ⟨1210709587813317077630545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1614279450417756103507393 1210709587813317077630545)
              ·
                refine ⟨908032190859987808222909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1210709587813317077630545 908032190859987808222909)
                ·
                  refine ⟨340512071572495428083591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908032190859987808222909 340512071572495428083591)
                  ·
                    rfl

theorem cell20_746038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_746038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746038 prefixEnd_746038 := by exact prefixLift 746038
  have htrace : WordTrace (prefixWord ++ tailWord_746038) baseStart_746038 baseEnd_746038 := by
    simpa [prefixWord, tailWord_746038, baseEnd_746038] using wordTrace_append hprefix tailTrace_746038
  have hstable : (prefixWord ++ tailWord_746038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746038).length < 2 ^ (prefixWord ++ tailWord_746038).sum := by decide
  have hdescent : baseEnd_746038 < baseStart_746038 := by decide
  rcases family_descends (prefixWord ++ tailWord_746038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746042 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_746042 : Nat := 118140960795 + 746042 * 2 ^ 59
def prefixEnd_746042 : Nat := 4983230072969 + 3 ^ 40 * 746042 * 2
def baseEnd_746042 : Nat := 340513897281489191950241

theorem tailTrace_746042 : CollatzResearch.WordTrace tailWord_746042 prefixEnd_746042 340513897281489191950241 := by
  unfold tailWord_746042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6802596790806180668694095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18140258108816481783184253 6802596790806180668694095)
  ·
    refine ⟨10203895186209271003041143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6802596790806180668694095 10203895186209271003041143)
    ·
      refine ⟨15305842779313906504561715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10203895186209271003041143 15305842779313906504561715)
      ·
        refine ⟨22958764168970859756842573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15305842779313906504561715 22958764168970859756842573)
        ·
          refine ⟨8609536563364072408815965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22958764168970859756842573 8609536563364072408815965)
          ·
            refine ⟨3228576211261527153305987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8609536563364072408815965 3228576211261527153305987)
            ·
              refine ⟨4842864316892290729958981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228576211261527153305987 4842864316892290729958981)
              ·
                refine ⟨908037059417304511867309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4842864316892290729958981 908037059417304511867309)
                ·
                  refine ⟨340513897281489191950241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908037059417304511867309 340513897281489191950241)
                  ·
                    rfl

theorem cell20_746042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_746042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746042 prefixEnd_746042 := by exact prefixLift 746042
  have htrace : WordTrace (prefixWord ++ tailWord_746042) baseStart_746042 baseEnd_746042 := by
    simpa [prefixWord, tailWord_746042, baseEnd_746042] using wordTrace_append hprefix tailTrace_746042
  have hstable : (prefixWord ++ tailWord_746042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746042).length < 2 ^ (prefixWord ++ tailWord_746042).sum := by decide
  have hdescent : baseEnd_746042 < baseStart_746042 := by decide
  rcases family_descends (prefixWord ++ tailWord_746042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746045 : List Nat := [1, 4, 1, 3, 2, 2, 1, 4, 2]
def baseStart_746045 : Nat := 118140960795 + 746045 * 2 ^ 59
def prefixEnd_746045 : Nat := 4983230072969 + 3 ^ 40 * 746045 * 2
def baseEnd_746045 : Nat := 340515266563234514850229

theorem tailTrace_746045 : CollatzResearch.WordTrace tailWord_746045 prefixEnd_746045 340515266563234514850229 := by
  unfold tailWord_746045
  simp only [CollatzResearch.WordTrace]
  refine ⟨27210496582213854187135589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18140331054809236124757059 27210496582213854187135589)
  ·
    refine ⟨5101968109165097660087923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27210496582213854187135589 5101968109165097660087923)
    ·
      refine ⟨7652952163747646490131885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5101968109165097660087923 7652952163747646490131885)
      ·
        refine ⟨2869857061405367433799457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7652952163747646490131885 2869857061405367433799457)
        ·
          refine ⟨2152392796054025575349593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2869857061405367433799457 2152392796054025575349593)
          ·
            refine ⟨1614294597040519181512195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2152392796054025575349593 1614294597040519181512195)
            ·
              refine ⟨2421441895560778772268293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614294597040519181512195 2421441895560778772268293)
              ·
                refine ⟨454020355417646019800305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2421441895560778772268293 454020355417646019800305)
                ·
                  refine ⟨340515266563234514850229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454020355417646019800305 340515266563234514850229)
                  ·
                    rfl

theorem cell20_746045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_746045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746045 prefixEnd_746045 := by exact prefixLift 746045
  have htrace : WordTrace (prefixWord ++ tailWord_746045) baseStart_746045 baseEnd_746045 := by
    simpa [prefixWord, tailWord_746045, baseEnd_746045] using wordTrace_append hprefix tailTrace_746045
  have hstable : (prefixWord ++ tailWord_746045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746045).length < 2 ^ (prefixWord ++ tailWord_746045).sum := by decide
  have hdescent : baseEnd_746045 < baseStart_746045 := by decide
  rcases family_descends (prefixWord ++ tailWord_746045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746159 : List Nat := [1, 1, 2, 1, 2, 6, 3, 2, 2]
def baseStart_746159 : Nat := 118140960795 + 746159 * 2 ^ 59
def prefixEnd_746159 : Nat := 4983230072969 + 3 ^ 40 * 746159 * 2
def baseEnd_746159 : Nat := 340567299269556785049763

theorem tailTrace_746159 : CollatzResearch.WordTrace tailWord_746159 prefixEnd_746159 340567299269556785049763 := by
  unfold tailWord_746159
  simp only [CollatzResearch.WordTrace]
  refine ⟨27214654503800851656785531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18143103002533901104523687 27214654503800851656785531)
  ·
    refine ⟨40821981755701277485178297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27214654503800851656785531 40821981755701277485178297)
    ·
      refine ⟨30616486316775958113883723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40821981755701277485178297 30616486316775958113883723)
      ·
        refine ⟨45924729475163937170825585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30616486316775958113883723 45924729475163937170825585)
        ·
          refine ⟨34443547106372952878119189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45924729475163937170825585 34443547106372952878119189)
          ·
            refine ⟨1614541270611232166161837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34443547106372952878119189 1614541270611232166161837)
            ·
              refine ⟨605452976479212062310689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1614541270611232166161837 605452976479212062310689)
              ·
                refine ⟨454089732359409046733017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605452976479212062310689 454089732359409046733017)
                ·
                  refine ⟨340567299269556785049763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454089732359409046733017 340567299269556785049763)
                  ·
                    rfl

theorem cell20_746159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 2].length) (baseStart_746159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746159 prefixEnd_746159 := by exact prefixLift 746159
  have htrace : WordTrace (prefixWord ++ tailWord_746159) baseStart_746159 baseEnd_746159 := by
    simpa [prefixWord, tailWord_746159, baseEnd_746159] using wordTrace_append hprefix tailTrace_746159
  have hstable : (prefixWord ++ tailWord_746159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746159).length < 2 ^ (prefixWord ++ tailWord_746159).sum := by decide
  have hdescent : baseEnd_746159 < baseStart_746159 := by decide
  rcases family_descends (prefixWord ++ tailWord_746159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746163 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 4]
def baseStart_746163 : Nat := 118140960795 + 746163 * 2 ^ 59
def prefixEnd_746163 : Nat := 4983230072969 + 3 ^ 40 * 746163 * 2
def baseEnd_746163 : Nat := 340569124978550548916413

theorem tailTrace_746163 : CollatzResearch.WordTrace tailWord_746163 prefixEnd_746163 340569124978550548916413 := by
  unfold tailWord_746163
  simp only [CollatzResearch.WordTrace]
  refine ⟨27214800395786360339931143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18143200263857573559954095 27214800395786360339931143)
  ·
    refine ⟨40822200593679540509896715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27214800395786360339931143 40822200593679540509896715)
    ·
      refine ⟨61233300890519310764845073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40822200593679540509896715 61233300890519310764845073)
      ·
        refine ⟨45924975667889483073633805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61233300890519310764845073 45924975667889483073633805)
        ·
          refine ⟨17221865875458556152612677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45924975667889483073633805 17221865875458556152612677)
          ·
            refine ⟨3229099851648479278614877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17221865875458556152612677 3229099851648479278614877)
            ·
              refine ⟨1210912444368179729480579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3229099851648479278614877 1210912444368179729480579)
              ·
                refine ⟨1816368666552269594220869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210912444368179729480579 1816368666552269594220869)
                ·
                  refine ⟨340569124978550548916413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816368666552269594220869 340569124978550548916413)
                  ·
                    rfl

theorem cell20_746163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_746163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746163 prefixEnd_746163 := by exact prefixLift 746163
  have htrace : WordTrace (prefixWord ++ tailWord_746163) baseStart_746163 baseEnd_746163 := by
    simpa [prefixWord, tailWord_746163, baseEnd_746163] using wordTrace_append hprefix tailTrace_746163
  have hstable : (prefixWord ++ tailWord_746163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746163).length < 2 ^ (prefixWord ++ tailWord_746163).sum := by decide
  have hdescent : baseEnd_746163 < baseStart_746163 := by decide
  rcases family_descends (prefixWord ++ tailWord_746163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746170 : List Nat := [3, 1, 1, 1, 2, 3, 4, 5]
def baseStart_746170 : Nat := 118140960795 + 746170 * 2 ^ 59
def prefixEnd_746170 : Nat := 4983230072969 + 3 ^ 40 * 746170 * 2
def baseEnd_746170 : Nat := 113524106656429878561017

theorem tailTrace_746170 : CollatzResearch.WordTrace tailWord_746170 prefixEnd_746170 113524106656429878561017 := by
  unfold tailWord_746170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6803763926690250133858991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18143370471174000356957309 6803763926690250133858991)
  ·
    refine ⟨10205645890035375200788487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6803763926690250133858991 10205645890035375200788487)
    ·
      refine ⟨15308468835053062801182731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10205645890035375200788487 15308468835053062801182731)
      ·
        refine ⟨22962703252579594201774097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15308468835053062801182731 22962703252579594201774097)
        ·
          refine ⟨17222027439434695651330573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22962703252579594201774097 17222027439434695651330573)
          ·
            refine ⟨6458260289788010869248965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17222027439434695651330573 6458260289788010869248965)
            ·
              refine ⟨1210923804335252037984181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6458260289788010869248965 1210923804335252037984181)
              ·
                refine ⟨113524106656429878561017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1210923804335252037984181 113524106656429878561017)
                ·
                  rfl

theorem cell20_746170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_746170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746170 prefixEnd_746170 := by exact prefixLift 746170
  have htrace : WordTrace (prefixWord ++ tailWord_746170) baseStart_746170 baseEnd_746170 := by
    simpa [prefixWord, tailWord_746170, baseEnd_746170] using wordTrace_append hprefix tailTrace_746170
  have hstable : (prefixWord ++ tailWord_746170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746170).length < 2 ^ (prefixWord ++ tailWord_746170).sum := by decide
  have hdescent : baseEnd_746170 < baseStart_746170 := by decide
  rcases family_descends (prefixWord ++ tailWord_746170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746173 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 3]
def baseStart_746173 : Nat := 118140960795 + 746173 * 2 ^ 59
def prefixEnd_746173 : Nat := 4983230072969 + 3 ^ 40 * 746173 * 2
def baseEnd_746173 : Nat := 340573689251034958583039

theorem tailTrace_746173 : CollatzResearch.WordTrace tailWord_746173 prefixEnd_746173 340573689251034958583039 := by
  unfold tailWord_746173
  simp only [CollatzResearch.WordTrace]
  refine ⟨27215165125750132047795173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18143443417166754698530115 27215165125750132047795173)
  ·
    refine ⟨5102843461078149758961595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27215165125750132047795173 5102843461078149758961595)
    ·
      refine ⟨7654265191617224638442393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5102843461078149758961595 7654265191617224638442393)
      ·
        refine ⟨5740698893712918478831795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7654265191617224638442393 5740698893712918478831795)
        ·
          refine ⟨8611048340569377718247693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5740698893712918478831795 8611048340569377718247693)
          ·
            refine ⟨3229143127713516644342885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8611048340569377718247693 3229143127713516644342885)
            ·
              refine ⟨605464336446284370814291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3229143127713516644342885 605464336446284370814291)
              ·
                refine ⟨908196504669426556221437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605464336446284370814291 908196504669426556221437)
                ·
                  refine ⟨340573689251034958583039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908196504669426556221437 340573689251034958583039)
                  ·
                    rfl

theorem cell20_746173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_746173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746173 prefixEnd_746173 := by exact prefixLift 746173
  have htrace : WordTrace (prefixWord ++ tailWord_746173) baseStart_746173 baseEnd_746173 := by
    simpa [prefixWord, tailWord_746173, baseEnd_746173] using wordTrace_append hprefix tailTrace_746173
  have hstable : (prefixWord ++ tailWord_746173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746173).length < 2 ^ (prefixWord ++ tailWord_746173).sum := by decide
  have hdescent : baseEnd_746173 < baseStart_746173 := by decide
  rcases family_descends (prefixWord ++ tailWord_746173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746211 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 3]
def baseStart_746211 : Nat := 118140960795 + 746211 * 2 ^ 59
def prefixEnd_746211 : Nat := 4983230072969 + 3 ^ 40 * 746211 * 2
def baseEnd_746211 : Nat := 340591033486475715316217

theorem tailTrace_746211 : CollatzResearch.WordTrace tailWord_746211 prefixEnd_746211 340591033486475715316217 := by
  unfold tailWord_746211
  simp only [CollatzResearch.WordTrace]
  refine ⟨27216551099612464537678487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18144367399741643025118991 27216551099612464537678487)
  ·
    refine ⟨40824826649418696806517731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27216551099612464537678487 40824826649418696806517731)
    ·
      refine ⟨61237239974128045209776597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40824826649418696806517731 61237239974128045209776597)
      ·
        refine ⟨1435247811893626059604139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 61237239974128045209776597 1435247811893626059604139)
        ·
          refine ⟨2152871717840439089406209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435247811893626059604139 2152871717840439089406209)
          ·
            refine ⟨1614653788380329317054657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2152871717840439089406209 1614653788380329317054657)
            ·
              refine ⟨1210990341285246987790993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1614653788380329317054657 1210990341285246987790993)
              ·
                refine ⟨908242755963935240843245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1210990341285246987790993 908242755963935240843245)
                ·
                  refine ⟨340591033486475715316217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908242755963935240843245 340591033486475715316217)
                  ·
                    rfl

theorem cell20_746211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 3].length) (baseStart_746211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746211 prefixEnd_746211 := by exact prefixLift 746211
  have htrace : WordTrace (prefixWord ++ tailWord_746211) baseStart_746211 baseEnd_746211 := by
    simpa [prefixWord, tailWord_746211, baseEnd_746211] using wordTrace_append hprefix tailTrace_746211
  have hstable : (prefixWord ++ tailWord_746211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746211).length < 2 ^ (prefixWord ++ tailWord_746211).sum := by decide
  have hdescent : baseEnd_746211 < baseStart_746211 := by decide
  rcases family_descends (prefixWord ++ tailWord_746211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746242 : List Nat := [3, 4, 1, 1, 1, 3, 3, 4]
def baseStart_746242 : Nat := 118140960795 + 746242 * 2 ^ 59
def prefixEnd_746242 : Nat := 4983230072969 + 3 ^ 40 * 746242 * 2
def baseEnd_746242 : Nat := 113535060910392461760919

theorem tailTrace_746242 : CollatzResearch.WordTrace tailWord_746242 prefixEnd_746242 113535060910392461760919 := by
  unfold tailWord_746242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6804420440625039208014245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18145121175000104554704653 6804420440625039208014245)
  ·
    refine ⟨1275828832617194851502671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6804420440625039208014245 1275828832617194851502671)
    ·
      refine ⟨1913743248925792277254007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275828832617194851502671 1913743248925792277254007)
      ·
        refine ⟨2870614873388688415881011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913743248925792277254007 2870614873388688415881011)
        ·
          refine ⟨4305922310083032623821517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870614873388688415881011 4305922310083032623821517)
          ·
            refine ⟨1614720866281137233933069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4305922310083032623821517 1614720866281137233933069)
            ·
              refine ⟨605520324855426462724901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1614720866281137233933069 605520324855426462724901)
              ·
                refine ⟨113535060910392461760919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 605520324855426462724901 113535060910392461760919)
                ·
                  rfl

theorem cell20_746242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_746242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746242 prefixEnd_746242 := by exact prefixLift 746242
  have htrace : WordTrace (prefixWord ++ tailWord_746242) baseStart_746242 baseEnd_746242 := by
    simpa [prefixWord, tailWord_746242, baseEnd_746242] using wordTrace_append hprefix tailTrace_746242
  have hstable : (prefixWord ++ tailWord_746242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746242).length < 2 ^ (prefixWord ++ tailWord_746242).sum := by decide
  have hdescent : baseEnd_746242 < baseStart_746242 := by decide
  rcases family_descends (prefixWord ++ tailWord_746242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746277 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 4]
def baseStart_746277 : Nat := 118140960795 + 746277 * 2 ^ 59
def prefixEnd_746277 : Nat := 4983230072969 + 3 ^ 40 * 746277 * 2
def baseEnd_746277 : Nat := 340621157684872819115947

theorem tailTrace_746277 : CollatzResearch.WordTrace tailWord_746277 prefixEnd_746277 340621157684872819115947 := by
  unfold tailWord_746277
  simp only [CollatzResearch.WordTrace]
  refine ⟨27218958317373357809581085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18145972211582238539720723 27218958317373357809581085)
  ·
    refine ⟨10207109369015009178592907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27218958317373357809581085 10207109369015009178592907)
    ·
      refine ⟨15310664053522513767889361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10207109369015009178592907 15310664053522513767889361)
      ·
        refine ⟨11482998040141885325917021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15310664053522513767889361 11482998040141885325917021)
        ·
          refine ⟨4306124265053206997218883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11482998040141885325917021 4306124265053206997218883)
          ·
            refine ⟨6459186397579810495828325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4306124265053206997218883 6459186397579810495828325)
            ·
              refine ⟨1211097449546214467967811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6459186397579810495828325 1211097449546214467967811)
              ·
                refine ⟨1816646174319321701951717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211097449546214467967811 1816646174319321701951717)
                ·
                  refine ⟨340621157684872819115947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816646174319321701951717 340621157684872819115947)
                  ·
                    rfl

theorem cell20_746277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_746277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746277 prefixEnd_746277 := by exact prefixLift 746277
  have htrace : WordTrace (prefixWord ++ tailWord_746277) baseStart_746277 baseEnd_746277 := by
    simpa [prefixWord, tailWord_746277, baseEnd_746277] using wordTrace_append hprefix tailTrace_746277
  have hstable : (prefixWord ++ tailWord_746277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746277).length < 2 ^ (prefixWord ++ tailWord_746277).sum := by decide
  have hdescent : baseEnd_746277 < baseStart_746277 := by decide
  rcases family_descends (prefixWord ++ tailWord_746277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746301 : List Nat := [1, 4, 1, 4, 2, 1, 1, 6]
def baseStart_746301 : Nat := 118140960795 + 746301 * 2 ^ 59
def prefixEnd_746301 : Nat := 4983230072969 + 3 ^ 40 * 746301 * 2
def baseEnd_746301 : Nat := 113544037312945134105283

theorem tailTrace_746301 : CollatzResearch.WordTrace tailWord_746301 prefixEnd_746301 113544037312945134105283 := by
  unfold tailWord_746301
  simp only [CollatzResearch.WordTrace]
  refine ⟨27219833669286409908454757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18146555779524273272303171 27219833669286409908454757)
  ·
    refine ⟨5103718812991201857835267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27219833669286409908454757 5103718812991201857835267)
    ·
      refine ⟨7655578219486802786752901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5103718812991201857835267 7655578219486802786752901)
      ·
        refine ⟨1435420916153775522516169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7655578219486802786752901 1435420916153775522516169)
        ·
          refine ⟨1076565687115331641887127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1435420916153775522516169 1076565687115331641887127)
          ·
            refine ⟨1614848530672997462830691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076565687115331641887127 1614848530672997462830691)
            ·
              refine ⟨2422272796009496194246037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614848530672997462830691 2422272796009496194246037)
              ·
                refine ⟨113544037312945134105283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2422272796009496194246037 113544037312945134105283)
                ·
                  rfl

theorem cell20_746301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 6].length) (baseStart_746301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746301 prefixEnd_746301 := by exact prefixLift 746301
  have htrace : WordTrace (prefixWord ++ tailWord_746301) baseStart_746301 baseEnd_746301 := by
    simpa [prefixWord, tailWord_746301, baseEnd_746301] using wordTrace_append hprefix tailTrace_746301
  have hstable : (prefixWord ++ tailWord_746301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746301).length < 2 ^ (prefixWord ++ tailWord_746301).sum := by decide
  have hdescent : baseEnd_746301 < baseStart_746301 := by decide
  rcases family_descends (prefixWord ++ tailWord_746301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746329 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 5]
def baseStart_746329 : Nat := 118140960795 + 746329 * 2 ^ 59
def prefixEnd_746329 : Nat := 4983230072969 + 3 ^ 40 * 746329 * 2
def baseEnd_746329 : Nat := 340644891901791749382401

theorem tailTrace_746329 : CollatzResearch.WordTrace tailWord_746329 prefixEnd_746329 340644891901791749382401 := by
  unfold tailWord_746329
  simp only [CollatzResearch.WordTrace]
  refine ⟨27220854913184970690474041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18147236608789980460316027 27220854913184970690474041)
  ·
    refine ⟨20415641184888728017855531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27220854913184970690474041 20415641184888728017855531)
    ·
      refine ⟨30623461777333092026783297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20415641184888728017855531 30623461777333092026783297)
      ·
        refine ⟨22967596332999819020087473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30623461777333092026783297 22967596332999819020087473)
        ·
          refine ⟨17225697249749864265065605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22967596332999819020087473 17225697249749864265065605)
          ·
            refine ⟨3229818234328099549699801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17225697249749864265065605 3229818234328099549699801)
            ·
              refine ⟨2422363675746074662274851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3229818234328099549699801 2422363675746074662274851)
              ·
                refine ⟨3633545513619111993412277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422363675746074662274851 3633545513619111993412277)
                ·
                  refine ⟨340644891901791749382401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3633545513619111993412277 340644891901791749382401)
                  ·
                    rfl

theorem cell20_746329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_746329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746329 prefixEnd_746329 := by exact prefixLift 746329
  have htrace : WordTrace (prefixWord ++ tailWord_746329) baseStart_746329 baseEnd_746329 := by
    simpa [prefixWord, tailWord_746329, baseEnd_746329] using wordTrace_append hprefix tailTrace_746329
  have hstable : (prefixWord ++ tailWord_746329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746329).length < 2 ^ (prefixWord ++ tailWord_746329).sum := by decide
  have hdescent : baseEnd_746329 < baseStart_746329 := by decide
  rcases family_descends (prefixWord ++ tailWord_746329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746332 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_746332 : Nat := 118140960795 + 746332 * 2 ^ 59
def prefixEnd_746332 : Nat := 4983230072969 + 3 ^ 40 * 746332 * 2
def baseEnd_746332 : Nat := 340646261183537072282389

theorem tailTrace_746332 : CollatzResearch.WordTrace tailWord_746332 prefixEnd_746332 340646261183537072282389 := by
  unfold tailWord_746332
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610482166087051101416625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18147309554782734801888833 13610482166087051101416625)
  ·
    refine ⟨10207861624565288326062469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13610482166087051101416625 10207861624565288326062469)
    ·
      refine ⟨1913974054605991561136713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10207861624565288326062469 1913974054605991561136713)
      ·
        refine ⟨1435480540954493670852535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1913974054605991561136713 1435480540954493670852535)
        ·
          refine ⟨2153220811431740506278803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435480540954493670852535 2153220811431740506278803)
          ·
            refine ⟨3229831217147610759418205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153220811431740506278803 3229831217147610759418205)
            ·
              refine ⟨1211186706430354034781827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3229831217147610759418205 1211186706430354034781827)
              ·
                refine ⟨1816780059645531052172741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211186706430354034781827 1816780059645531052172741)
                ·
                  refine ⟨340646261183537072282389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816780059645531052172741 340646261183537072282389)
                  ·
                    rfl

theorem cell20_746332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_746332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746332 prefixEnd_746332 := by exact prefixLift 746332
  have htrace : WordTrace (prefixWord ++ tailWord_746332) baseStart_746332 baseEnd_746332 := by
    simpa [prefixWord, tailWord_746332, baseEnd_746332] using wordTrace_append hprefix tailTrace_746332
  have hstable : (prefixWord ++ tailWord_746332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746332).length < 2 ^ (prefixWord ++ tailWord_746332).sum := by decide
  have hdescent : baseEnd_746332 < baseStart_746332 := by decide
  rcases family_descends (prefixWord ++ tailWord_746332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746394 : List Nat := [3, 1, 1, 4, 4, 1, 1, 5]
def baseStart_746394 : Nat := 118140960795 + 746394 * 2 ^ 59
def prefixEnd_746394 : Nat := 4983230072969 + 3 ^ 40 * 746394 * 2
def baseEnd_746394 : Nat := 113558186557646804071823

theorem tailTrace_746394 : CollatzResearch.WordTrace tailWord_746394 prefixEnd_746394 113558186557646804071823 := by
  unfold tailWord_746394
  simp only [CollatzResearch.WordTrace]
  refine ⟨6805806414487371697897559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18148817105299657861060157 6805806414487371697897559)
  ·
    refine ⟨10208709621731057546846339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6805806414487371697897559 10208709621731057546846339)
    ·
      refine ⟨15313064432596586320269509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10208709621731057546846339 15313064432596586320269509)
      ·
        refine ⟨2871199581111859935050533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15313064432596586320269509 2871199581111859935050533)
        ·
          refine ⟨538349921458473737821975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2871199581111859935050533 538349921458473737821975)
          ·
            refine ⟨807524882187710606732963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538349921458473737821975 807524882187710606732963)
            ·
              refine ⟨1211287323281565910099445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807524882187710606732963 1211287323281565910099445)
              ·
                refine ⟨113558186557646804071823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1211287323281565910099445 113558186557646804071823)
                ·
                  rfl

theorem cell20_746394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_746394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746394 prefixEnd_746394 := by exact prefixLift 746394
  have htrace : WordTrace (prefixWord ++ tailWord_746394) baseStart_746394 baseEnd_746394 := by
    simpa [prefixWord, tailWord_746394, baseEnd_746394] using wordTrace_append hprefix tailTrace_746394
  have hstable : (prefixWord ++ tailWord_746394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746394).length < 2 ^ (prefixWord ++ tailWord_746394).sum := by decide
  have hdescent : baseEnd_746394 < baseStart_746394 := by decide
  rcases family_descends (prefixWord ++ tailWord_746394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746412 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_746412 : Nat := 118140960795 + 746412 * 2 ^ 59
def prefixEnd_746412 : Nat := 4983230072969 + 3 ^ 40 * 746412 * 2
def baseEnd_746412 : Nat := 340682775363412349615395

theorem tailTrace_746412 : CollatzResearch.WordTrace tailWord_746412 prefixEnd_746412 340682775363412349615395 := by
  unfold tailWord_746412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13611941085942137932872745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18149254781256183910496993 13611941085942137932872745)
  ·
    refine ⟨10208955814456603449654559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13611941085942137932872745 10208955814456603449654559)
    ·
      refine ⟨15313433721684905174481839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10208955814456603449654559 15313433721684905174481839)
      ·
        refine ⟨22970150582527357761722759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15313433721684905174481839 22970150582527357761722759)
        ·
          refine ⟨34455225873791036642584139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22970150582527357761722759 34455225873791036642584139)
          ·
            refine ⟨51682838810686554963876209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34455225873791036642584139 51682838810686554963876209)
            ·
              refine ⟨38762129108014916222907157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51682838810686554963876209 38762129108014916222907157)
              ·
                refine ⟨1816974801938199197948773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38762129108014916222907157 1816974801938199197948773)
                ·
                  refine ⟨340682775363412349615395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1816974801938199197948773 340682775363412349615395)
                  ·
                    rfl

theorem cell20_746412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_746412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746412 prefixEnd_746412 := by exact prefixLift 746412
  have htrace : WordTrace (prefixWord ++ tailWord_746412) baseStart_746412 baseEnd_746412 := by
    simpa [prefixWord, tailWord_746412, baseEnd_746412] using wordTrace_append hprefix tailTrace_746412
  have hstable : (prefixWord ++ tailWord_746412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746412).length < 2 ^ (prefixWord ++ tailWord_746412).sum := by decide
  have hdescent : baseEnd_746412 < baseStart_746412 := by decide
  rcases family_descends (prefixWord ++ tailWord_746412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746443 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 5]
def baseStart_746443 : Nat := 118140960795 + 746443 * 2 ^ 59
def prefixEnd_746443 : Nat := 4983230072969 + 3 ^ 40 * 746443 * 2
def baseEnd_746443 : Nat := 340696924608114019581935

theorem tailTrace_746443 : CollatzResearch.WordTrace tailWord_746443 prefixEnd_746443 340696924608114019581935 := by
  unfold tailWord_746443
  simp only [CollatzResearch.WordTrace]
  refine ⟨27225012834771968160123983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18150008556514645440082655 27225012834771968160123983)
  ·
    refine ⟨40837519252157952240185975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27225012834771968160123983 40837519252157952240185975)
    ·
      refine ⟨61256278878236928360278963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40837519252157952240185975 61256278878236928360278963)
      ·
        refine ⟨91884418317355392540418445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61256278878236928360278963 91884418317355392540418445)
        ·
          refine ⟨34456656869008272202656917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91884418317355392540418445 34456656869008272202656917)
          ·
            refine ⟨1615155790734762759499543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34456656869008272202656917 1615155790734762759499543)
            ·
              refine ⟨2422733686102144139249315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615155790734762759499543 2422733686102144139249315)
              ·
                refine ⟨3634100529153216208873973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422733686102144139249315 3634100529153216208873973)
                ·
                  refine ⟨340696924608114019581935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3634100529153216208873973 340696924608114019581935)
                  ·
                    rfl

theorem cell20_746443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_746443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746443 prefixEnd_746443 := by exact prefixLift 746443
  have htrace : WordTrace (prefixWord ++ tailWord_746443) baseStart_746443 baseEnd_746443 := by
    simpa [prefixWord, tailWord_746443, baseEnd_746443] using wordTrace_append hprefix tailTrace_746443
  have hstable : (prefixWord ++ tailWord_746443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746443).length < 2 ^ (prefixWord ++ tailWord_746443).sum := by decide
  have hdescent : baseEnd_746443 < baseStart_746443 := by decide
  rcases family_descends (prefixWord ++ tailWord_746443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746446 : List Nat := [4, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_746446 : Nat := 118140960795 + 746446 * 2 ^ 59
def prefixEnd_746446 : Nat := 4983230072969 + 3 ^ 40 * 746446 * 2
def baseEnd_746446 : Nat := 340698293889859342481923

theorem tailTrace_746446 : CollatzResearch.WordTrace tailWord_746446 prefixEnd_746446 340698293889859342481923 := by
  unfold tailWord_746446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3403140281720137459060399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18150081502507399781655461 3403140281720137459060399)
  ·
    refine ⟨5104710422580206188590599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3403140281720137459060399 5104710422580206188590599)
    ·
      refine ⟨7657065633870309282885899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5104710422580206188590599 7657065633870309282885899)
      ·
        refine ⟨11485598450805463924328849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7657065633870309282885899 11485598450805463924328849)
        ·
          refine ⟨8614198838104097943246637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11485598450805463924328849 8614198838104097943246637)
          ·
            refine ⟨3230324564289036728717489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8614198838104097943246637 3230324564289036728717489)
            ·
              refine ⟨2422743423216777546538117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3230324564289036728717489 2422743423216777546538117)
              ·
                refine ⟨454264391853145789975897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2422743423216777546538117 454264391853145789975897)
                ·
                  refine ⟨340698293889859342481923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454264391853145789975897 340698293889859342481923)
                  ·
                    rfl

theorem cell20_746446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_746446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746446 prefixEnd_746446 := by exact prefixLift 746446
  have htrace : WordTrace (prefixWord ++ tailWord_746446) baseStart_746446 baseEnd_746446 := by
    simpa [prefixWord, tailWord_746446, baseEnd_746446] using wordTrace_append hprefix tailTrace_746446
  have hstable : (prefixWord ++ tailWord_746446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746446).length < 2 ^ (prefixWord ++ tailWord_746446).sum := by decide
  have hdescent : baseEnd_746446 < baseStart_746446 := by decide
  rcases family_descends (prefixWord ++ tailWord_746446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746474 : List Nat := [3, 1, 3, 1, 2, 3, 1, 6]
def baseStart_746474 : Nat := 118140960795 + 746474 * 2 ^ 59
def prefixEnd_746474 : Nat := 4983230072969 + 3 ^ 40 * 746474 * 2
def baseEnd_746474 : Nat := 113570357950938563182825

theorem tailTrace_746474 : CollatzResearch.WordTrace tailWord_746474 prefixEnd_746474 113570357950938563182825 := by
  unfold tailWord_746474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6806535874414915113625619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18150762331773106969668317 6806535874414915113625619)
  ·
    refine ⟨10209803811622372670438429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6806535874414915113625619 10209803811622372670438429)
    ·
      refine ⟨3828676429358389751414411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10209803811622372670438429 3828676429358389751414411)
      ·
        refine ⟨5743014644037584627121617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3828676429358389751414411 5743014644037584627121617)
        ·
          refine ⟨4307260983028188470341213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5743014644037584627121617 4307260983028188470341213)
          ·
            refine ⟨1615222868635570676377955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4307260983028188470341213 1615222868635570676377955)
            ·
              refine ⟨2422834302953356014566933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615222868635570676377955 2422834302953356014566933)
              ·
                refine ⟨113570357950938563182825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2422834302953356014566933 113570357950938563182825)
                ·
                  rfl

theorem cell20_746474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_746474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746474 prefixEnd_746474 := by exact prefixLift 746474
  have htrace : WordTrace (prefixWord ++ tailWord_746474) baseStart_746474 baseEnd_746474 := by
    simpa [prefixWord, tailWord_746474, baseEnd_746474] using wordTrace_append hprefix tailTrace_746474
  have hstable : (prefixWord ++ tailWord_746474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746474).length < 2 ^ (prefixWord ++ tailWord_746474).sum := by decide
  have hdescent : baseEnd_746474 < baseStart_746474 := by decide
  rcases family_descends (prefixWord ++ tailWord_746474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746481 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 5]
def baseStart_746481 : Nat := 118140960795 + 746481 * 2 ^ 59
def prefixEnd_746481 : Nat := 4983230072969 + 3 ^ 40 * 746481 * 2
def baseEnd_746481 : Nat := 340714268843554776315113

theorem tailTrace_746481 : CollatzResearch.WordTrace tailWord_746481 prefixEnd_746481 340714268843554776315113 := by
  unfold tailWord_746481
  simp only [CollatzResearch.WordTrace]
  refine ⟨27226398808634300650007297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18150932539089533766671531 27226398808634300650007297)
  ·
    refine ⟨20419799106475725487505473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27226398808634300650007297 20419799106475725487505473)
    ·
      refine ⟨15314849329856794115629105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20419799106475725487505473 15314849329856794115629105)
      ·
        refine ⟨11486136997392595586721829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15314849329856794115629105 11486136997392595586721829)
        ·
          refine ⟨2153650687011111672510343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11486136997392595586721829 2153650687011111672510343)
          ·
            refine ⟨3230476030516667508765515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153650687011111672510343 3230476030516667508765515)
            ·
              refine ⟨4845714045775001263148273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3230476030516667508765515 4845714045775001263148273)
              ·
                refine ⟨3634285534331250947361205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4845714045775001263148273 3634285534331250947361205)
                ·
                  refine ⟨340714268843554776315113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3634285534331250947361205 340714268843554776315113)
                  ·
                    rfl

theorem cell20_746481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_746481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746481 prefixEnd_746481 := by exact prefixLift 746481
  have htrace : WordTrace (prefixWord ++ tailWord_746481) baseStart_746481 baseEnd_746481 := by
    simpa [prefixWord, tailWord_746481, baseEnd_746481] using wordTrace_append hprefix tailTrace_746481
  have hstable : (prefixWord ++ tailWord_746481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746481).length < 2 ^ (prefixWord ++ tailWord_746481).sum := by decide
  have hdescent : baseEnd_746481 < baseStart_746481 := by decide
  rcases family_descends (prefixWord ++ tailWord_746481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746505 : List Nat := [1, 2, 1, 1, 3, 1, 1, 8, 2]
def baseStart_746505 : Nat := 118140960795 + 746505 * 2 ^ 59
def prefixEnd_746505 : Nat := 4983230072969 + 3 ^ 40 * 746505 * 2
def baseEnd_746505 : Nat := 340725223097517359515015

theorem tailTrace_746505 : CollatzResearch.WordTrace tailWord_746505 prefixEnd_746505 340725223097517359515015 := by
  unfold tailWord_746505
  simp only [CollatzResearch.WordTrace]
  refine ⟨27227274160547352748880969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18151516107031568499253979 27227274160547352748880969)
  ·
    refine ⟨20420455620410514561660727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27227274160547352748880969 20420455620410514561660727)
    ·
      refine ⟨30630683430615771842491091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20420455620410514561660727 30630683430615771842491091)
      ·
        refine ⟨45946025145923657763736637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30630683430615771842491091 45946025145923657763736637)
        ·
          refine ⟨17229759429721371661401239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45946025145923657763736637 17229759429721371661401239)
          ·
            refine ⟨25844639144582057492101859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17229759429721371661401239 25844639144582057492101859)
            ·
              refine ⟨38766958716873086238152789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25844639144582057492101859 38766958716873086238152789)
              ·
                refine ⟨454300297463356479353353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 38766958716873086238152789 454300297463356479353353)
                ·
                  refine ⟨340725223097517359515015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454300297463356479353353 340725223097517359515015)
                  ·
                    rfl

theorem cell20_746505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 2].length) (baseStart_746505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746505 prefixEnd_746505 := by exact prefixLift 746505
  have htrace : WordTrace (prefixWord ++ tailWord_746505) baseStart_746505 baseEnd_746505 := by
    simpa [prefixWord, tailWord_746505, baseEnd_746505] using wordTrace_append hprefix tailTrace_746505
  have hstable : (prefixWord ++ tailWord_746505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746505).length < 2 ^ (prefixWord ++ tailWord_746505).sum := by decide
  have hdescent : baseEnd_746505 < baseStart_746505 := by decide
  rcases family_descends (prefixWord ++ tailWord_746505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746533 : List Nat := [1, 3, 1, 2, 2, 2, 1, 8]
def baseStart_746533 : Nat := 118140960795 + 746533 * 2 ^ 59
def prefixEnd_746533 : Nat := 4983230072969 + 3 ^ 40 * 746533 * 2
def baseEnd_746533 : Nat := 113579334353491235527189

theorem tailTrace_746533 : CollatzResearch.WordTrace tailWord_746533 prefixEnd_746533 113579334353491235527189 := by
  unfold tailWord_746533
  simp only [CollatzResearch.WordTrace]
  refine ⟨27228295404445913530900253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18152196936297275687266835 27228295404445913530900253)
  ·
    refine ⟨10210610776667217574087595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27228295404445913530900253 10210610776667217574087595)
    ·
      refine ⟨15315916165000826361131393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10210610776667217574087595 15315916165000826361131393)
      ·
        refine ⟨11486937123750619770848545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15315916165000826361131393 11486937123750619770848545)
        ·
          refine ⟨8615202842812964828136409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11486937123750619770848545 8615202842812964828136409)
          ·
            refine ⟨6461402132109723621102307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8615202842812964828136409 6461402132109723621102307)
            ·
              refine ⟨9692103198164585431653461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6461402132109723621102307 9692103198164585431653461)
              ·
                refine ⟨113579334353491235527189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9692103198164585431653461 113579334353491235527189)
                ·
                  rfl

theorem cell20_746533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_746533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746533 prefixEnd_746533 := by exact prefixLift 746533
  have htrace : WordTrace (prefixWord ++ tailWord_746533) baseStart_746533 baseEnd_746533 := by
    simpa [prefixWord, tailWord_746533, baseEnd_746533] using wordTrace_append hprefix tailTrace_746533
  have hstable : (prefixWord ++ tailWord_746533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746533).length < 2 ^ (prefixWord ++ tailWord_746533).sum := by decide
  have hdescent : baseEnd_746533 < baseStart_746533 := by decide
  rcases family_descends (prefixWord ++ tailWord_746533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746550 : List Nat := [5, 1, 2, 1, 1, 10]
def baseStart_746550 : Nat := 118140960795 + 746550 * 2 ^ 59
def prefixEnd_746550 : Nat := 4983230072969 + 3 ^ 40 * 746550 * 2
def baseEnd_746550 : Nat := 12620213419396192704253

theorem tailTrace_746550 : CollatzResearch.WordTrace tailWord_746550 prefixEnd_746550 12620213419396192704253 := by
  unfold tailWord_746550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701807215336520339641819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18152610296922883622846069 1701807215336520339641819)
  ·
    refine ⟨2552710823004780509462729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1701807215336520339641819 2552710823004780509462729)
    ·
      refine ⟨1914533117253585382097047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2552710823004780509462729 1914533117253585382097047)
      ·
        refine ⟨2871799675880378073145571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914533117253585382097047 2871799675880378073145571)
        ·
          refine ⟨4307699513820567109718357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2871799675880378073145571 4307699513820567109718357)
          ·
            refine ⟨12620213419396192704253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4307699513820567109718357 12620213419396192704253)
            ·
              rfl

theorem cell20_746550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 10].length) (baseStart_746550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746550 prefixEnd_746550 := by exact prefixLift 746550
  have htrace : WordTrace (prefixWord ++ tailWord_746550) baseStart_746550 baseEnd_746550 := by
    simpa [prefixWord, tailWord_746550, baseEnd_746550] using wordTrace_append hprefix tailTrace_746550
  have hstable : (prefixWord ++ tailWord_746550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746550).length < 2 ^ (prefixWord ++ tailWord_746550).sum := by decide
  have hdescent : baseEnd_746550 < baseStart_746550 := by decide
  rcases family_descends (prefixWord ++ tailWord_746550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746629 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 3]
def baseStart_746629 : Nat := 118140960795 + 746629 * 2 ^ 59
def prefixEnd_746629 : Nat := 4983230072969 + 3 ^ 40 * 746629 * 2
def baseEnd_746629 : Nat := 340781820076324039381175

theorem tailTrace_746629 : CollatzResearch.WordTrace tailWord_746629 prefixEnd_746629 340781820076324039381175 := by
  unfold tailWord_746629
  simp only [CollatzResearch.WordTrace]
  refine ⟨27231796812098121926394941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18154531208065414617596627 27231796812098121926394941)
  ·
    refine ⟨10211923804536795722398103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27231796812098121926394941 10211923804536795722398103)
    ·
      refine ⟨15317885706805193583597155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10211923804536795722398103 15317885706805193583597155)
      ·
        refine ⟨22976828560207790375395733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15317885706805193583597155 22976828560207790375395733)
        ·
          refine ⟨1077038838759740173846675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22976828560207790375395733 1077038838759740173846675)
          ·
            refine ⟨1615558258139610260770013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077038838759740173846675 1615558258139610260770013)
            ·
              refine ⟨605834346802353847788755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1615558258139610260770013 605834346802353847788755)
              ·
                refine ⟨908751520203530771683133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605834346802353847788755 908751520203530771683133)
                ·
                  refine ⟨340781820076324039381175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908751520203530771683133 340781820076324039381175)
                  ·
                    rfl

theorem cell20_746629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_746629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746629 prefixEnd_746629 := by exact prefixLift 746629
  have htrace : WordTrace (prefixWord ++ tailWord_746629) baseStart_746629 baseEnd_746629 := by
    simpa [prefixWord, tailWord_746629, baseEnd_746629] using wordTrace_append hprefix tailTrace_746629
  have hstable : (prefixWord ++ tailWord_746629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746629).length < 2 ^ (prefixWord ++ tailWord_746629).sum := by decide
  have hdescent : baseEnd_746629 < baseStart_746629 := by decide
  rcases family_descends (prefixWord ++ tailWord_746629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746685 : List Nat := [1, 4, 1, 2, 1, 1, 3, 7]
def baseStart_746685 : Nat := 118140960795 + 746685 * 2 ^ 59
def prefixEnd_746685 : Nat := 4983230072969 + 3 ^ 40 * 746685 * 2
def baseEnd_746685 : Nat := 113602460000745577838093

theorem tailTrace_746685 : CollatzResearch.WordTrace tailWord_746685 prefixEnd_746685 113602460000745577838093 := by
  unfold tailWord_746685
  simp only [CollatzResearch.WordTrace]
  refine ⟨27233839299895243490433509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18155892866596828993622339 27233839299895243490433509)
  ·
    refine ⟨5106344868730358154456283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27233839299895243490433509 5106344868730358154456283)
    ·
      refine ⟨7659517303095537231684425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5106344868730358154456283 7659517303095537231684425)
      ·
        refine ⟨5744637977321652923763319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7659517303095537231684425 5744637977321652923763319)
        ·
          refine ⟨8616956965982479385644979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5744637977321652923763319 8616956965982479385644979)
          ·
            refine ⟨12925435448973719078467469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8616956965982479385644979 12925435448973719078467469)
            ·
              refine ⟨4847038293365144654425301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12925435448973719078467469 4847038293365144654425301)
              ·
                refine ⟨113602460000745577838093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4847038293365144654425301 113602460000745577838093)
                ·
                  rfl

theorem cell20_746685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_746685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746685 prefixEnd_746685 := by exact prefixLift 746685
  have htrace : WordTrace (prefixWord ++ tailWord_746685) baseStart_746685 baseEnd_746685 := by
    simpa [prefixWord, tailWord_746685, baseEnd_746685] using wordTrace_append hprefix tailTrace_746685
  have hstable : (prefixWord ++ tailWord_746685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746685).length < 2 ^ (prefixWord ++ tailWord_746685).sum := by decide
  have hdescent : baseEnd_746685 < baseStart_746685 := by decide
  rcases family_descends (prefixWord ++ tailWord_746685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746688 : List Nat := [2, 1, 1, 2, 6, 1, 1, 3, 3]
def baseStart_746688 : Nat := 118140960795 + 746688 * 2 ^ 59
def prefixEnd_746688 : Nat := 4983230072969 + 3 ^ 40 * 746688 * 2
def baseEnd_746688 : Nat := 340808749283982056414267

theorem tailTrace_746688 : CollatzResearch.WordTrace tailWord_746688 prefixEnd_746688 340808749283982056414267 := by
  unfold tailWord_746688
  simp only [CollatzResearch.WordTrace]
  refine ⟨13616974359442187501396359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18155965812589583335195145 13616974359442187501396359)
  ·
    refine ⟨20425461539163281252094539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13616974359442187501396359 20425461539163281252094539)
    ·
      refine ⟨30638192308744921878141809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20425461539163281252094539 30638192308744921878141809)
      ·
        refine ⟨22978644231558691408606357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30638192308744921878141809 22978644231558691408606357)
        ·
          refine ⟨1077123948354313659778423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22978644231558691408606357 1077123948354313659778423)
          ·
            refine ⟨1615685922531470489667635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077123948354313659778423 1615685922531470489667635)
            ·
              refine ⟨2423528883797205734501453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615685922531470489667635 2423528883797205734501453)
              ·
                refine ⟨908823331423952150438045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2423528883797205734501453 908823331423952150438045)
                ·
                  refine ⟨340808749283982056414267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908823331423952150438045 340808749283982056414267)
                  ·
                    rfl

theorem cell20_746688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_746688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746688 prefixEnd_746688 := by exact prefixLift 746688
  have htrace : WordTrace (prefixWord ++ tailWord_746688) baseStart_746688 baseEnd_746688 := by
    simpa [prefixWord, tailWord_746688, baseEnd_746688] using wordTrace_append hprefix tailTrace_746688
  have hstable : (prefixWord ++ tailWord_746688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746688).length < 2 ^ (prefixWord ++ tailWord_746688).sum := by decide
  have hdescent : baseEnd_746688 < baseStart_746688 := by decide
  rcases family_descends (prefixWord ++ tailWord_746688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746781 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 3]
def baseStart_746781 : Nat := 118140960795 + 746781 * 2 ^ 59
def prefixEnd_746781 : Nat := 4983230072969 + 3 ^ 40 * 746781 * 2
def baseEnd_746781 : Nat := 340851197018087066313887

theorem tailTrace_746781 : CollatzResearch.WordTrace tailWord_746781 prefixEnd_746781 340851197018087066313887 := by
  unfold tailWord_746781
  simp only [CollatzResearch.WordTrace]
  refine ⟨27237340707547451885928197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18158227138364967923952131 27237340707547451885928197)
  ·
    refine ⟨5107001382665147228611537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27237340707547451885928197 5107001382665147228611537)
    ·
      refine ⟨3830251036998860421458653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5107001382665147228611537 3830251036998860421458653)
      ·
        refine ⟨1436344138874572658046995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3830251036998860421458653 1436344138874572658046995)
        ·
          refine ⟨2154516208311858987070493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436344138874572658046995 2154516208311858987070493)
          ·
            refine ⟨807943578116947120151435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2154516208311858987070493 807943578116947120151435)
            ·
              refine ⟨1211915367175420680227153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807943578116947120151435 1211915367175420680227153)
              ·
                refine ⟨908936525381565510170365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211915367175420680227153 908936525381565510170365)
                ·
                  refine ⟨340851197018087066313887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 908936525381565510170365 340851197018087066313887)
                  ·
                    rfl

theorem cell20_746781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_746781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746781 prefixEnd_746781 := by exact prefixLift 746781
  have htrace : WordTrace (prefixWord ++ tailWord_746781) baseStart_746781 baseEnd_746781 := by
    simpa [prefixWord, tailWord_746781, baseEnd_746781] using wordTrace_append hprefix tailTrace_746781
  have hstable : (prefixWord ++ tailWord_746781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746781).length < 2 ^ (prefixWord ++ tailWord_746781).sum := by decide
  have hdescent : baseEnd_746781 < baseStart_746781 := by decide
  rcases family_descends (prefixWord ++ tailWord_746781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746837 : List Nat := [1, 3, 2, 2, 3, 1, 8]
def baseStart_746837 : Nat := 118140960795 + 746837 * 2 ^ 59
def prefixEnd_746837 : Nat := 4983230072969 + 3 ^ 40 * 746837 * 2
def baseEnd_746837 : Nat := 37875195215999973382999

theorem tailTrace_746837 : CollatzResearch.WordTrace tailWord_746837 prefixEnd_746837 37875195215999973382999 := by
  unfold tailWord_746837
  simp only [CollatzResearch.WordTrace]
  refine ⟨27239383195344573449966765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18159588796896382299977843 27239383195344573449966765)
  ·
    refine ⟨10214768698254215043737537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27239383195344573449966765 10214768698254215043737537)
    ·
      refine ⟨7661076523690661282803153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10214768698254215043737537 7661076523690661282803153)
      ·
        refine ⟨5745807392767995962102365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7661076523690661282803153 5745807392767995962102365)
        ·
          refine ⟨2154677772287998485788387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5745807392767995962102365 2154677772287998485788387)
          ·
            refine ⟨3232016658431997728682581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154677772287998485788387 3232016658431997728682581)
            ·
              refine ⟨37875195215999973382999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3232016658431997728682581 37875195215999973382999)
              ·
                rfl

theorem cell20_746837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 8].length) (baseStart_746837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746837 prefixEnd_746837 := by exact prefixLift 746837
  have htrace : WordTrace (prefixWord ++ tailWord_746837) baseStart_746837 baseEnd_746837 := by
    simpa [prefixWord, tailWord_746837, baseEnd_746837] using wordTrace_append hprefix tailTrace_746837
  have hstable : (prefixWord ++ tailWord_746837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746837).length < 2 ^ (prefixWord ++ tailWord_746837).sum := by decide
  have hdescent : baseEnd_746837 < baseStart_746837 := by decide
  rcases family_descends (prefixWord ++ tailWord_746837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746906 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_746906 : Nat := 118140960795 + 746906 * 2 ^ 59
def prefixEnd_746906 : Nat := 4983230072969 + 3 ^ 40 * 746906 * 2
def baseEnd_746906 : Nat := 340908250424142187146709

theorem tailTrace_746906 : CollatzResearch.WordTrace tailWord_746906 prefixEnd_746906 340908250424142187146709 := by
  unfold tailWord_746906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6810474958023649558557143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18161266554729732156152381 6810474958023649558557143)
  ·
    refine ⟨10215712437035474337835715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6810474958023649558557143 10215712437035474337835715)
    ·
      refine ⟨15323568655553211506753573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10215712437035474337835715 15323568655553211506753573)
      ·
        refine ⟨2873169122916227157516295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15323568655553211506753573 2873169122916227157516295)
        ·
          refine ⟨4309753684374340736274443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873169122916227157516295 4309753684374340736274443)
          ·
            refine ⟨6464630526561511104411665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309753684374340736274443 6464630526561511104411665)
            ·
              refine ⟨4848472894921133328308749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6464630526561511104411665 4848472894921133328308749)
              ·
                refine ⟨1818177335595424998115781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4848472894921133328308749 1818177335595424998115781)
                ·
                  refine ⟨340908250424142187146709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1818177335595424998115781 340908250424142187146709)
                  ·
                    rfl

theorem cell20_746906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_746906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746906 prefixEnd_746906 := by exact prefixLift 746906
  have htrace : WordTrace (prefixWord ++ tailWord_746906) baseStart_746906 baseEnd_746906 := by
    simpa [prefixWord, tailWord_746906, baseEnd_746906] using wordTrace_append hprefix tailTrace_746906
  have hstable : (prefixWord ++ tailWord_746906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746906).length < 2 ^ (prefixWord ++ tailWord_746906).sum := by decide
  have hdescent : baseEnd_746906 < baseStart_746906 := by decide
  rcases family_descends (prefixWord ++ tailWord_746906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746946 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 3]
def baseStart_746946 : Nat := 118140960795 + 746946 * 2 ^ 59
def prefixEnd_746946 : Nat := 4983230072969 + 3 ^ 40 * 746946 * 2
def baseEnd_746946 : Nat := 340926507514079825813213

theorem tailTrace_746946 : CollatzResearch.WordTrace tailWord_746946 prefixEnd_746946 340926507514079825813213 := by
  unfold tailWord_746946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6810839687987421266421173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18162239167966456710456461 6810839687987421266421173)
  ·
    refine ⟨638516220748820743726985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6810839687987421266421173 638516220748820743726985)
    ·
      refine ⟨478887165561615557795239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 638516220748820743726985 478887165561615557795239)
      ·
        refine ⟨718330748342423336692859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478887165561615557795239 718330748342423336692859)
        ·
          refine ⟨1077496122513635005039289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718330748342423336692859 1077496122513635005039289)
          ·
            refine ⟨808122091885226253779467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1077496122513635005039289 808122091885226253779467)
            ·
              refine ⟨1212183137827839380669201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808122091885226253779467 1212183137827839380669201)
              ·
                refine ⟨909137353370879535501901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212183137827839380669201 909137353370879535501901)
                ·
                  refine ⟨340926507514079825813213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909137353370879535501901 340926507514079825813213)
                  ·
                    rfl

theorem cell20_746946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_746946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746946 prefixEnd_746946 := by exact prefixLift 746946
  have htrace : WordTrace (prefixWord ++ tailWord_746946) baseStart_746946 baseEnd_746946 := by
    simpa [prefixWord, tailWord_746946, baseEnd_746946] using wordTrace_append hprefix tailTrace_746946
  have hstable : (prefixWord ++ tailWord_746946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746946).length < 2 ^ (prefixWord ++ tailWord_746946).sum := by decide
  have hdescent : baseEnd_746946 < baseStart_746946 := by decide
  rcases family_descends (prefixWord ++ tailWord_746946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746954 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_746954 : Nat := 118140960795 + 746954 * 2 ^ 59
def prefixEnd_746954 : Nat := 4983230072969 + 3 ^ 40 * 746954 * 2
def baseEnd_746954 : Nat := 340930158932067353546513

theorem tailTrace_746954 : CollatzResearch.WordTrace tailWord_746954 prefixEnd_746954 340930158932067353546513 := by
  unfold tailWord_746954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6810912633980175607993979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18162433690613801621317277 6810912633980175607993979)
  ·
    refine ⟨10216368950970263411990969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6810912633980175607993979 10216368950970263411990969)
    ·
      refine ⟨7662276713227697558993227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10216368950970263411990969 7662276713227697558993227)
      ·
        refine ⟨11493415069841546338489841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7662276713227697558993227 11493415069841546338489841)
        ·
          refine ⟨8620061302381159753867381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11493415069841546338489841 8620061302381159753867381)
          ·
            refine ⟨808130747098233726925067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8620061302381159753867381 808130747098233726925067)
            ·
              refine ⟨1212196120647350590387601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808130747098233726925067 1212196120647350590387601)
              ·
                refine ⟨909147090485512942790701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212196120647350590387601 909147090485512942790701)
                ·
                  refine ⟨340930158932067353546513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 909147090485512942790701 340930158932067353546513)
                  ·
                    rfl

theorem cell20_746954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_746954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_746954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_746954 prefixEnd_746954 := by exact prefixLift 746954
  have htrace : WordTrace (prefixWord ++ tailWord_746954) baseStart_746954 baseEnd_746954 := by
    simpa [prefixWord, tailWord_746954, baseEnd_746954] using wordTrace_append hprefix tailTrace_746954
  have hstable : (prefixWord ++ tailWord_746954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746954).length < 2 ^ (prefixWord ++ tailWord_746954).sum := by decide
  have hdescent : baseEnd_746954 < baseStart_746954 := by decide
  rcases family_descends (prefixWord ++ tailWord_746954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
