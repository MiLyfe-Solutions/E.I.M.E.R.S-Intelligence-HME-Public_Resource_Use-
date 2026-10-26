import V185TrunkScan23Chunk0518

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3068935 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 4, 2, 2]
def baseStart_3068935 : Nat := 118140960795 + 3068935 * 2 ^ 59
def prefixEnd_3068935 : Nat := 4983230072969 + 3 ^ 40 * 3068935 * 2
def baseEnd_3068935 : Nat := 1575838752406055511398731

theorem tailTrace_3068935 : CollatzResearch.WordTrace tailWord_3068935 prefixEnd_3068935 1575838752406055511398731 := by
  unfold tailWord_3068935
  simp only [CollatzResearch.WordTrace]
  refine ⟨111933255136780102214800259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74622170091186734809866839 111933255136780102214800259)
  ·
    refine ⟨167899882705170153322200389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111933255136780102214800259 167899882705170153322200389)
    ·
      refine ⟨31481228007219403747912573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167899882705170153322200389 31481228007219403747912573)
      ·
        refine ⟨11805460502707276405467215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31481228007219403747912573 11805460502707276405467215)
        ·
          refine ⟨17708190754060914608200823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11805460502707276405467215 17708190754060914608200823)
          ·
            refine ⟨26562286131091371912301235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17708190754060914608200823 26562286131091371912301235)
            ·
              refine ⟨39843429196637057868451853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26562286131091371912301235 39843429196637057868451853)
              ·
                refine ⟨14941285948738896700669445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39843429196637057868451853 14941285948738896700669445)
                ·
                  refine ⟨2801491115388543131375521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14941285948738896700669445 2801491115388543131375521)
                  ·
                    refine ⟨2101118336541407348531641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2801491115388543131375521 2101118336541407348531641)
                    ·
                      refine ⟨1575838752406055511398731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101118336541407348531641 1575838752406055511398731)
                      ·
                        rfl

theorem cell23_3068935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_3068935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068935 prefixEnd_3068935 := by exact prefixLift 3068935
  have htrace : WordTrace (prefixWord ++ tailWord_3068935) baseStart_3068935 baseEnd_3068935 := by
    simpa [prefixWord, tailWord_3068935, baseEnd_3068935] using wordTrace_append hprefix tailTrace_3068935
  have hstable : (prefixWord ++ tailWord_3068935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068935).length < 2 ^ (prefixWord ++ tailWord_3068935).sum := by decide
  have hdescent : baseEnd_3068935 < baseStart_3068935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068946 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3068946 : Nat := 118140960795 + 3068946 * 2 ^ 59
def prefixEnd_3068946 : Nat := 4983230072969 + 3 ^ 40 * 3068946 * 2
def baseEnd_3068946 : Nat := 1575844400693254968361181

theorem tailTrace_3068946 : CollatzResearch.WordTrace tailWord_3068946 prefixEnd_3068946 1575844400693254968361181 := by
  unfold tailWord_3068946
  simp only [CollatzResearch.WordTrace]
  refine ⟨27983414084935062773362673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74622437559826834062300461 27983414084935062773362673)
  ·
    refine ⟨20987560563701297080022005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27983414084935062773362673 20987560563701297080022005)
    ·
      refine ⟨1967583802846996601252063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20987560563701297080022005 1967583802846996601252063)
      ·
        refine ⟨2951375704270494901878095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967583802846996601252063 2951375704270494901878095)
        ·
          refine ⟨4427063556405742352817143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951375704270494901878095 4427063556405742352817143)
          ·
            refine ⟨6640595334608613529225715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427063556405742352817143 6640595334608613529225715)
            ·
              refine ⟨9960893001912920293838573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6640595334608613529225715 9960893001912920293838573)
              ·
                refine ⟨3735334875717345110189465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9960893001912920293838573 3735334875717345110189465)
                ·
                  refine ⟨2801501156788008832642099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3735334875717345110189465 2801501156788008832642099)
                  ·
                    refine ⟨4202251735182013248963149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2801501156788008832642099 4202251735182013248963149)
                    ·
                      refine ⟨1575844400693254968361181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4202251735182013248963149 1575844400693254968361181)
                      ·
                        rfl

theorem cell23_3068946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3068946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068946 prefixEnd_3068946 := by exact prefixLift 3068946
  have htrace : WordTrace (prefixWord ++ tailWord_3068946) baseStart_3068946 baseEnd_3068946 := by
    simpa [prefixWord, tailWord_3068946, baseEnd_3068946] using wordTrace_append hprefix tailTrace_3068946
  have hstable : (prefixWord ++ tailWord_3068946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068946).length < 2 ^ (prefixWord ++ tailWord_3068946).sum := by decide
  have hdescent : baseEnd_3068946 < baseStart_3068946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068952 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 2, 2, 2]
def baseStart_3068952 : Nat := 118140960795 + 3068952 * 2 ^ 59
def prefixEnd_3068952 : Nat := 4983230072969 + 3 ^ 40 * 3068952 * 2
def baseEnd_3068952 : Nat := 1575847481577181944886153

theorem tailTrace_3068952 : CollatzResearch.WordTrace tailWord_3068952 prefixEnd_3068952 1575847481577181944886153 := by
  unfold tailWord_3068952
  simp only [CollatzResearch.WordTrace]
  refine ⟨55966937588859257059084555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74622583451812342745446073 55966937588859257059084555)
  ·
    refine ⟨83950406383288885588626833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55966937588859257059084555 83950406383288885588626833)
    ·
      refine ⟨62962804787466664191470125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83950406383288885588626833 62962804787466664191470125)
      ·
        refine ⟨23611051795299999071801297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62962804787466664191470125 23611051795299999071801297)
        ·
          refine ⟨17708288846474999303850973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23611051795299999071801297 17708288846474999303850973)
          ·
            refine ⟨6640608317428124738944115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17708288846474999303850973 6640608317428124738944115)
            ·
              refine ⟨9960912476142187108416173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6640608317428124738944115 9960912476142187108416173)
              ·
                refine ⟨3735342178553320165656065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9960912476142187108416173 3735342178553320165656065)
                ·
                  refine ⟨2801506633914990124242049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3735342178553320165656065 2801506633914990124242049)
                  ·
                    refine ⟨2101129975436242593181537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2801506633914990124242049 2101129975436242593181537)
                    ·
                      refine ⟨1575847481577181944886153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101129975436242593181537 1575847481577181944886153)
                      ·
                        rfl

theorem cell23_3068952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_3068952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068952 prefixEnd_3068952 := by exact prefixLift 3068952
  have htrace : WordTrace (prefixWord ++ tailWord_3068952) baseStart_3068952 baseEnd_3068952 := by
    simpa [prefixWord, tailWord_3068952, baseEnd_3068952] using wordTrace_append hprefix tailTrace_3068952
  have hstable : (prefixWord ++ tailWord_3068952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068952).length < 2 ^ (prefixWord ++ tailWord_3068952).sum := by decide
  have hdescent : baseEnd_3068952 < baseStart_3068952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068988 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_3068988 : Nat := 118140960795 + 3068988 * 2 ^ 59
def prefixEnd_3068988 : Nat := 4983230072969 + 3 ^ 40 * 3068988 * 2
def baseEnd_3068988 : Nat := 525288655626914601345329

theorem tailTrace_3068988 : CollatzResearch.WordTrace tailWord_3068988 prefixEnd_3068988 525288655626914601345329 := by
  unfold tailWord_3068988
  simp only [CollatzResearch.WordTrace]
  refine ⟨55967594102794046133239809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74623458803725394844319745 55967594102794046133239809)
  ·
    refine ⟨41975695577095534599929857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55967594102794046133239809 41975695577095534599929857)
    ·
      refine ⟨31481771682821650949947393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41975695577095534599929857 31481771682821650949947393)
      ·
        refine ⟨23611328762116238212460545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31481771682821650949947393 23611328762116238212460545)
        ·
          refine ⟨17708496571587178659345409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23611328762116238212460545 17708496571587178659345409)
          ·
            refine ⟨13281372428690383994509057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17708496571587178659345409 13281372428690383994509057)
            ·
              refine ⟨9961029321517787995881793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13281372428690383994509057 9961029321517787995881793)
              ·
                refine ⟨7470771991138340996911345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9961029321517787995881793 7470771991138340996911345)
                ·
                  refine ⟨5603078993353755747683509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7470771991138340996911345 5603078993353755747683509)
                  ·
                    refine ⟨525288655626914601345329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5603078993353755747683509 525288655626914601345329)
                    ·
                      rfl

theorem cell23_3068988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_3068988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068988 prefixEnd_3068988 := by exact prefixLift 3068988
  have htrace : WordTrace (prefixWord ++ tailWord_3068988) baseStart_3068988 baseEnd_3068988 := by
    simpa [prefixWord, tailWord_3068988, baseEnd_3068988] using wordTrace_append hprefix tailTrace_3068988
  have hstable : (prefixWord ++ tailWord_3068988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068988).length < 2 ^ (prefixWord ++ tailWord_3068988).sum := by decide
  have hdescent : baseEnd_3068988 < baseStart_3068988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3068991 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 4]
def baseStart_3068991 : Nat := 118140960795 + 3068991 * 2 ^ 59
def prefixEnd_3068991 : Nat := 4983230072969 + 3 ^ 40 * 3068991 * 2
def baseEnd_3068991 : Nat := 1575867507322707292298473

theorem tailTrace_3068991 : CollatzResearch.WordTrace tailWord_3068991 prefixEnd_3068991 1575867507322707292298473 := by
  unfold tailWord_3068991
  simp only [CollatzResearch.WordTrace]
  refine ⟨111935297624577223778838827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74623531749718149185892551 111935297624577223778838827)
  ·
    refine ⟨167902946436865835668258241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111935297624577223778838827 167902946436865835668258241)
    ·
      refine ⟨125927209827649376751193681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167902946436865835668258241 125927209827649376751193681)
      ·
        refine ⟨94445407370737032563395261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125927209827649376751193681 94445407370737032563395261)
        ·
          refine ⟨35417027764026387211273223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94445407370737032563395261 35417027764026387211273223)
          ·
            refine ⟨53125541646039580816909835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35417027764026387211273223 53125541646039580816909835)
            ·
              refine ⟨79688312469059371225364753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53125541646039580816909835 79688312469059371225364753)
              ·
                refine ⟨59766234351794528419023565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79688312469059371225364753 59766234351794528419023565)
                ·
                  refine ⟨22412337881922948157133837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59766234351794528419023565 22412337881922948157133837)
                  ·
                    refine ⟨8404626705721105558925189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22412337881922948157133837 8404626705721105558925189)
                    ·
                      refine ⟨1575867507322707292298473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8404626705721105558925189 1575867507322707292298473)
                      ·
                        rfl

theorem cell23_3068991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_3068991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3068991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3068991 prefixEnd_3068991 := by exact prefixLift 3068991
  have htrace : WordTrace (prefixWord ++ tailWord_3068991) baseStart_3068991 baseEnd_3068991 := by
    simpa [prefixWord, tailWord_3068991, baseEnd_3068991] using wordTrace_append hprefix tailTrace_3068991
  have hstable : (prefixWord ++ tailWord_3068991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3068991).length < 2 ^ (prefixWord ++ tailWord_3068991).sum := by decide
  have hdescent : baseEnd_3068991 < baseStart_3068991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3068991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069022 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3069022 : Nat := 118140960795 + 3069022 * 2 ^ 59
def prefixEnd_3069022 : Nat := 4983230072969 + 3 ^ 40 * 3069022 * 2
def baseEnd_3069022 : Nat := 525294475074332223670277

theorem tailTrace_3069022 : CollatzResearch.WordTrace tailWord_3069022 prefixEnd_3069022 525294475074332223670277 := by
  unfold tailWord_3069022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13992053535933114509152165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74624285524976610715478213 13992053535933114509152165)
  ·
    refine ⟨2623510037987458970466031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13992053535933114509152165 2623510037987458970466031)
    ·
      refine ⟨3935265056981188455699047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2623510037987458970466031 3935265056981188455699047)
      ·
        refine ⟨5902897585471782683548571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3935265056981188455699047 5902897585471782683548571)
        ·
          refine ⟨8854346378207674025322857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5902897585471782683548571 8854346378207674025322857)
          ·
            refine ⟨6640759783655755518992143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8854346378207674025322857 6640759783655755518992143)
            ·
              refine ⟨9961139675483633278488215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6640759783655755518992143 9961139675483633278488215)
              ·
                refine ⟨14941709513225449917732323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9961139675483633278488215 14941709513225449917732323)
                ·
                  refine ⟨22412564269838174876598485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14941709513225449917732323 22412564269838174876598485)
                  ·
                    refine ⟨525294475074332223670277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22412564269838174876598485 525294475074332223670277)
                    ·
                      rfl

theorem cell23_3069022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3069022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069022 prefixEnd_3069022 := by exact prefixLift 3069022
  have htrace : WordTrace (prefixWord ++ tailWord_3069022) baseStart_3069022 baseEnd_3069022 := by
    simpa [prefixWord, tailWord_3069022, baseEnd_3069022] using wordTrace_append hprefix tailTrace_3069022
  have hstable : (prefixWord ++ tailWord_3069022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069022).length < 2 ^ (prefixWord ++ tailWord_3069022).sum := by decide
  have hdescent : baseEnd_3069022 < baseStart_3069022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069038 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3069038 : Nat := 118140960795 + 3069038 * 2 ^ 59
def prefixEnd_3069038 : Nat := 4983230072969 + 3 ^ 40 * 3069038 * 2
def baseEnd_3069038 : Nat := 1575891640913468608410757

theorem tailTrace_3069038 : CollatzResearch.WordTrace tailWord_3069038 prefixEnd_3069038 1575891640913468608410757 := by
  unfold tailWord_3069038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13992126481925868850724971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74624674570271300537199845 13992126481925868850724971)
  ·
    refine ⟨20988189722888803276087457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13992126481925868850724971 20988189722888803276087457)
    ·
      refine ⟨15741142292166602457065593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20988189722888803276087457 15741142292166602457065593)
      ·
        refine ⟨11805856719124951842799195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15741142292166602457065593 11805856719124951842799195)
        ·
          refine ⟨17708785078687427764198793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11805856719124951842799195 17708785078687427764198793)
          ·
            refine ⟨13281588809015570823149095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17708785078687427764198793 13281588809015570823149095)
            ·
              refine ⟨19922383213523356234723643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13281588809015570823149095 19922383213523356234723643)
              ·
                refine ⟨29883574820285034352085465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19922383213523356234723643 29883574820285034352085465)
                ·
                  refine ⟨22412681115213775764064099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29883574820285034352085465 22412681115213775764064099)
                  ·
                    refine ⟨33619021672820663646096149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22412681115213775764064099 33619021672820663646096149)
                    ·
                      refine ⟨1575891640913468608410757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33619021672820663646096149 1575891640913468608410757)
                      ·
                        rfl

theorem cell23_3069038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3069038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069038 prefixEnd_3069038 := by exact prefixLift 3069038
  have htrace : WordTrace (prefixWord ++ tailWord_3069038) baseStart_3069038 baseEnd_3069038 := by
    simpa [prefixWord, tailWord_3069038, baseEnd_3069038] using wordTrace_append hprefix tailTrace_3069038
  have hstable : (prefixWord ++ tailWord_3069038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069038).length < 2 ^ (prefixWord ++ tailWord_3069038).sum := by decide
  have hdescent : baseEnd_3069038 < baseStart_3069038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069048 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 6]
def baseStart_3069048 : Nat := 118140960795 + 3069048 * 2 ^ 59
def prefixEnd_3069048 : Nat := 4983230072969 + 3 ^ 40 * 3069048 * 2
def baseEnd_3069048 : Nat := 175099641746668174365079

theorem tailTrace_3069048 : CollatzResearch.WordTrace tailWord_3069048 prefixEnd_3069048 175099641746668174365079 := by
  unfold tailWord_3069048
  simp only [CollatzResearch.WordTrace]
  refine ⟨55968688292685361256831899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74624917723580481675775865 55968688292685361256831899)
  ·
    refine ⟨83953032439028041885247849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55968688292685361256831899 83953032439028041885247849)
    ·
      refine ⟨62964774329271031413935887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83953032439028041885247849 62964774329271031413935887)
      ·
        refine ⟨94447161493906547120903831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62964774329271031413935887 94447161493906547120903831)
        ·
          refine ⟨141670742240859820681355747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94447161493906547120903831 141670742240859820681355747)
          ·
            refine ⟨212506113361289731022033621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141670742240859820681355747 212506113361289731022033621)
            ·
              refine ⟨4980612031905228070828913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 212506113361289731022033621 4980612031905228070828913)
              ·
                refine ⟨3735459023928921053121685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4980612031905228070828913 3735459023928921053121685)
                ·
                  refine ⟨175099641746668174365079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3735459023928921053121685 175099641746668174365079)
                  ·
                    rfl

theorem cell23_3069048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 6].length) (baseStart_3069048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069048 prefixEnd_3069048 := by exact prefixLift 3069048
  have htrace : WordTrace (prefixWord ++ tailWord_3069048) baseStart_3069048 baseEnd_3069048 := by
    simpa [prefixWord, tailWord_3069048, baseEnd_3069048] using wordTrace_append hprefix tailTrace_3069048
  have hstable : (prefixWord ++ tailWord_3069048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069048).length < 2 ^ (prefixWord ++ tailWord_3069048).sum := by decide
  have hdescent : baseEnd_3069048 < baseStart_3069048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069065 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 6]
def baseStart_3069065 : Nat := 118140960795 + 3069065 * 2 ^ 59
def prefixEnd_3069065 : Nat := 4983230072969 + 3 ^ 40 * 3069065 * 2
def baseEnd_3069065 : Nat := 175100611654571111419237

theorem tailTrace_3069065 : CollatzResearch.WordTrace tailWord_3069065 prefixEnd_3069065 175100611654571111419237 := by
  unfold tailWord_3069065
  simp only [CollatzResearch.WordTrace]
  refine ⟨111937996626309134417032649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74625331084206089611355099 111937996626309134417032649)
  ·
    refine ⟨83953497469731850812774487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111937996626309134417032649 83953497469731850812774487)
    ·
      refine ⟨125930246204597776219161731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83953497469731850812774487 125930246204597776219161731)
      ·
        refine ⟨188895369306896664328742597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125930246204597776219161731 188895369306896664328742597)
        ·
          refine ⟨35417881745043124561639237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188895369306896664328742597 35417881745043124561639237)
          ·
            refine ⟨6640852827195585855307357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35417881745043124561639237 6640852827195585855307357)
            ·
              refine ⟨2490319810198344695740259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6640852827195585855307357 2490319810198344695740259)
              ·
                refine ⟨3735479715297517043610389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2490319810198344695740259 3735479715297517043610389)
                ·
                  refine ⟨175100611654571111419237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3735479715297517043610389 175100611654571111419237)
                  ·
                    rfl

theorem cell23_3069065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 6].length) (baseStart_3069065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069065 prefixEnd_3069065 := by exact prefixLift 3069065
  have htrace : WordTrace (prefixWord ++ tailWord_3069065) baseStart_3069065 baseEnd_3069065 := by
    simpa [prefixWord, tailWord_3069065, baseEnd_3069065] using wordTrace_append hprefix tailTrace_3069065
  have hstable : (prefixWord ++ tailWord_3069065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069065).length < 2 ^ (prefixWord ++ tailWord_3069065).sum := by decide
  have hdescent : baseEnd_3069065 < baseStart_3069065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069071 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_3069071 : Nat := 118140960795 + 3069071 * 2 ^ 59
def prefixEnd_3069071 : Nat := 4983230072969 + 3 ^ 40 * 3069071 * 2
def baseEnd_3069071 : Nat := 1575908585775066979298105

theorem tailTrace_3069071 : CollatzResearch.WordTrace tailWord_3069071 prefixEnd_3069071 1575908585775066979298105 := by
  unfold tailWord_3069071
  simp only [CollatzResearch.WordTrace]
  refine ⟨111938215464287397441751067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74625476976191598294500711 111938215464287397441751067)
  ·
    refine ⟨167907323196431096162626601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111938215464287397441751067 167907323196431096162626601)
    ·
      refine ⟨125930492397323322121969951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167907323196431096162626601 125930492397323322121969951)
      ·
        refine ⟨188895738595984983182954927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125930492397323322121969951 188895738595984983182954927)
        ·
          refine ⟨283343607893977474774432391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188895738595984983182954927 283343607893977474774432391)
          ·
            refine ⟨425015411840966212161648587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283343607893977474774432391 425015411840966212161648587)
            ·
              refine ⟨637523117761449318242472881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425015411840966212161648587 637523117761449318242472881)
              ·
                refine ⟨478142338321086988681854661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 637523117761449318242472881 478142338321086988681854661)
                ·
                  refine ⟨89651688435203810377847749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 478142338321086988681854661 89651688435203810377847749)
                  ·
                    refine ⟨16809691581600714445846453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89651688435203810377847749 16809691581600714445846453)
                    ·
                      refine ⟨1575908585775066979298105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16809691581600714445846453 1575908585775066979298105)
                      ·
                        rfl

theorem cell23_3069071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_3069071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069071 prefixEnd_3069071 := by exact prefixLift 3069071
  have htrace : WordTrace (prefixWord ++ tailWord_3069071) baseStart_3069071 baseEnd_3069071 := by
    simpa [prefixWord, tailWord_3069071, baseEnd_3069071] using wordTrace_append hprefix tailTrace_3069071
  have hstable : (prefixWord ++ tailWord_3069071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069071).length < 2 ^ (prefixWord ++ tailWord_3069071).sum := by decide
  have hdescent : baseEnd_3069071 < baseStart_3069071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069075 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 3, 1, 3]
def baseStart_3069075 : Nat := 118140960795 + 3069075 * 2 ^ 59
def prefixEnd_3069075 : Nat := 4983230072969 + 3 ^ 40 * 3069075 * 2
def baseEnd_3069075 : Nat := 1575910639697684963648087

theorem tailTrace_3069075 : CollatzResearch.WordTrace tailWord_3069075 prefixEnd_3069075 1575910639697684963648087 := by
  unfold tailWord_3069075
  simp only [CollatzResearch.WordTrace]
  refine ⟨111938361356272906124896679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74625574237515270749931119 111938361356272906124896679)
  ·
    refine ⟨167907542034409359187345019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111938361356272906124896679 167907542034409359187345019)
    ·
      refine ⟨251861313051614038781017529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167907542034409359187345019 251861313051614038781017529)
      ·
        refine ⟨188895984788710529085763147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251861313051614038781017529 188895984788710529085763147)
        ·
          refine ⟨283343977183065793628644721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188895984788710529085763147 283343977183065793628644721)
          ·
            refine ⟨212507982887299345221483541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283343977183065793628644721 212507982887299345221483541)
            ·
              refine ⟨9961311697842156807257041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212507982887299345221483541 9961311697842156807257041)
              ·
                refine ⟨7470983773381617605442781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9961311697842156807257041 7470983773381617605442781)
                ·
                  refine ⟨2801618915018106602041043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7470983773381617605442781 2801618915018106602041043)
                  ·
                    refine ⟨4202428372527159903061565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2801618915018106602041043 4202428372527159903061565)
                    ·
                      refine ⟨1575910639697684963648087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4202428372527159903061565 1575910639697684963648087)
                      ·
                        rfl

theorem cell23_3069075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 1, 3].length) (baseStart_3069075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069075 prefixEnd_3069075 := by exact prefixLift 3069075
  have htrace : WordTrace (prefixWord ++ tailWord_3069075) baseStart_3069075 baseEnd_3069075 := by
    simpa [prefixWord, tailWord_3069075, baseEnd_3069075] using wordTrace_append hprefix tailTrace_3069075
  have hstable : (prefixWord ++ tailWord_3069075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069075).length < 2 ^ (prefixWord ++ tailWord_3069075).sum := by decide
  have hdescent : baseEnd_3069075 < baseStart_3069075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069085 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_3069085 : Nat := 118140960795 + 3069085 * 2 ^ 59
def prefixEnd_3069085 : Nat := 4983230072969 + 3 ^ 40 * 3069085 * 2
def baseEnd_3069085 : Nat := 1575915774504229924523041

theorem tailTrace_3069085 : CollatzResearch.WordTrace tailWord_3069085 prefixEnd_3069085 1575915774504229924523041 := by
  unfold tailWord_3069085
  simp only [CollatzResearch.WordTrace]
  refine ⟨111938726086236677832760709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74625817390824451888507139 111938726086236677832760709)
  ·
    refine ⟨20988511141169377093642633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111938726086236677832760709 20988511141169377093642633)
    ·
      refine ⟨15741383355877032820231975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20988511141169377093642633 15741383355877032820231975)
      ·
        refine ⟨23612075033815549230347963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15741383355877032820231975 23612075033815549230347963)
        ·
          refine ⟨35418112550723323845521945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23612075033815549230347963 35418112550723323845521945)
          ·
            refine ⟨26563584413042492884141459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35418112550723323845521945 26563584413042492884141459)
            ·
              refine ⟨39845376619563739326212189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26563584413042492884141459 39845376619563739326212189)
              ·
                refine ⟨14942016232336402247329571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39845376619563739326212189 14942016232336402247329571)
                ·
                  refine ⟨22413024348504603370994357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14942016232336402247329571 22413024348504603370994357)
                  ·
                    refine ⟨2101221032672306566030721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22413024348504603370994357 2101221032672306566030721)
                    ·
                      refine ⟨1575915774504229924523041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101221032672306566030721 1575915774504229924523041)
                      ·
                        rfl

theorem cell23_3069085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_3069085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069085 prefixEnd_3069085 := by exact prefixLift 3069085
  have htrace : WordTrace (prefixWord ++ tailWord_3069085) baseStart_3069085 baseEnd_3069085 := by
    simpa [prefixWord, tailWord_3069085, baseEnd_3069085] using wordTrace_append hprefix tailTrace_3069085
  have hstable : (prefixWord ++ tailWord_3069085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069085).length < 2 ^ (prefixWord ++ tailWord_3069085).sum := by decide
  have hdescent : baseEnd_3069085 < baseStart_3069085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069086 : List Nat := [4, 3, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_3069086 : Nat := 118140960795 + 3069086 * 2 ^ 59
def prefixEnd_3069086 : Nat := 4983230072969 + 3 ^ 40 * 3069086 * 2
def baseEnd_3069086 : Nat := 525305429328294806870179

theorem tailTrace_3069086 : CollatzResearch.WordTrace tailWord_3069086 prefixEnd_3069086 525305429328294806870179 := by
  unfold tailWord_3069086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13992345319904131875443389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74625841706155370002364741 13992345319904131875443389)
  ·
    refine ⟨5247129494964049453291271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13992345319904131875443389 5247129494964049453291271)
    ·
      refine ⟨7870694242446074179936907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5247129494964049453291271 7870694242446074179936907)
      ·
        refine ⟨11806041363669111269905361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7870694242446074179936907 11806041363669111269905361)
        ·
          refine ⟨8854531022751833452429021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11806041363669111269905361 8854531022751833452429021)
          ·
            refine ⟨3320449133531937544660883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8854531022751833452429021 3320449133531937544660883)
            ·
              refine ⟨4980673700297906316991325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320449133531937544660883 4980673700297906316991325)
              ·
                refine ⟨1867752637611714868871747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4980673700297906316991325 1867752637611714868871747)
                ·
                  refine ⟨2801628956417572303307621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867752637611714868871747 2801628956417572303307621)
                  ·
                    refine ⟨525305429328294806870179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2801628956417572303307621 525305429328294806870179)
                    ·
                      rfl

theorem cell23_3069086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_3069086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069086 prefixEnd_3069086 := by exact prefixLift 3069086
  have htrace : WordTrace (prefixWord ++ tailWord_3069086) baseStart_3069086 baseEnd_3069086 := by
    simpa [prefixWord, tailWord_3069086, baseEnd_3069086] using wordTrace_append hprefix tailTrace_3069086
  have hstable : (prefixWord ++ tailWord_3069086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069086).length < 2 ^ (prefixWord ++ tailWord_3069086).sum := by decide
  have hdescent : baseEnd_3069086 < baseStart_3069086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069128 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3069128 : Nat := 118140960795 + 3069128 * 2 ^ 59
def prefixEnd_3069128 : Nat := 4983230072969 + 3 ^ 40 * 3069128 * 2
def baseEnd_3069128 : Nat := 1575937854172373256285343

theorem tailTrace_3069128 : CollatzResearch.WordTrace tailWord_3069128 prefixEnd_3069128 1575937854172373256285343 := by
  unfold tailWord_3069128
  simp only [CollatzResearch.WordTrace]
  refine ⟨55970147212540448088288019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74626862950053930784384025 55970147212540448088288019)
  ·
    refine ⟨83955220818810672132432029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55970147212540448088288019 83955220818810672132432029)
    ·
      refine ⟨31483207807054002049662011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83955220818810672132432029 31483207807054002049662011)
      ·
        refine ⟨47224811710581003074493017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31483207807054002049662011 47224811710581003074493017)
        ·
          refine ⟨35418608782935752305869763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47224811710581003074493017 35418608782935752305869763)
          ·
            refine ⟨53127913174403628458804645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35418608782935752305869763 53127913174403628458804645)
            ·
              refine ⟨9961483720200680336025871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53127913174403628458804645 9961483720200680336025871)
              ·
                refine ⟨14942225580301020504038807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9961483720200680336025871 14942225580301020504038807)
                ·
                  refine ⟨22413338370451530756058211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14942225580301020504038807 22413338370451530756058211)
                  ·
                    refine ⟨33620007555677296134087317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22413338370451530756058211 33620007555677296134087317)
                    ·
                      refine ⟨1575937854172373256285343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33620007555677296134087317 1575937854172373256285343)
                      ·
                        rfl

theorem cell23_3069128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3069128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069128 prefixEnd_3069128 := by exact prefixLift 3069128
  have htrace : WordTrace (prefixWord ++ tailWord_3069128) baseStart_3069128 baseEnd_3069128 := by
    simpa [prefixWord, tailWord_3069128, baseEnd_3069128] using wordTrace_append hprefix tailTrace_3069128
  have hstable : (prefixWord ++ tailWord_3069128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069128).length < 2 ^ (prefixWord ++ tailWord_3069128).sum := by decide
  have hdescent : baseEnd_3069128 < baseStart_3069128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069135 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 1, 2, 3]
def baseStart_3069135 : Nat := 118140960795 + 3069135 * 2 ^ 59
def prefixEnd_3069135 : Nat := 4983230072969 + 3 ^ 40 * 3069135 * 2
def baseEnd_3069135 : Nat := 1575941448536954728897811

theorem tailTrace_3069135 : CollatzResearch.WordTrace tailWord_3069135 prefixEnd_3069135 1575941448536954728897811 := by
  unfold tailWord_3069135
  simp only [CollatzResearch.WordTrace]
  refine ⟨111940549736055536372080859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74627033157370357581387239 111940549736055536372080859)
  ·
    refine ⟨167910824604083304558121289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111940549736055536372080859 167910824604083304558121289)
    ·
      refine ⟨125933118453062478418590967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167910824604083304558121289 125933118453062478418590967)
      ·
        refine ⟨188899677679593717627886451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125933118453062478418590967 188899677679593717627886451)
        ·
          refine ⟨283349516519390576441829677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188899677679593717627886451 283349516519390576441829677)
          ·
            refine ⟨106256068694771466165686129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283349516519390576441829677 106256068694771466165686129)
            ·
              refine ⟨79692051521078599624264597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106256068694771466165686129 79692051521078599624264597)
              ·
                refine ⟨3735564915050559357387403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79692051521078599624264597 3735564915050559357387403)
                ·
                  refine ⟨5603347372575839036081105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3735564915050559357387403 5603347372575839036081105)
                  ·
                    refine ⟨4202510529431879277060829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5603347372575839036081105 4202510529431879277060829)
                    ·
                      refine ⟨1575941448536954728897811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4202510529431879277060829 1575941448536954728897811)
                      ·
                        rfl

theorem cell23_3069135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 2, 3].length) (baseStart_3069135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069135 prefixEnd_3069135 := by exact prefixLift 3069135
  have htrace : WordTrace (prefixWord ++ tailWord_3069135) baseStart_3069135 baseEnd_3069135 := by
    simpa [prefixWord, tailWord_3069135, baseEnd_3069135] using wordTrace_append hprefix tailTrace_3069135
  have hstable : (prefixWord ++ tailWord_3069135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069135).length < 2 ^ (prefixWord ++ tailWord_3069135).sum := by decide
  have hdescent : baseEnd_3069135 < baseStart_3069135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069138 : List Nat := [3, 2, 2, 2, 1, 1, 1, 11]
def baseStart_3069138 : Nat := 118140960795 + 3069138 * 2 ^ 59
def prefixEnd_3069138 : Nat := 4983230072969 + 3 ^ 40 * 3069138 * 2
def baseEnd_3069138 : Nat := 58368258851071045080011

theorem tailTrace_3069138 : CollatzResearch.WordTrace tailWord_3069138 prefixEnd_3069138 58368258851071045080011 := by
  unfold tailWord_3069138
  simp only [CollatzResearch.WordTrace]
  refine ⟨27985164788761166971110017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74627106103363111922960045 27985164788761166971110017)
  ·
    refine ⟨20988873591570875228332513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27985164788761166971110017 20988873591570875228332513)
    ·
      refine ⟨15741655193678156421249385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20988873591570875228332513 15741655193678156421249385)
      ·
        refine ⟨11806241395258617315937039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15741655193678156421249385 11806241395258617315937039)
        ·
          refine ⟨17709362092887925973905559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11806241395258617315937039 17709362092887925973905559)
          ·
            refine ⟨26564043139331888960858339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17709362092887925973905559 26564043139331888960858339)
            ·
              refine ⟨39846064708997833441287509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26564043139331888960858339 39846064708997833441287509)
              ·
                refine ⟨58368258851071045080011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 39846064708997833441287509 58368258851071045080011)
                ·
                  rfl

theorem cell23_3069138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 11].length) (baseStart_3069138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069138 prefixEnd_3069138 := by exact prefixLift 3069138
  have htrace : WordTrace (prefixWord ++ tailWord_3069138) baseStart_3069138 baseEnd_3069138 := by
    simpa [prefixWord, tailWord_3069138, baseEnd_3069138] using wordTrace_append hprefix tailTrace_3069138
  have hstable : (prefixWord ++ tailWord_3069138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069138).length < 2 ^ (prefixWord ++ tailWord_3069138).sum := by decide
  have hdescent : baseEnd_3069138 < baseStart_3069138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069159 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 2, 4]
def baseStart_3069159 : Nat := 118140960795 + 3069159 * 2 ^ 59
def prefixEnd_3069159 : Nat := 4983230072969 + 3 ^ 40 * 3069159 * 2
def baseEnd_3069159 : Nat := 525317924024220878332567

theorem tailTrace_3069159 : CollatzResearch.WordTrace tailWord_3069159 prefixEnd_3069159 525317924024220878332567 := by
  unfold tailWord_3069159
  simp only [CollatzResearch.WordTrace]
  refine ⟨111941425087968588470954531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74627616725312392313969687 111941425087968588470954531)
  ·
    refine ⟨167912137631952882706431797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111941425087968588470954531 167912137631952882706431797)
    ·
      refine ⟨15741762902995582753727981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167912137631952882706431797 15741762902995582753727981)
      ·
        refine ⟨5903161088623343532647993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15741762902995582753727981 5903161088623343532647993)
        ·
          refine ⟨4427370816467507649485995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5903161088623343532647993 4427370816467507649485995)
          ·
            refine ⟨6641056224701261474228993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427370816467507649485995 6641056224701261474228993)
            ·
              refine ⟨4980792168525946105671745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6641056224701261474228993 4980792168525946105671745)
              ·
                refine ⟨3735594126394459579253809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4980792168525946105671745 3735594126394459579253809)
                ·
                  refine ⟨2801695594795844684440357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3735594126394459579253809 2801695594795844684440357)
                  ·
                    refine ⟨525317924024220878332567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2801695594795844684440357 525317924024220878332567)
                    ·
                      rfl

theorem cell23_3069159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_3069159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069159 prefixEnd_3069159 := by exact prefixLift 3069159
  have htrace : WordTrace (prefixWord ++ tailWord_3069159) baseStart_3069159 baseEnd_3069159 := by
    simpa [prefixWord, tailWord_3069159, baseEnd_3069159] using wordTrace_append hprefix tailTrace_3069159
  have hstable : (prefixWord ++ tailWord_3069159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069159).length < 2 ^ (prefixWord ++ tailWord_3069159).sum := by decide
  have hdescent : baseEnd_3069159 < baseStart_3069159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069182 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_3069182 : Nat := 118140960795 + 3069182 * 2 ^ 59
def prefixEnd_3069182 : Nat := 4983230072969 + 3 ^ 40 * 3069182 * 2
def baseEnd_3069182 : Nat := 1575965582127716045010095

theorem tailTrace_3069182 : CollatzResearch.WordTrace tailWord_3069182 prefixEnd_3069182 1575965582127716045010095 := by
  unfold tailWord_3069182
  simp only [CollatzResearch.WordTrace]
  refine ⟨13992782995860657924880225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74628175977923508932694533 13992782995860657924880225)
  ·
    refine ⟨10494587246895493443660169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13992782995860657924880225 10494587246895493443660169)
    ·
      refine ⟨7870940435171620082745127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10494587246895493443660169 7870940435171620082745127)
      ·
        refine ⟨11806410652757430124117691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7870940435171620082745127 11806410652757430124117691)
        ·
          refine ⟨17709615979136145186176537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11806410652757430124117691 17709615979136145186176537)
          ·
            refine ⟨13282211984352108889632403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17709615979136145186176537 13282211984352108889632403)
            ·
              refine ⟨19923317976528163334448605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13282211984352108889632403 19923317976528163334448605)
              ·
                refine ⟨7471244241198061250418227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19923317976528163334448605 7471244241198061250418227)
                ·
                  refine ⟨11206866361797091875627341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7471244241198061250418227 11206866361797091875627341)
                  ·
                    refine ⟨4202574885673909453360253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11206866361797091875627341 4202574885673909453360253)
                    ·
                      refine ⟨1575965582127716045010095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4202574885673909453360253 1575965582127716045010095)
                      ·
                        rfl

theorem cell23_3069182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_3069182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069182 prefixEnd_3069182 := by exact prefixLift 3069182
  have htrace : WordTrace (prefixWord ++ tailWord_3069182) baseStart_3069182 baseEnd_3069182 := by
    simpa [prefixWord, tailWord_3069182, baseEnd_3069182] using wordTrace_append hprefix tailTrace_3069182
  have hstable : (prefixWord ++ tailWord_3069182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069182).length < 2 ^ (prefixWord ++ tailWord_3069182).sum := by decide
  have hdescent : baseEnd_3069182 < baseStart_3069182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069216 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3069216 : Nat := 118140960795 + 3069216 * 2 ^ 59
def prefixEnd_3069216 : Nat := 4983230072969 + 3 ^ 40 * 3069216 * 2
def baseEnd_3069216 : Nat := 1575983040469968911984939

theorem tailTrace_3069216 : CollatzResearch.WordTrace tailWord_3069216 prefixEnd_3069216 1575983040469968911984939 := by
  unfold tailWord_3069216
  simp only [CollatzResearch.WordTrace]
  refine ⟨55971752024381043602889751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74629002699174724803853001 55971752024381043602889751)
  ·
    refine ⟨83957628036571565404334627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55971752024381043602889751 83957628036571565404334627)
    ·
      refine ⟨125936442054857348106501941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83957628036571565404334627 125936442054857348106501941)
      ·
        refine ⟨11806541442642876384984557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125936442054857348106501941 11806541442642876384984557)
        ·
          refine ⟨4427453040991078644369209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11806541442642876384984557 4427453040991078644369209)
          ·
            refine ⟨3320589780743308983276907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4427453040991078644369209 3320589780743308983276907)
            ·
              refine ⟨4980884671114963474915361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320589780743308983276907 4980884671114963474915361)
              ·
                refine ⟨3735663503336222606186521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4980884671114963474915361 3735663503336222606186521)
                ·
                  refine ⟨2801747627502166954639891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3735663503336222606186521 2801747627502166954639891)
                  ·
                    refine ⟨4202621441253250431959837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2801747627502166954639891 4202621441253250431959837)
                    ·
                      refine ⟨1575983040469968911984939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4202621441253250431959837 1575983040469968911984939)
                      ·
                        rfl

theorem cell23_3069216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3069216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069216 prefixEnd_3069216 := by exact prefixLift 3069216
  have htrace : WordTrace (prefixWord ++ tailWord_3069216) baseStart_3069216 baseEnd_3069216 := by
    simpa [prefixWord, tailWord_3069216, baseEnd_3069216] using wordTrace_append hprefix tailTrace_3069216
  have hstable : (prefixWord ++ tailWord_3069216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069216).length < 2 ^ (prefixWord ++ tailWord_3069216).sum := by decide
  have hdescent : baseEnd_3069216 < baseStart_3069216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069235 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 4]
def baseStart_3069235 : Nat := 118140960795 + 3069235 * 2 ^ 59
def prefixEnd_3069235 : Nat := 4983230072969 + 3 ^ 40 * 3069235 * 2
def baseEnd_3069235 : Nat := 1575992796602404337647351

theorem tailTrace_3069235 : CollatzResearch.WordTrace tailWord_3069235 prefixEnd_3069235 1575992796602404337647351 := by
  unfold tailWord_3069235
  simp only [CollatzResearch.WordTrace]
  refine ⟨111944197035693253450721159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74629464690462168967147439 111944197035693253450721159)
  ·
    refine ⟨167916295553539880176081739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111944197035693253450721159 167916295553539880176081739)
    ·
      refine ⟨251874443330309820264122609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167916295553539880176081739 251874443330309820264122609)
      ·
        refine ⟨188905832497732365198091957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251874443330309820264122609 188905832497732365198091957)
        ·
          refine ⟨17709921796662409237321121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188905832497732365198091957 17709921796662409237321121)
          ·
            refine ⟨13282441347496806927990841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17709921796662409237321121 13282441347496806927990841)
            ·
              refine ⟨9961831010622605195993131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13282441347496806927990841 9961831010622605195993131)
              ·
                refine ⟨14942746515933907793989697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9961831010622605195993131 14942746515933907793989697)
                ·
                  refine ⟨11207059886950430845492273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14942746515933907793989697 11207059886950430845492273)
                  ·
                    refine ⟨8405294915212823134119205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11207059886950430845492273 8405294915212823134119205)
                    ·
                      refine ⟨1575992796602404337647351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8405294915212823134119205 1575992796602404337647351)
                      ·
                        rfl

theorem cell23_3069235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_3069235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069235 prefixEnd_3069235 := by exact prefixLift 3069235
  have htrace : WordTrace (prefixWord ++ tailWord_3069235) baseStart_3069235 baseEnd_3069235 := by
    simpa [prefixWord, tailWord_3069235, baseEnd_3069235] using wordTrace_append hprefix tailTrace_3069235
  have hstable : (prefixWord ++ tailWord_3069235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069235).length < 2 ^ (prefixWord ++ tailWord_3069235).sum := by decide
  have hdescent : baseEnd_3069235 < baseStart_3069235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069285 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_3069285 : Nat := 118140960795 + 3069285 * 2 ^ 59
def prefixEnd_3069285 : Nat := 4983230072969 + 3 ^ 40 * 3069285 * 2
def baseEnd_3069285 : Nat := 1576018470635129142022121

theorem tailTrace_3069285 : CollatzResearch.WordTrace tailWord_3069285 prefixEnd_3069285 1576018470635129142022121 := by
  unfold tailWord_3069285
  simp only [CollatzResearch.WordTrace]
  refine ⟨111946020685512111990041309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74630680457008074660027539 111946020685512111990041309)
  ·
    refine ⟨41979757757067041996265491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111946020685512111990041309 41979757757067041996265491)
    ·
      refine ⟨62969636635600562994398237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41979757757067041996265491 62969636635600562994398237)
      ·
        refine ⟨23613613738350211122899339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62969636635600562994398237 23613613738350211122899339)
        ·
          refine ⟨35420420607525316684349009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23613613738350211122899339 35420420607525316684349009)
          ·
            refine ⟨26565315455643987513261757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35420420607525316684349009 26565315455643987513261757)
            ·
              refine ⟨9961993295866495317473159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26565315455643987513261757 9961993295866495317473159)
              ·
                refine ⟨14942989943799742976209739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9961993295866495317473159 14942989943799742976209739)
                ·
                  refine ⟨22414484915699614464314609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14942989943799742976209739 22414484915699614464314609)
                  ·
                    refine ⟨16810863686774710848235957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22414484915699614464314609 16810863686774710848235957)
                    ·
                      refine ⟨1576018470635129142022121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16810863686774710848235957 1576018470635129142022121)
                      ·
                        rfl

theorem cell23_3069285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_3069285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069285 prefixEnd_3069285 := by exact prefixLift 3069285
  have htrace : WordTrace (prefixWord ++ tailWord_3069285) baseStart_3069285 baseEnd_3069285 := by
    simpa [prefixWord, tailWord_3069285, baseEnd_3069285] using wordTrace_append hprefix tailTrace_3069285
  have hstable : (prefixWord ++ tailWord_3069285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069285).length < 2 ^ (prefixWord ++ tailWord_3069285).sum := by decide
  have hdescent : baseEnd_3069285 < baseStart_3069285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069290 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_3069290 : Nat := 118140960795 + 3069290 * 2 ^ 59
def prefixEnd_3069290 : Nat := 4983230072969 + 3 ^ 40 * 3069290 * 2
def baseEnd_3069290 : Nat := 1576021038038401622459599

theorem tailTrace_3069290 : CollatzResearch.WordTrace tailWord_3069290 prefixEnd_3069290 1576021038038401622459599 := by
  unfold tailWord_3069290
  simp only [CollatzResearch.WordTrace]
  refine ⟨27986550762623499460993331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74630802033662665229315549 27986550762623499460993331)
  ·
    refine ⟨41979826143935249191489997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27986550762623499460993331 41979826143935249191489997)
    ·
      refine ⟨15742434803975718446808749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41979826143935249191489997 15742434803975718446808749)
      ·
        refine ⟨5903413051490894417553281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15742434803975718446808749 5903413051490894417553281)
        ·
          refine ⟨4427559788618170813164961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5903413051490894417553281 4427559788618170813164961)
          ·
            refine ⟨3320669841463628109873721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4427559788618170813164961 3320669841463628109873721)
            ·
              refine ⟨2490502381097721082405291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3320669841463628109873721 2490502381097721082405291)
              ·
                refine ⟨3735753571646581623607937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2490502381097721082405291 3735753571646581623607937)
                ·
                  refine ⟨2801815178734936217705953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3735753571646581623607937 2801815178734936217705953)
                  ·
                    refine ⟨2101361384051202163279465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2801815178734936217705953 2101361384051202163279465)
                    ·
                      refine ⟨1576021038038401622459599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101361384051202163279465 1576021038038401622459599)
                      ·
                        rfl

theorem cell23_3069290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_3069290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069290 prefixEnd_3069290 := by exact prefixLift 3069290
  have htrace : WordTrace (prefixWord ++ tailWord_3069290) baseStart_3069290 baseEnd_3069290 := by
    simpa [prefixWord, tailWord_3069290, baseEnd_3069290] using wordTrace_append hprefix tailTrace_3069290
  have hstable : (prefixWord ++ tailWord_3069290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069290).length < 2 ^ (prefixWord ++ tailWord_3069290).sum := by decide
  have hdescent : baseEnd_3069290 < baseStart_3069290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069295 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 4]
def baseStart_3069295 : Nat := 118140960795 + 3069295 * 2 ^ 59
def prefixEnd_3069295 : Nat := 4983230072969 + 3 ^ 40 * 3069295 * 2
def baseEnd_3069295 : Nat := 1576023605441674102897075

theorem tailTrace_3069295 : CollatzResearch.WordTrace tailWord_3069295 prefixEnd_3069295 1576023605441674102897075 := by
  unfold tailWord_3069295
  simp only [CollatzResearch.WordTrace]
  refine ⟨111946385415475883697905339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74630923610317255798603559 111946385415475883697905339)
  ·
    refine ⟨167919578123213825546858009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111946385415475883697905339 167919578123213825546858009)
    ·
      refine ⟨125939683592410369160143507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167919578123213825546858009 125939683592410369160143507)
      ·
        refine ⟨188909525388615553740215261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125939683592410369160143507 188909525388615553740215261)
        ·
          refine ⟨70841072020730832652580723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188909525388615553740215261 70841072020730832652580723)
          ·
            refine ⟨106261608031096248978871085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70841072020730832652580723 106261608031096248978871085)
            ·
              refine ⟨39848103011661093367076657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106261608031096248978871085 39848103011661093367076657)
              ·
                refine ⟨29886077258745820025307493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39848103011661093367076657 29886077258745820025307493)
                ·
                  refine ⟨5603639486014841254745155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29886077258745820025307493 5603639486014841254745155)
                  ·
                    refine ⟨8405459229022261882117733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5603639486014841254745155 8405459229022261882117733)
                    ·
                      refine ⟨1576023605441674102897075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8405459229022261882117733 1576023605441674102897075)
                      ·
                        rfl

theorem cell23_3069295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_3069295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069295 prefixEnd_3069295 := by exact prefixLift 3069295
  have htrace : WordTrace (prefixWord ++ tailWord_3069295) baseStart_3069295 baseEnd_3069295 := by
    simpa [prefixWord, tailWord_3069295, baseEnd_3069295] using wordTrace_append hprefix tailTrace_3069295
  have hstable : (prefixWord ++ tailWord_3069295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069295).length < 2 ^ (prefixWord ++ tailWord_3069295).sum := by decide
  have hdescent : baseEnd_3069295 < baseStart_3069295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069330 : List Nat := [3, 2, 3, 3, 2, 1, 2, 2, 5]
def baseStart_3069330 : Nat := 118140960795 + 3069330 * 2 ^ 59
def prefixEnd_3069330 : Nat := 4983230072969 + 3 ^ 40 * 3069330 * 2
def baseEnd_3069330 : Nat := 175115730807175718439935

theorem tailTrace_3069330 : CollatzResearch.WordTrace tailWord_3069330 prefixEnd_3069330 175115730807175718439935 := by
  unfold tailWord_3069330
  simp only [CollatzResearch.WordTrace]
  refine ⟨27986915492587271168857361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74631774646899389783619629 27986915492587271168857361)
  ·
    refine ⟨20990186619440453376643021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27986915492587271168857361 20990186619440453376643021)
    ·
      refine ⟨7871319982290170016241133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20990186619440453376643021 7871319982290170016241133)
      ·
        refine ⟨2951744993358813756090425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7871319982290170016241133 2951744993358813756090425)
        ·
          refine ⟨2213808745019110317067819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2951744993358813756090425 2213808745019110317067819)
          ·
            refine ⟨3320713117528665475601729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213808745019110317067819 3320713117528665475601729)
            ·
              refine ⟨2490534838146499106701297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3320713117528665475601729 2490534838146499106701297)
              ·
                refine ⟨1867901128609874330025973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490534838146499106701297 1867901128609874330025973)
                ·
                  refine ⟨175115730807175718439935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1867901128609874330025973 175115730807175718439935)
                  ·
                    rfl

theorem cell23_3069330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_3069330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069330 prefixEnd_3069330 := by exact prefixLift 3069330
  have htrace : WordTrace (prefixWord ++ tailWord_3069330) baseStart_3069330 baseEnd_3069330 := by
    simpa [prefixWord, tailWord_3069330, baseEnd_3069330] using wordTrace_append hprefix tailTrace_3069330
  have hstable : (prefixWord ++ tailWord_3069330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069330).length < 2 ^ (prefixWord ++ tailWord_3069330).sum := by decide
  have hdescent : baseEnd_3069330 < baseStart_3069330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069419 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 5, 2, 2]
def baseStart_3069419 : Nat := 118140960795 + 3069419 * 2 ^ 59
def prefixEnd_3069419 : Nat := 4983230072969 + 3 ^ 40 * 3069419 * 2
def baseEnd_3069419 : Nat := 1576087277042831617746505

theorem tailTrace_3069419 : CollatzResearch.WordTrace tailWord_3069419 prefixEnd_3069419 1576087277042831617746505 := by
  unfold tailWord_3069419
  simp only [CollatzResearch.WordTrace]
  refine ⟨111950908067026652875419311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74633938711351101916946207 111950908067026652875419311)
  ·
    refine ⟨167926362100539979313128967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111950908067026652875419311 167926362100539979313128967)
    ·
      refine ⟨251889543150809968969693451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167926362100539979313128967 251889543150809968969693451)
      ·
        refine ⟨377834314726214953454540177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251889543150809968969693451 377834314726214953454540177)
        ·
          refine ⟨283375736044661215090905133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377834314726214953454540177 283375736044661215090905133)
          ·
            refine ⟨106265901016747955659089425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283375736044661215090905133 106265901016747955659089425)
            ·
              refine ⟨79699425762560966744317069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106265901016747955659089425 79699425762560966744317069)
              ·
                refine ⟨29887284660960362529118901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79699425762560966744317069 29887284660960362529118901)
                ·
                  refine ⟨2801932936965033987104897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29887284660960362529118901 2801932936965033987104897)
                  ·
                    refine ⟨2101449702723775490328673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2801932936965033987104897 2101449702723775490328673)
                    ·
                      refine ⟨1576087277042831617746505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101449702723775490328673 1576087277042831617746505)
                      ·
                        rfl

theorem cell23_3069419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 2, 2].length) (baseStart_3069419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069419 prefixEnd_3069419 := by exact prefixLift 3069419
  have htrace : WordTrace (prefixWord ++ tailWord_3069419) baseStart_3069419 baseEnd_3069419 := by
    simpa [prefixWord, tailWord_3069419, baseEnd_3069419] using wordTrace_append hprefix tailTrace_3069419
  have hstable : (prefixWord ++ tailWord_3069419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069419).length < 2 ^ (prefixWord ++ tailWord_3069419).sum := by decide
  have hdescent : baseEnd_3069419 < baseStart_3069419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069422 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_3069422 : Nat := 118140960795 + 3069422 * 2 ^ 59
def prefixEnd_3069422 : Nat := 4983230072969 + 3 ^ 40 * 3069422 * 2
def baseEnd_3069422 : Nat := 1576088817484795106008991

theorem tailTrace_3069422 : CollatzResearch.WordTrace tailWord_3069422 prefixEnd_3069422 1576088817484795106008991 := by
  unfold tailWord_3069422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13993877185751973048472315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74634011657343856258519013 13993877185751973048472315)
  ·
    refine ⟨20990815778627959572708473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13993877185751973048472315 20990815778627959572708473)
    ·
      refine ⟨15743111833970969679531355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20990815778627959572708473 15743111833970969679531355)
      ·
        refine ⟨23614667750956454519297033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15743111833970969679531355 23614667750956454519297033)
        ·
          refine ⟨17711000813217340889472775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23614667750956454519297033 17711000813217340889472775)
          ·
            refine ⟨26566501219826011334209163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17711000813217340889472775 26566501219826011334209163)
            ·
              refine ⟨39849751829739017001313745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26566501219826011334209163 39849751829739017001313745)
              ·
                refine ⟨29887313872304262750985309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39849751829739017001313745 29887313872304262750985309)
                ·
                  refine ⟨11207742702114098531619491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29887313872304262750985309 11207742702114098531619491)
                  ·
                    refine ⟨16811614053171147797429237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11207742702114098531619491 16811614053171147797429237)
                    ·
                      refine ⟨1576088817484795106008991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16811614053171147797429237 1576088817484795106008991)
                      ·
                        rfl

theorem cell23_3069422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_3069422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069422 prefixEnd_3069422 := by exact prefixLift 3069422
  have htrace : WordTrace (prefixWord ++ tailWord_3069422) baseStart_3069422 baseEnd_3069422 := by
    simpa [prefixWord, tailWord_3069422, baseEnd_3069422] using wordTrace_append hprefix tailTrace_3069422
  have hstable : (prefixWord ++ tailWord_3069422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069422).length < 2 ^ (prefixWord ++ tailWord_3069422).sum := by decide
  have hdescent : baseEnd_3069422 < baseStart_3069422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069430 : List Nat := [5, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_3069430 : Nat := 118140960795 + 3069430 * 2 ^ 59
def prefixEnd_3069430 : Nat := 4983230072969 + 3 ^ 40 * 3069430 * 2
def baseEnd_3069430 : Nat := 1576092925330031074708955

theorem tailTrace_3069430 : CollatzResearch.WordTrace tailWord_3069430 prefixEnd_3069430 1576092925330031074708955 := by
  unfold tailWord_3069430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6996956829374175109629359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74634206179991201169379829 6996956829374175109629359)
  ·
    refine ⟨10495435244061262664444039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6996956829374175109629359 10495435244061262664444039)
    ·
      refine ⟨15743152866091893996666059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10495435244061262664444039 15743152866091893996666059)
      ·
        refine ⟨23614729299137840994999089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15743152866091893996666059 23614729299137840994999089)
        ·
          refine ⟨17711046974353380746249317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23614729299137840994999089 17711046974353380746249317)
          ·
            refine ⟨3320821307691258889921747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17711046974353380746249317 3320821307691258889921747)
            ·
              refine ⟨4981231961536888334882621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320821307691258889921747 4981231961536888334882621)
              ·
                refine ⟨1867961985576333125580983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4981231961536888334882621 1867961985576333125580983)
                ·
                  refine ⟨2801942978364499688371475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867961985576333125580983 2801942978364499688371475)
                  ·
                    refine ⟨4202914467546749532557213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2801942978364499688371475 4202914467546749532557213)
                    ·
                      refine ⟨1576092925330031074708955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4202914467546749532557213 1576092925330031074708955)
                      ·
                        rfl

theorem cell23_3069430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_3069430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069430 prefixEnd_3069430 := by exact prefixLift 3069430
  have htrace : WordTrace (prefixWord ++ tailWord_3069430) baseStart_3069430 baseEnd_3069430 := by
    simpa [prefixWord, tailWord_3069430, baseEnd_3069430] using wordTrace_append hprefix tailTrace_3069430
  have hstable : (prefixWord ++ tailWord_3069430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069430).length < 2 ^ (prefixWord ++ tailWord_3069430).sum := by decide
  have hdescent : baseEnd_3069430 < baseStart_3069430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069469 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_3069469 : Nat := 118140960795 + 3069469 * 2 ^ 59
def prefixEnd_3069469 : Nat := 4983230072969 + 3 ^ 40 * 3069469 * 2
def baseEnd_3069469 : Nat := 1576112951075556422121275

theorem tailTrace_3069469 : CollatzResearch.WordTrace tailWord_3069469 prefixEnd_3069469 1576112951075556422121275 := by
  unfold tailWord_3069469
  simp only [CollatzResearch.WordTrace]
  refine ⟨111952731716845511414739461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74635154477897007609826307 111952731716845511414739461)
  ·
    refine ⟨20991137196908533390263649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111952731716845511414739461 20991137196908533390263649)
    ·
      refine ⟨15743352897681400042697737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20991137196908533390263649 15743352897681400042697737)
      ·
        refine ⟨11807514673261050032023303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15743352897681400042697737 11807514673261050032023303)
        ·
          refine ⟨17711272009891575048034955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11807514673261050032023303 17711272009891575048034955)
          ·
            refine ⟨26566908014837362572052433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17711272009891575048034955 26566908014837362572052433)
            ·
              refine ⟨19925181011128021929039325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26566908014837362572052433 19925181011128021929039325)
              ·
                refine ⟨7471942879173008223389747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19925181011128021929039325 7471942879173008223389747)
                ·
                  refine ⟨11207914318759512335084621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7471942879173008223389747 11207914318759512335084621)
                  ·
                    refine ⟨4202967869534817125656733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11207914318759512335084621 4202967869534817125656733)
                    ·
                      refine ⟨1576112951075556422121275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4202967869534817125656733 1576112951075556422121275)
                      ·
                        rfl

theorem cell23_3069469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_3069469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069469 prefixEnd_3069469 := by exact prefixLift 3069469
  have htrace : WordTrace (prefixWord ++ tailWord_3069469) baseStart_3069469 baseEnd_3069469 := by
    simpa [prefixWord, tailWord_3069469, baseEnd_3069469] using wordTrace_append hprefix tailTrace_3069469
  have hstable : (prefixWord ++ tailWord_3069469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069469).length < 2 ^ (prefixWord ++ tailWord_3069469).sum := by decide
  have hdescent : baseEnd_3069469 < baseStart_3069469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069470 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3069470 : Nat := 118140960795 + 3069470 * 2 ^ 59
def prefixEnd_3069470 : Nat := 4983230072969 + 3 ^ 40 * 3069470 * 2
def baseEnd_3069470 : Nat := 1576113464556210918208771

theorem tailTrace_3069470 : CollatzResearch.WordTrace tailWord_3069470 prefixEnd_3069470 1576113464556210918208771 := by
  unfold tailWord_3069470
  simp only [CollatzResearch.WordTrace]
  refine ⟨13994096023730236073190733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74635178793227925723683909 13994096023730236073190733)
  ·
    refine ⟨5247786008898838527446525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13994096023730236073190733 5247786008898838527446525)
    ·
      refine ⟨1967919753337064447792447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5247786008898838527446525 1967919753337064447792447)
      ·
        refine ⟨2951879630005596671688671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967919753337064447792447 2951879630005596671688671)
        ·
          refine ⟨4427819445008395007533007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951879630005596671688671 4427819445008395007533007)
          ·
            refine ⟨6641729167512592511299511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427819445008395007533007 6641729167512592511299511)
            ·
              refine ⟨9962593751268888766949267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641729167512592511299511 9962593751268888766949267)
              ·
                refine ⟨14943890626903333150423901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9962593751268888766949267 14943890626903333150423901)
                ·
                  refine ⟨5603958985088749931408963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14943890626903333150423901 5603958985088749931408963)
                  ·
                    refine ⟨8405938477633124897113445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5603958985088749931408963 8405938477633124897113445)
                    ·
                      refine ⟨1576113464556210918208771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8405938477633124897113445 1576113464556210918208771)
                      ·
                        rfl

theorem cell23_3069470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3069470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069470 prefixEnd_3069470 := by exact prefixLift 3069470
  have htrace : WordTrace (prefixWord ++ tailWord_3069470) baseStart_3069470 baseEnd_3069470 := by
    simpa [prefixWord, tailWord_3069470, baseEnd_3069470] using wordTrace_append hprefix tailTrace_3069470
  have hstable : (prefixWord ++ tailWord_3069470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069470).length < 2 ^ (prefixWord ++ tailWord_3069470).sum := by decide
  have hdescent : baseEnd_3069470 < baseStart_3069470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069486 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3069486 : Nat := 118140960795 + 3069486 * 2 ^ 59
def prefixEnd_3069486 : Nat := 4983230072969 + 3 ^ 40 * 3069486 * 2
def baseEnd_3069486 : Nat := 1576121680246682855608697

theorem tailTrace_3069486 : CollatzResearch.WordTrace tailWord_3069486 prefixEnd_3069486 1576121680246682855608697 := by
  unfold tailWord_3069486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13994168969722990414763539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74635567838522615545405541 13994168969722990414763539)
  ·
    refine ⟨20991253454584485622145309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13994168969722990414763539 20991253454584485622145309)
    ·
      refine ⟨7871720045469182108304491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20991253454584485622145309 7871720045469182108304491)
      ·
        refine ⟨11807580068203773162456737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7871720045469182108304491 11807580068203773162456737)
        ·
          refine ⟨8855685051152829871842553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11807580068203773162456737 8855685051152829871842553)
          ·
            refine ⟨6641763788364622403881915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8855685051152829871842553 6641763788364622403881915)
            ·
              refine ⟨9962645682546933605822873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641763788364622403881915 9962645682546933605822873)
              ·
                refine ⟨7471984261910200204367155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9962645682546933605822873 7471984261910200204367155)
                ·
                  refine ⟨11207976392865300306550733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7471984261910200204367155 11207976392865300306550733)
                  ·
                    refine ⟨4202991147324487614956525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11207976392865300306550733 4202991147324487614956525)
                    ·
                      refine ⟨1576121680246682855608697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4202991147324487614956525 1576121680246682855608697)
                      ·
                        rfl

theorem cell23_3069486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3069486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069486 prefixEnd_3069486 := by exact prefixLift 3069486
  have htrace : WordTrace (prefixWord ++ tailWord_3069486) baseStart_3069486 baseEnd_3069486 := by
    simpa [prefixWord, tailWord_3069486, baseEnd_3069486] using wordTrace_append hprefix tailTrace_3069486
  have hstable : (prefixWord ++ tailWord_3069486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069486).length < 2 ^ (prefixWord ++ tailWord_3069486).sum := by decide
  have hdescent : baseEnd_3069486 < baseStart_3069486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069509 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 3, 4, 2]
def baseStart_3069509 : Nat := 118140960795 + 3069509 * 2 ^ 59
def prefixEnd_3069509 : Nat := 4983230072969 + 3 ^ 40 * 3069509 * 2
def baseEnd_3069509 : Nat := 1576133490301736265621091

theorem tailTrace_3069509 : CollatzResearch.WordTrace tailWord_3069509 prefixEnd_3069509 1576133490301736265621091 := by
  unfold tailWord_3069509
  simp only [CollatzResearch.WordTrace]
  refine ⟨111954190636700598246195581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74636127091133732164130387 111954190636700598246195581)
  ·
    refine ⟨41982821488762724342323343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111954190636700598246195581 41982821488762724342323343)
    ·
      refine ⟨62974232233144086513485015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41982821488762724342323343 62974232233144086513485015)
      ·
        refine ⟨94461348349716129770227523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62974232233144086513485015 94461348349716129770227523)
        ·
          refine ⟨141692022524574194655341285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94461348349716129770227523 141692022524574194655341285)
          ·
            refine ⟨26567254223357661497876491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141692022524574194655341285 26567254223357661497876491)
            ·
              refine ⟨39850881335036492246814737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26567254223357661497876491 39850881335036492246814737)
              ·
                refine ⟨29888161001277369185111053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39850881335036492246814737 29888161001277369185111053)
                ·
                  refine ⟨11208060375479013444416645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29888161001277369185111053 11208060375479013444416645)
                  ·
                    refine ⟨2101511320402315020828121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11208060375479013444416645 2101511320402315020828121)
                    ·
                      refine ⟨1576133490301736265621091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101511320402315020828121 1576133490301736265621091)
                      ·
                        rfl

theorem cell23_3069509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 4, 2].length) (baseStart_3069509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069509 prefixEnd_3069509 := by exact prefixLift 3069509
  have htrace : WordTrace (prefixWord ++ tailWord_3069509) baseStart_3069509 baseEnd_3069509 := by
    simpa [prefixWord, tailWord_3069509, baseEnd_3069509] using wordTrace_append hprefix tailTrace_3069509
  have hstable : (prefixWord ++ tailWord_3069509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069509).length < 2 ^ (prefixWord ++ tailWord_3069509).sum := by decide
  have hdescent : baseEnd_3069509 < baseStart_3069509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069626 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 3, 4]
def baseStart_3069626 : Nat := 118140960795 + 3069626 * 2 ^ 59
def prefixEnd_3069626 : Nat := 4983230072969 + 3 ^ 40 * 3069626 * 2
def baseEnd_3069626 : Nat := 525397855846104102619351

theorem tailTrace_3069626 : CollatzResearch.WordTrace tailWord_3069626 prefixEnd_3069626 525397855846104102619351 := by
  unfold tailWord_3069626
  simp only [CollatzResearch.WordTrace]
  refine ⟨27989614494319181807051183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74638971984851151485469821 27989614494319181807051183)
  ·
    refine ⟨41984421741478772710576775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27989614494319181807051183 41984421741478772710576775)
    ·
      refine ⟨62976632612218159065865163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41984421741478772710576775 62976632612218159065865163)
      ·
        refine ⟨94464948918327238598797745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62976632612218159065865163 94464948918327238598797745)
        ·
          refine ⟨70848711688745428949098309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94464948918327238598797745 70848711688745428949098309)
          ·
            refine ⟨13284133441639767927955933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70848711688745428949098309 13284133441639767927955933)
            ·
              refine ⟨4981550040614912972983475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13284133441639767927955933 4981550040614912972983475)
              ·
                refine ⟨7472325060922369459475213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4981550040614912972983475 7472325060922369459475213)
                ·
                  refine ⟨2802121897845888547303205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7472325060922369459475213 2802121897845888547303205)
                  ·
                    refine ⟨525397855846104102619351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2802121897845888547303205 525397855846104102619351)
                    ·
                      rfl

theorem cell23_3069626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_3069626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069626 prefixEnd_3069626 := by exact prefixLift 3069626
  have htrace : WordTrace (prefixWord ++ tailWord_3069626) baseStart_3069626 baseEnd_3069626 := by
    simpa [prefixWord, tailWord_3069626, baseEnd_3069626] using wordTrace_append hprefix tailTrace_3069626
  have hstable : (prefixWord ++ tailWord_3069626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069626).length < 2 ^ (prefixWord ++ tailWord_3069626).sum := by decide
  have hdescent : baseEnd_3069626 < baseStart_3069626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069636 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3069636 : Nat := 118140960795 + 3069636 * 2 ^ 59
def prefixEnd_3069636 : Nat := 4983230072969 + 3 ^ 40 * 3069636 * 2
def baseEnd_3069636 : Nat := 1576198702344857268733007

theorem tailTrace_3069636 : CollatzResearch.WordTrace tailWord_3069636 prefixEnd_3069636 1576198702344857268733007 := by
  unfold tailWord_3069636
  simp only [CollatzResearch.WordTrace]
  refine ⟨55979411353620249468034381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74639215138160332624045841 55979411353620249468034381)
  ·
    refine ⟨20992279257607593550512893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55979411353620249468034381 20992279257607593550512893)
    ·
      refine ⟨7872104721602847581442335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20992279257607593550512893 7872104721602847581442335)
      ·
        refine ⟨11808157082404271372163503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7872104721602847581442335 11808157082404271372163503)
        ·
          refine ⟨17712235623606407058245255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11808157082404271372163503 17712235623606407058245255)
          ·
            refine ⟨26568353435409610587367883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17712235623606407058245255 26568353435409610587367883)
            ·
              refine ⟨39852530153114415881051825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26568353435409610587367883 39852530153114415881051825)
              ·
                refine ⟨29889397614835811910788869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39852530153114415881051825 29889397614835811910788869)
                ·
                  refine ⟨5604262052781714733272913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29889397614835811910788869 5604262052781714733272913)
                  ·
                    refine ⟨4203196539586286049954685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5604262052781714733272913 4203196539586286049954685)
                    ·
                      refine ⟨1576198702344857268733007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4203196539586286049954685 1576198702344857268733007)
                      ·
                        rfl

theorem cell23_3069636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3069636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069636 prefixEnd_3069636 := by exact prefixLift 3069636
  have htrace : WordTrace (prefixWord ++ tailWord_3069636) baseStart_3069636 baseEnd_3069636 := by
    simpa [prefixWord, tailWord_3069636, baseEnd_3069636] using wordTrace_append hprefix tailTrace_3069636
  have hstable : (prefixWord ++ tailWord_3069636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069636).length < 2 ^ (prefixWord ++ tailWord_3069636).sum := by decide
  have hdescent : baseEnd_3069636 < baseStart_3069636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069639 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 6]
def baseStart_3069639 : Nat := 118140960795 + 3069639 * 2 ^ 59
def prefixEnd_3069639 : Nat := 4983230072969 + 3 ^ 40 * 3069639 * 2
def baseEnd_3069639 : Nat := 175133360309646750777277

theorem tailTrace_3069639 : CollatzResearch.WordTrace tailWord_3069639 prefixEnd_3069639 175133360309646750777277 := by
  unfold tailWord_3069639
  simp only [CollatzResearch.WordTrace]
  refine ⟨111958932126229630448427971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74639288084153086965618647 111958932126229630448427971)
  ·
    refine ⟨167938398189344445672641957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111958932126229630448427971 167938398189344445672641957)
    ·
      refine ⟨31488449660502083563620367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167938398189344445672641957 31488449660502083563620367)
      ·
        refine ⟨47232674490753125345430551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31488449660502083563620367 47232674490753125345430551)
        ·
          refine ⟨70849011736129688018145827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47232674490753125345430551 70849011736129688018145827)
          ·
            refine ⟨106273517604194532027218741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70849011736129688018145827 106273517604194532027218741)
            ·
              refine ⟨9963142275393237377551757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106273517604194532027218741 9963142275393237377551757)
              ·
                refine ⟨3736178353272464016581909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9963142275393237377551757 3736178353272464016581909)
                ·
                  refine ⟨175133360309646750777277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3736178353272464016581909 175133360309646750777277)
                  ·
                    rfl

theorem cell23_3069639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 6].length) (baseStart_3069639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069639 prefixEnd_3069639 := by exact prefixLift 3069639
  have htrace : WordTrace (prefixWord ++ tailWord_3069639) baseStart_3069639 baseEnd_3069639 := by
    simpa [prefixWord, tailWord_3069639, baseEnd_3069639] using wordTrace_append hprefix tailTrace_3069639
  have hstable : (prefixWord ++ tailWord_3069639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069639).length < 2 ^ (prefixWord ++ tailWord_3069639).sum := by decide
  have hdescent : baseEnd_3069639 < baseStart_3069639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069677 : List Nat := [1, 5, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_3069677 : Nat := 118140960795 + 3069677 * 2 ^ 59
def prefixEnd_3069677 : Nat := 4983230072969 + 3 ^ 40 * 3069677 * 2
def baseEnd_3069677 : Nat := 525406585017230536106773

theorem tailTrace_3069677 : CollatzResearch.WordTrace tailWord_3069677 prefixEnd_3069677 525406585017230536106773 := by
  unfold tailWord_3069677
  simp only [CollatzResearch.WordTrace]
  refine ⟨111960318100091962938311285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74640212066727975292207523 111960318100091962938311285)
  ·
    refine ⟨10496279821883621525466683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111960318100091962938311285 10496279821883621525466683)
    ·
      refine ⟨15744419732825432288200025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10496279821883621525466683 15744419732825432288200025)
      ·
        refine ⟨11808314799619074216150019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15744419732825432288200025 11808314799619074216150019)
        ·
          refine ⟨17712472199428611324225029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11808314799619074216150019 17712472199428611324225029)
          ·
            refine ⟨3321088537392864623292193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17712472199428611324225029 3321088537392864623292193)
            ·
              refine ⟨2490816403044648467469145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3321088537392864623292193 2490816403044648467469145)
              ·
                refine ⟨1868112302283486350601859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490816403044648467469145 1868112302283486350601859)
                ·
                  refine ⟨2802168453425229525902789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868112302283486350601859 2802168453425229525902789)
                  ·
                    refine ⟨525406585017230536106773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2802168453425229525902789 525406585017230536106773)
                    ·
                      rfl

theorem cell23_3069677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_3069677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069677 prefixEnd_3069677 := by exact prefixLift 3069677
  have htrace : WordTrace (prefixWord ++ tailWord_3069677) baseStart_3069677 baseEnd_3069677 := by
    simpa [prefixWord, tailWord_3069677, baseEnd_3069677] using wordTrace_append hprefix tailTrace_3069677
  have hstable : (prefixWord ++ tailWord_3069677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069677).length < 2 ^ (prefixWord ++ tailWord_3069677).sum := by decide
  have hdescent : baseEnd_3069677 < baseStart_3069677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069686 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_3069686 : Nat := 118140960795 + 3069686 * 2 ^ 59
def prefixEnd_3069686 : Nat := 4983230072969 + 3 ^ 40 * 3069686 * 2
def baseEnd_3069686 : Nat := 525408125459194024369259

theorem tailTrace_3069686 : CollatzResearch.WordTrace tailWord_3069686 prefixEnd_3069686 525408125459194024369259 := by
  unfold tailWord_3069686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6997540397316209842211807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74640430904706238316925941 6997540397316209842211807)
  ·
    refine ⟨10496310595974314763317711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6997540397316209842211807 10496310595974314763317711)
    ·
      refine ⟨15744465893961472144976567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10496310595974314763317711 15744465893961472144976567)
      ·
        refine ⟨23616698840942208217464851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15744465893961472144976567 23616698840942208217464851)
        ·
          refine ⟨35425048261413312326197277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23616698840942208217464851 35425048261413312326197277)
          ·
            refine ⟨13284393098029992122323979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35425048261413312326197277 13284393098029992122323979)
            ·
              refine ⟨19926589647044988183485969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13284393098029992122323979 19926589647044988183485969)
              ·
                refine ⟨14944942235283741137614477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19926589647044988183485969 14944942235283741137614477)
                ·
                  refine ⟨5604353338231402926605429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14944942235283741137614477 5604353338231402926605429)
                  ·
                    refine ⟨525408125459194024369259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5604353338231402926605429 525408125459194024369259)
                    ·
                      rfl

theorem cell23_3069686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_3069686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069686 prefixEnd_3069686 := by exact prefixLift 3069686
  have htrace : WordTrace (prefixWord ++ tailWord_3069686) baseStart_3069686 baseEnd_3069686 := by
    simpa [prefixWord, tailWord_3069686, baseEnd_3069686] using wordTrace_append hprefix tailTrace_3069686
  have hstable : (prefixWord ++ tailWord_3069686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069686).length < 2 ^ (prefixWord ++ tailWord_3069686).sum := by decide
  have hdescent : baseEnd_3069686 < baseStart_3069686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069699 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 1, 6]
def baseStart_3069699 : Nat := 118140960795 + 3069699 * 2 ^ 59
def prefixEnd_3069699 : Nat := 4983230072969 + 3 ^ 40 * 3069699 * 2
def baseEnd_3069699 : Nat := 525410350542030174081739

theorem tailTrace_3069699 : CollatzResearch.WordTrace tailWord_3069699 prefixEnd_3069699 525410350542030174081739 := by
  unfold tailWord_3069699
  simp only [CollatzResearch.WordTrace]
  refine ⟨111961120506012260695612151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74640747004008173797074767 111961120506012260695612151)
  ·
    refine ⟨167941680759018391043418227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111961120506012260695612151 167941680759018391043418227)
    ·
      refine ⟨251912521138527586565127341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167941680759018391043418227 251912521138527586565127341)
      ·
        refine ⟨94467195426947844961922753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251912521138527586565127341 94467195426947844961922753)
        ·
          refine ⟨70850396570210883721442065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94467195426947844961922753 70850396570210883721442065)
          ·
            refine ⟨53137797427658162791081549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70850396570210883721442065 53137797427658162791081549)
            ·
              refine ⟨19926674035371811046655581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53137797427658162791081549 19926674035371811046655581)
              ·
                refine ⟨7472502763264429142495843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19926674035371811046655581 7472502763264429142495843)
                ·
                  refine ⟨11208754144896643713743765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7472502763264429142495843 11208754144896643713743765)
                  ·
                    refine ⟨525410350542030174081739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11208754144896643713743765 525410350542030174081739)
                    ·
                      rfl

theorem cell23_3069699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 6].length) (baseStart_3069699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069699 prefixEnd_3069699 := by exact prefixLift 3069699
  have htrace : WordTrace (prefixWord ++ tailWord_3069699) baseStart_3069699 baseEnd_3069699 := by
    simpa [prefixWord, tailWord_3069699, baseEnd_3069699] using wordTrace_append hprefix tailTrace_3069699
  have hstable : (prefixWord ++ tailWord_3069699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069699).length < 2 ^ (prefixWord ++ tailWord_3069699).sum := by decide
  have hdescent : baseEnd_3069699 < baseStart_3069699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069706 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_3069706 : Nat := 118140960795 + 3069706 * 2 ^ 59
def prefixEnd_3069706 : Nat := 4983230072969 + 3 ^ 40 * 3069706 * 2
def baseEnd_3069706 : Nat := 1576234645990671994857685

theorem tailTrace_3069706 : CollatzResearch.WordTrace tailWord_3069706 prefixEnd_3069706 1576234645990671994857685 := by
  unfold tailWord_3069706
  simp only [CollatzResearch.WordTrace]
  refine ⟨27990343954246725222779243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74640917211324600594077981 27990343954246725222779243)
  ·
    refine ⟨41985515931370087834168865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27990343954246725222779243 41985515931370087834168865)
    ·
      refine ⟨31489136948527565875626649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41985515931370087834168865 31489136948527565875626649)
      ·
        refine ⟨23616852711395674406719987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31489136948527565875626649 23616852711395674406719987)
        ·
          refine ⟨35425279067093511610079981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23616852711395674406719987 35425279067093511610079981)
          ·
            refine ⟨13284479650160066853779993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35425279067093511610079981 13284479650160066853779993)
            ·
              refine ⟨9963359737620050140334995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13284479650160066853779993 9963359737620050140334995)
              ·
                refine ⟨14945039606430075210502493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9963359737620050140334995 14945039606430075210502493)
                ·
                  refine ⟨5604389852411278203938435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14945039606430075210502493 5604389852411278203938435)
                  ·
                    refine ⟨8406584778616917305907653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5604389852411278203938435 8406584778616917305907653)
                    ·
                      refine ⟨1576234645990671994857685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8406584778616917305907653 1576234645990671994857685)
                      ·
                        rfl

theorem cell23_3069706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_3069706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069706 prefixEnd_3069706 := by exact prefixLift 3069706
  have htrace : WordTrace (prefixWord ++ tailWord_3069706) baseStart_3069706 baseEnd_3069706 := by
    simpa [prefixWord, tailWord_3069706, baseEnd_3069706] using wordTrace_append hprefix tailTrace_3069706
  have hstable : (prefixWord ++ tailWord_3069706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069706).length < 2 ^ (prefixWord ++ tailWord_3069706).sum := by decide
  have hdescent : baseEnd_3069706 < baseStart_3069706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069729 : List Nat := [1, 2, 3, 2, 1, 4, 10]
def baseStart_3069729 : Nat := 118140960795 + 3069729 * 2 ^ 59
def prefixEnd_3069729 : Nat := 4983230072969 + 3 ^ 40 * 3069729 * 2
def baseEnd_3069729 : Nat := 19459832790687967961359

theorem tailTrace_3069729 : CollatzResearch.WordTrace tailWord_3069729 prefixEnd_3069729 19459832790687967961359 := by
  unfold tailWord_3069729
  simp only [CollatzResearch.WordTrace]
  refine ⟨111962214695903575819204241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74641476463935717212802827 111962214695903575819204241)
  ·
    refine ⟨83971661021927681864403181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111962214695903575819204241 83971661021927681864403181)
    ·
      refine ⟨31489372883222880699151193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83971661021927681864403181 31489372883222880699151193)
      ·
        refine ⟨23617029662417160524363395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31489372883222880699151193 23617029662417160524363395)
        ·
          refine ⟨35425544493625740786545093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23617029662417160524363395 35425544493625740786545093)
          ·
            refine ⟨6642289592554826397477205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35425544493625740786545093 6642289592554826397477205)
            ·
              refine ⟨19459832790687967961359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6642289592554826397477205 19459832790687967961359)
              ·
                rfl

theorem cell23_3069729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 10].length) (baseStart_3069729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069729 prefixEnd_3069729 := by exact prefixLift 3069729
  have htrace : WordTrace (prefixWord ++ tailWord_3069729) baseStart_3069729 baseEnd_3069729 := by
    simpa [prefixWord, tailWord_3069729, baseEnd_3069729] using wordTrace_append hprefix tailTrace_3069729
  have hstable : (prefixWord ++ tailWord_3069729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069729).length < 2 ^ (prefixWord ++ tailWord_3069729).sum := by decide
  have hdescent : baseEnd_3069729 < baseStart_3069729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069733 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 2, 4]
def baseStart_3069733 : Nat := 118140960795 + 3069733 * 2 ^ 59
def prefixEnd_3069733 : Nat := 4983230072969 + 3 ^ 40 * 3069733 * 2
def baseEnd_3069733 : Nat := 525416169989447796406687

theorem tailTrace_3069733 : CollatzResearch.WordTrace tailWord_3069733 prefixEnd_3069733 525416169989447796406687 := by
  unfold tailWord_3069733
  simp only [CollatzResearch.WordTrace]
  refine ⟨111962360587889084502349853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74641573725259389668233235 111962360587889084502349853)
  ·
    refine ⟨41985885220458406688381195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111962360587889084502349853 41985885220458406688381195)
    ·
      refine ⟨62978827830687610032571793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41985885220458406688381195 62978827830687610032571793)
      ·
        refine ⟨47234120873015707524428845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62978827830687610032571793 47234120873015707524428845)
        ·
          refine ⟨17712795327380890321660817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47234120873015707524428845 17712795327380890321660817)
          ·
            refine ⟨13284596495535667741245613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17712795327380890321660817 13284596495535667741245613)
            ·
              refine ⟨4981723685825875402967105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13284596495535667741245613 4981723685825875402967105)
              ·
                refine ⟨3736292764369406552225329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4981723685825875402967105 3736292764369406552225329)
                ·
                  refine ⟨2802219573277054914168997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3736292764369406552225329 2802219573277054914168997)
                  ·
                    refine ⟨525416169989447796406687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2802219573277054914168997 525416169989447796406687)
                    ·
                      rfl

theorem cell23_3069733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_3069733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069733 prefixEnd_3069733 := by exact prefixLift 3069733
  have htrace : WordTrace (prefixWord ++ tailWord_3069733) baseStart_3069733 baseEnd_3069733 := by
    simpa [prefixWord, tailWord_3069733, baseEnd_3069733] using wordTrace_append hprefix tailTrace_3069733
  have hstable : (prefixWord ++ tailWord_3069733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069733).length < 2 ^ (prefixWord ++ tailWord_3069733).sum := by decide
  have hdescent : baseEnd_3069733 < baseStart_3069733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069740 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 3, 2, 2]
def baseStart_3069740 : Nat := 118140960795 + 3069740 * 2 ^ 59
def prefixEnd_3069740 : Nat := 4983230072969 + 3 ^ 40 * 3069740 * 2
def baseEnd_3069740 : Nat := 1576252104332924861832529

theorem tailTrace_3069740 : CollatzResearch.WordTrace tailWord_3069740 prefixEnd_3069740 1576252104332924861832529 := by
  unfold tailWord_3069740
  simp only [CollatzResearch.WordTrace]
  refine ⟨55981307949431862348927337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74641743932575816465236449 55981307949431862348927337)
  ·
    refine ⟨41985980962073896761695503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55981307949431862348927337 41985980962073896761695503)
    ·
      refine ⟨62978971443110845142543255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41985980962073896761695503 62978971443110845142543255)
      ·
        refine ⟨94468457164666267713814883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62978971443110845142543255 94468457164666267713814883)
        ·
          refine ⟨141702685746999401570722325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94468457164666267713814883 141702685746999401570722325)
          ·
            refine ⟨6642313394390596948627609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141702685746999401570722325 6642313394390596948627609)
            ·
              refine ⟨4981735045792947711470707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6642313394390596948627609 4981735045792947711470707)
              ·
                refine ⟨7472602568689421567206061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4981735045792947711470707 7472602568689421567206061)
                ·
                  refine ⟨2802225963258533087702273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7472602568689421567206061 2802225963258533087702273)
                  ·
                    refine ⟨2101669472443899815776705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2802225963258533087702273 2101669472443899815776705)
                    ·
                      refine ⟨1576252104332924861832529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101669472443899815776705 1576252104332924861832529)
                      ·
                        rfl

theorem cell23_3069740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 2, 2].length) (baseStart_3069740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069740 prefixEnd_3069740 := by exact prefixLift 3069740
  have htrace : WordTrace (prefixWord ++ tailWord_3069740) baseStart_3069740 baseEnd_3069740 := by
    simpa [prefixWord, tailWord_3069740, baseEnd_3069740] using wordTrace_append hprefix tailTrace_3069740
  have hstable : (prefixWord ++ tailWord_3069740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069740).length < 2 ^ (prefixWord ++ tailWord_3069740).sum := by decide
  have hdescent : baseEnd_3069740 < baseStart_3069740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069750 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_3069750 : Nat := 118140960795 + 3069750 * 2 ^ 59
def prefixEnd_3069750 : Nat := 4983230072969 + 3 ^ 40 * 3069750 * 2
def baseEnd_3069750 : Nat := 525419079713156607569161

theorem tailTrace_3069750 : CollatzResearch.WordTrace tailWord_3069750 prefixEnd_3069750 525419079713156607569161 := by
  unfold tailWord_3069750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6997686289301718525357419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74641987085884997603812469 6997686289301718525357419)
  ·
    refine ⟨10496529433952577788036129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6997686289301718525357419 10496529433952577788036129)
    ·
      refine ⟨7872397075464433341027097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10496529433952577788036129 7872397075464433341027097)
      ·
        refine ⟨5904297806598325005770323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7872397075464433341027097 5904297806598325005770323)
        ·
          refine ⟨8856446709897487508655485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5904297806598325005770323 8856446709897487508655485)
          ·
            refine ⟨3321167516211557815745807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8856446709897487508655485 3321167516211557815745807)
            ·
              refine ⟨4981751274317336723618711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321167516211557815745807 4981751274317336723618711)
              ·
                refine ⟨7472626911476005085428067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4981751274317336723618711 7472626911476005085428067)
                ·
                  refine ⟨11208940367214007628142101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7472626911476005085428067 11208940367214007628142101)
                  ·
                    refine ⟨525419079713156607569161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11208940367214007628142101 525419079713156607569161)
                    ·
                      rfl

theorem cell23_3069750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_3069750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069750 prefixEnd_3069750 := by exact prefixLift 3069750
  have htrace : WordTrace (prefixWord ++ tailWord_3069750) baseStart_3069750 baseEnd_3069750 := by
    simpa [prefixWord, tailWord_3069750, baseEnd_3069750] using wordTrace_append hprefix tailTrace_3069750
  have hstable : (prefixWord ++ tailWord_3069750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069750).length < 2 ^ (prefixWord ++ tailWord_3069750).sum := by decide
  have hdescent : baseEnd_3069750 < baseStart_3069750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069753 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3069753 : Nat := 118140960795 + 3069753 * 2 ^ 59
def prefixEnd_3069753 : Nat := 4983230072969 + 3 ^ 40 * 3069753 * 2
def baseEnd_3069753 : Nat := 1576258779581433310969969

theorem tailTrace_3069753 : CollatzResearch.WordTrace tailWord_3069753 prefixEnd_3069753 1576258779581433310969969 := by
  unfold tailWord_3069753
  simp only [CollatzResearch.WordTrace]
  refine ⟨111963090047816627918077913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74642060031877751945385275 111963090047816627918077913)
  ·
    refine ⟨83972317535862470938558435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111963090047816627918077913 83972317535862470938558435)
    ·
      refine ⟨125958476303793706407837653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83972317535862470938558435 125958476303793706407837653)
      ·
        refine ⟨2952151788370164993933695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 125958476303793706407837653 2952151788370164993933695)
        ·
          refine ⟨4428227682555247490900543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952151788370164993933695 4428227682555247490900543)
          ·
            refine ⟨6642341523832871236350815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428227682555247490900543 6642341523832871236350815)
            ·
              refine ⟨9963512285749306854526223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6642341523832871236350815 9963512285749306854526223)
              ·
                refine ⟨14945268428623960281789335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9963512285749306854526223 14945268428623960281789335)
                ·
                  refine ⟨22417902642935940422684003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14945268428623960281789335 22417902642935940422684003)
                  ·
                    refine ⟨33626853964403910634026005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22417902642935940422684003 33626853964403910634026005)
                    ·
                      refine ⟨1576258779581433310969969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33626853964403910634026005 1576258779581433310969969)
                      ·
                        rfl

theorem cell23_3069753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3069753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069753 prefixEnd_3069753 := by exact prefixLift 3069753
  have htrace : WordTrace (prefixWord ++ tailWord_3069753) baseStart_3069753 baseEnd_3069753 := by
    simpa [prefixWord, tailWord_3069753, baseEnd_3069753] using wordTrace_append hprefix tailTrace_3069753
  have hstable : (prefixWord ++ tailWord_3069753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069753).length < 2 ^ (prefixWord ++ tailWord_3069753).sum := by decide
  have hdescent : baseEnd_3069753 < baseStart_3069753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069769 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_3069769 : Nat := 118140960795 + 3069769 * 2 ^ 59
def prefixEnd_3069769 : Nat := 4983230072969 + 3 ^ 40 * 3069769 * 2
def baseEnd_3069769 : Nat := 1576266995271905248369895

theorem tailTrace_3069769 : CollatzResearch.WordTrace tailWord_3069769 prefixEnd_3069769 1576266995271905248369895 := by
  unfold tailWord_3069769
  simp only [CollatzResearch.WordTrace]
  refine ⟨111963673615758662650660361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74642449077172441767106907 111963673615758662650660361)
  ·
    refine ⟨83972755211818996987995271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111963673615758662650660361 83972755211818996987995271)
    ·
      refine ⟨125959132817728495481992907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83972755211818996987995271 125959132817728495481992907)
      ·
        refine ⟨188938699226592743222989361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125959132817728495481992907 188938699226592743222989361)
        ·
          refine ⟨141704024419944557417242021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188938699226592743222989361 141704024419944557417242021)
          ·
            refine ⟨26569504578739604515732879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141704024419944557417242021 26569504578739604515732879)
            ·
              refine ⟨39854256868109406773599319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26569504578739604515732879 39854256868109406773599319)
              ·
                refine ⟨59781385302164110160398979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39854256868109406773599319 59781385302164110160398979)
                ·
                  refine ⟨89672077953246165240598469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59781385302164110160398979 89672077953246165240598469)
                  ·
                    refine ⟨16813514616233655982612213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89672077953246165240598469 16813514616233655982612213)
                    ·
                      refine ⟨1576266995271905248369895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16813514616233655982612213 1576266995271905248369895)
                      ·
                        rfl

theorem cell23_3069769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_3069769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069769 prefixEnd_3069769 := by exact prefixLift 3069769
  have htrace : WordTrace (prefixWord ++ tailWord_3069769) baseStart_3069769 baseEnd_3069769 := by
    simpa [prefixWord, tailWord_3069769, baseEnd_3069769] using wordTrace_append hprefix tailTrace_3069769
  have hstable : (prefixWord ++ tailWord_3069769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069769).length < 2 ^ (prefixWord ++ tailWord_3069769).sum := by decide
  have hdescent : baseEnd_3069769 < baseStart_3069769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069779 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 4]
def baseStart_3069779 : Nat := 118140960795 + 3069779 * 2 ^ 59
def prefixEnd_3069779 : Nat := 4983230072969 + 3 ^ 40 * 3069779 * 2
def baseEnd_3069779 : Nat := 1576272130078450209244849

theorem tailTrace_3069779 : CollatzResearch.WordTrace tailWord_3069779 prefixEnd_3069779 1576272130078450209244849 := by
  unfold tailWord_3069779
  simp only [CollatzResearch.WordTrace]
  refine ⟨111964038345722434358524391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74642692230481622905682927 111964038345722434358524391)
  ·
    refine ⟨167946057518583651537786587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111964038345722434358524391 167946057518583651537786587)
    ·
      refine ⟨251919086277875477306679881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167946057518583651537786587 251919086277875477306679881)
      ·
        refine ⟨188939314708406607980009911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251919086277875477306679881 188939314708406607980009911)
        ·
          refine ⟨283408972062609911970014867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188939314708406607980009911 283408972062609911970014867)
          ·
            refine ⟨425113458093914867955022301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283408972062609911970014867 425113458093914867955022301)
            ·
              refine ⟨159417546785218075483133363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 425113458093914867955022301 159417546785218075483133363)
              ·
                refine ⟨239126320177827113224700045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159417546785218075483133363 239126320177827113224700045)
                ·
                  refine ⟨89672370066685167459262517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239126320177827113224700045 89672370066685167459262517)
                  ·
                    refine ⟨8406784693751734449305861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89672370066685167459262517 8406784693751734449305861)
                    ·
                      refine ⟨1576272130078450209244849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8406784693751734449305861 1576272130078450209244849)
                      ·
                        rfl

theorem cell23_3069779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_3069779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069779 prefixEnd_3069779 := by exact prefixLift 3069779
  have htrace : WordTrace (prefixWord ++ tailWord_3069779) baseStart_3069779 baseEnd_3069779 := by
    simpa [prefixWord, tailWord_3069779, baseEnd_3069779] using wordTrace_append hprefix tailTrace_3069779
  have hstable : (prefixWord ++ tailWord_3069779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069779).length < 2 ^ (prefixWord ++ tailWord_3069779).sum := by decide
  have hdescent : baseEnd_3069779 < baseStart_3069779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069819 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 9]
def baseStart_3069819 : Nat := 118140960795 + 3069819 * 2 ^ 59
def prefixEnd_3069819 : Nat := 4983230072969 + 3 ^ 40 * 3069819 * 2
def baseEnd_3069819 : Nat := 175143629922736672527185

theorem tailTrace_3069819 : CollatzResearch.WordTrace tailWord_3069819 prefixEnd_3069819 175143629922736672527185 := by
  unfold tailWord_3069819
  simp only [CollatzResearch.WordTrace]
  refine ⟨111965497265577521189980511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74643664843718347459987007 111965497265577521189980511)
  ·
    refine ⟨167948245898366281784970767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111965497265577521189980511 167948245898366281784970767)
    ·
      refine ⟨251922368847549422677456151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167948245898366281784970767 251922368847549422677456151)
      ·
        refine ⟨377883553271324134016184227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251922368847549422677456151 377883553271324134016184227)
        ·
          refine ⟨566825329906986201024276341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377883553271324134016184227 566825329906986201024276341)
          ·
            refine ⟨53139874678779956346025907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 566825329906986201024276341 53139874678779956346025907)
            ·
              refine ⟨79709812018169934519038861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53139874678779956346025907 79709812018169934519038861)
              ·
                refine ⟨29891179506813725444639573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79709812018169934519038861 29891179506813725444639573)
                ·
                  refine ⟨175143629922736672527185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29891179506813725444639573 175143629922736672527185)
                  ·
                    rfl

theorem cell23_3069819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 9].length) (baseStart_3069819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069819 prefixEnd_3069819 := by exact prefixLift 3069819
  have htrace : WordTrace (prefixWord ++ tailWord_3069819) baseStart_3069819 baseEnd_3069819 := by
    simpa [prefixWord, tailWord_3069819, baseEnd_3069819] using wordTrace_append hprefix tailTrace_3069819
  have hstable : (prefixWord ++ tailWord_3069819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069819).length < 2 ^ (prefixWord ++ tailWord_3069819).sum := by decide
  have hdescent : baseEnd_3069819 < baseStart_3069819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069834 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2]
def baseStart_3069834 : Nat := 118140960795 + 3069834 * 2 ^ 59
def prefixEnd_3069834 : Nat := 4983230072969 + 3 ^ 40 * 3069834 * 2
def baseEnd_3069834 : Nat := 1576300371514447494057097

theorem tailTrace_3069834 : CollatzResearch.WordTrace tailWord_3069834 prefixEnd_3069834 1576300371514447494057097 := by
  unfold tailWord_3069834
  simp only [CollatzResearch.WordTrace]
  refine ⟨27991511090130794687944139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74644029573682119167851037 27991511090130794687944139)
  ·
    refine ⟨41987266635196192031916209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27991511090130794687944139 41987266635196192031916209)
    ·
      refine ⟨31490449976397144023937157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41987266635196192031916209 31490449976397144023937157)
      ·
        refine ⟨5904459370574464504488217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31490449976397144023937157 5904459370574464504488217)
        ·
          refine ⟨4428344527930848378366163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5904459370574464504488217 4428344527930848378366163)
          ·
            refine ⟨6642516791896272567549245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428344527930848378366163 6642516791896272567549245)
            ·
              refine ⟨2490943796961102212830967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6642516791896272567549245 2490943796961102212830967)
              ·
                refine ⟨3736415695441653319246451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2490943796961102212830967 3736415695441653319246451)
                ·
                  refine ⟨5604623543162479978869677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736415695441653319246451 5604623543162479978869677)
                  ·
                    refine ⟨2101733828685929992076129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5604623543162479978869677 2101733828685929992076129)
                    ·
                      refine ⟨1576300371514447494057097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101733828685929992076129 1576300371514447494057097)
                      ·
                        rfl

theorem cell23_3069834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_3069834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069834 prefixEnd_3069834 := by exact prefixLift 3069834
  have htrace : WordTrace (prefixWord ++ tailWord_3069834) baseStart_3069834 baseEnd_3069834 := by
    simpa [prefixWord, tailWord_3069834, baseEnd_3069834] using wordTrace_append hprefix tailTrace_3069834
  have hstable : (prefixWord ++ tailWord_3069834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069834).length < 2 ^ (prefixWord ++ tailWord_3069834).sum := by decide
  have hdescent : baseEnd_3069834 < baseStart_3069834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069839 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_3069839 : Nat := 118140960795 + 3069839 * 2 ^ 59
def prefixEnd_3069839 : Nat := 4983230072969 + 3 ^ 40 * 3069839 * 2
def baseEnd_3069839 : Nat := 1576302938917719974494573

theorem tailTrace_3069839 : CollatzResearch.WordTrace tailWord_3069839 prefixEnd_3069839 1576302938917719974494573 := by
  unfold tailWord_3069839
  simp only [CollatzResearch.WordTrace]
  refine ⟨111966226725505064605708571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74644151150336709737139047 111966226725505064605708571)
  ·
    refine ⟨167949340088257596908562857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111966226725505064605708571 167949340088257596908562857)
    ·
      refine ⟨125962005066193197681422143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167949340088257596908562857 125962005066193197681422143)
      ·
        refine ⟨188943007599289796522133215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125962005066193197681422143 188943007599289796522133215)
        ·
          refine ⟨283414511398934694783199823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188943007599289796522133215 283414511398934694783199823)
          ·
            refine ⟨425121767098402042174799735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283414511398934694783199823 425121767098402042174799735)
            ·
              refine ⟨637682650647603063262199603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425121767098402042174799735 637682650647603063262199603)
              ·
                refine ⟨956523975971404594893299405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637682650647603063262199603 956523975971404594893299405)
                ·
                  refine ⟨358696490989276723084987277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956523975971404594893299405 358696490989276723084987277)
                  ·
                    refine ⟨134511184120978771156870229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 358696490989276723084987277 134511184120978771156870229)
                    ·
                      refine ⟨1576302938917719974494573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 134511184120978771156870229 1576302938917719974494573)
                      ·
                        rfl

theorem cell23_3069839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_3069839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069839 prefixEnd_3069839 := by exact prefixLift 3069839
  have htrace : WordTrace (prefixWord ++ tailWord_3069839) baseStart_3069839 baseEnd_3069839 := by
    simpa [prefixWord, tailWord_3069839, baseEnd_3069839] using wordTrace_append hprefix tailTrace_3069839
  have hstable : (prefixWord ++ tailWord_3069839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069839).length < 2 ^ (prefixWord ++ tailWord_3069839).sum := by decide
  have hdescent : baseEnd_3069839 < baseStart_3069839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069847 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 2, 2, 2]
def baseStart_3069847 : Nat := 118140960795 + 3069847 * 2 ^ 59
def prefixEnd_3069847 : Nat := 4983230072969 + 3 ^ 40 * 3069847 * 2
def baseEnd_3069847 : Nat := 1576307046762955943194537

theorem tailTrace_3069847 : CollatzResearch.WordTrace tailWord_3069847 prefixEnd_3069847 1576307046762955943194537 := by
  unfold tailWord_3069847
  simp only [CollatzResearch.WordTrace]
  refine ⟨111966518509476081971999795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74644345672984054647999863 111966518509476081971999795)
  ·
    refine ⟨167949777764214122957999693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111966518509476081971999795 167949777764214122957999693)
    ·
      refine ⟨62981166661580296109249885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167949777764214122957999693 62981166661580296109249885)
      ·
        refine ⟨23617937498092611040968707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62981166661580296109249885 23617937498092611040968707)
        ·
          refine ⟨35426906247138916561453061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23617937498092611040968707 35426906247138916561453061)
          ·
            refine ⟨6642544921338546855272449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35426906247138916561453061 6642544921338546855272449)
            ·
              refine ⟨4981908691003910141454337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6642544921338546855272449 4981908691003910141454337)
              ·
                refine ⟨3736431518252932606090753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4981908691003910141454337 3736431518252932606090753)
                ·
                  refine ⟨2802323638689699454568065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3736431518252932606090753 2802323638689699454568065)
                  ·
                    refine ⟨2101742729017274590926049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2802323638689699454568065 2101742729017274590926049)
                    ·
                      refine ⟨1576307046762955943194537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101742729017274590926049 1576307046762955943194537)
                      ·
                        rfl

theorem cell23_3069847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_3069847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069847 prefixEnd_3069847 := by exact prefixLift 3069847
  have htrace : WordTrace (prefixWord ++ tailWord_3069847) baseStart_3069847 baseEnd_3069847 := by
    simpa [prefixWord, tailWord_3069847, baseEnd_3069847] using wordTrace_append hprefix tailTrace_3069847
  have hstable : (prefixWord ++ tailWord_3069847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069847).length < 2 ^ (prefixWord ++ tailWord_3069847).sum := by decide
  have hdescent : baseEnd_3069847 < baseStart_3069847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069863 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_3069863 : Nat := 118140960795 + 3069863 * 2 ^ 59
def prefixEnd_3069863 : Nat := 4983230072969 + 3 ^ 40 * 3069863 * 2
def baseEnd_3069863 : Nat := 1576315262453427880594463

theorem tailTrace_3069863 : CollatzResearch.WordTrace tailWord_3069863 prefixEnd_3069863 1576315262453427880594463 := by
  unfold tailWord_3069863
  simp only [CollatzResearch.WordTrace]
  refine ⟨111967102077418116704582243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74644734718278744469721495 111967102077418116704582243)
  ·
    refine ⟨167950653116127175056873365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111967102077418116704582243 167950653116127175056873365)
    ·
      refine ⟨7872686864818461330790939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 167950653116127175056873365 7872686864818461330790939)
      ·
        refine ⟨11809030297227691996186409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7872686864818461330790939 11809030297227691996186409)
        ·
          refine ⟨8856772722920768997139807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11809030297227691996186409 8856772722920768997139807)
          ·
            refine ⟨13285159084381153495709711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8856772722920768997139807 13285159084381153495709711)
            ·
              refine ⟨19927738626571730243564567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13285159084381153495709711 19927738626571730243564567)
              ·
                refine ⟨29891607939857595365346851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19927738626571730243564567 29891607939857595365346851)
                ·
                  refine ⟨44837411909786393048020277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29891607939857595365346851 44837411909786393048020277)
                  ·
                    refine ⟨4203507366542474348251901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44837411909786393048020277 4203507366542474348251901)
                    ·
                      refine ⟨1576315262453427880594463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4203507366542474348251901 1576315262453427880594463)
                      ·
                        rfl

theorem cell23_3069863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_3069863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069863 prefixEnd_3069863 := by exact prefixLift 3069863
  have htrace : WordTrace (prefixWord ++ tailWord_3069863) baseStart_3069863 baseEnd_3069863 := by
    simpa [prefixWord, tailWord_3069863, baseEnd_3069863] using wordTrace_append hprefix tailTrace_3069863
  have hstable : (prefixWord ++ tailWord_3069863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069863).length < 2 ^ (prefixWord ++ tailWord_3069863).sum := by decide
  have hdescent : baseEnd_3069863 < baseStart_3069863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069864 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3069864 : Nat := 118140960795 + 3069864 * 2 ^ 59
def prefixEnd_3069864 : Nat := 4983230072969 + 3 ^ 40 * 3069864 * 2
def baseEnd_3069864 : Nat := 1576315775934082376681959

theorem tailTrace_3069864 : CollatzResearch.WordTrace tailWord_3069864 prefixEnd_3069864 1576315775934082376681959 := by
  unfold tailWord_3069864
  simp only [CollatzResearch.WordTrace]
  refine ⟨55983569275207246937684323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74644759033609662583579097 55983569275207246937684323)
  ·
    refine ⟨83975353912810870406526485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55983569275207246937684323 83975353912810870406526485)
    ·
      refine ⟨3936344714663009550305929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83975353912810870406526485 3936344714663009550305929)
      ·
        refine ⟨2952258535997257162729447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3936344714663009550305929 2952258535997257162729447)
        ·
          refine ⟨4428387803995885744094171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952258535997257162729447 4428387803995885744094171)
          ·
            refine ⟨6642581705993828616141257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428387803995885744094171 6642581705993828616141257)
            ·
              refine ⟨4981936279495371462105943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6642581705993828616141257 4981936279495371462105943)
              ·
                refine ⟨7472904419243057193158915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4981936279495371462105943 7472904419243057193158915)
                ·
                  refine ⟨11209356628864585789738373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7472904419243057193158915 11209356628864585789738373)
                  ·
                    refine ⟨2101754367912109835575945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11209356628864585789738373 2101754367912109835575945)
                    ·
                      refine ⟨1576315775934082376681959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101754367912109835575945 1576315775934082376681959)
                      ·
                        rfl

theorem cell23_3069864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3069864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069864 prefixEnd_3069864 := by exact prefixLift 3069864
  have htrace : WordTrace (prefixWord ++ tailWord_3069864) baseStart_3069864 baseEnd_3069864 := by
    simpa [prefixWord, tailWord_3069864, baseEnd_3069864] using wordTrace_append hprefix tailTrace_3069864
  have hstable : (prefixWord ++ tailWord_3069864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069864).length < 2 ^ (prefixWord ++ tailWord_3069864).sum := by decide
  have hdescent : baseEnd_3069864 < baseStart_3069864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069903 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 4, 4, 2]
def baseStart_3069903 : Nat := 118140960795 + 3069903 * 2 ^ 59
def prefixEnd_3069903 : Nat := 4983230072969 + 3 ^ 40 * 3069903 * 2
def baseEnd_3069903 : Nat := 1576335801679607724094279

theorem tailTrace_3069903 : CollatzResearch.WordTrace tailWord_3069903 prefixEnd_3069903 1576335801679607724094279 := by
  unfold tailWord_3069903
  simp only [CollatzResearch.WordTrace]
  refine ⟨111968560997273203536038363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74645707331515469024025575 111968560997273203536038363)
  ·
    refine ⟨167952841495909805304057545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111968560997273203536038363 167952841495909805304057545)
    ·
      refine ⟨125964631121932353978043159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167952841495909805304057545 125964631121932353978043159)
      ·
        refine ⟨188946946682898530967064739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125964631121932353978043159 188946946682898530967064739)
        ·
          refine ⟨283420420024347796450597109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188946946682898530967064739 283420420024347796450597109)
          ·
            refine ⟨26570664377282605917243479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 283420420024347796450597109 26570664377282605917243479)
            ·
              refine ⟨39855996565923908875865219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26570664377282605917243479 39855996565923908875865219)
              ·
                refine ⟨59783994848885863313797829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39855996565923908875865219 59783994848885863313797829)
                ·
                  refine ⟨11209499034166099371337093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59783994848885863313797829 11209499034166099371337093)
                  ·
                    refine ⟨2101781068906143632125705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11209499034166099371337093 2101781068906143632125705)
                    ·
                      refine ⟨1576335801679607724094279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101781068906143632125705 1576335801679607724094279)
                      ·
                        rfl

theorem cell23_3069903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 4, 2].length) (baseStart_3069903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069903 prefixEnd_3069903 := by exact prefixLift 3069903
  have htrace : WordTrace (prefixWord ++ tailWord_3069903) baseStart_3069903 baseEnd_3069903 := by
    simpa [prefixWord, tailWord_3069903, baseEnd_3069903] using wordTrace_append hprefix tailTrace_3069903
  have hstable : (prefixWord ++ tailWord_3069903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069903).length < 2 ^ (prefixWord ++ tailWord_3069903).sum := by decide
  have hdescent : baseEnd_3069903 < baseStart_3069903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3069923 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 3]
def baseStart_3069923 : Nat := 118140960795 + 3069923 * 2 ^ 59
def prefixEnd_3069923 : Nat := 4983230072969 + 3 ^ 40 * 3069923 * 2
def baseEnd_3069923 : Nat := 1576346071292697645844187

theorem tailTrace_3069923 : CollatzResearch.WordTrace tailWord_3069923 prefixEnd_3069923 1576346071292697645844187 := by
  unfold tailWord_3069923
  simp only [CollatzResearch.WordTrace]
  refine ⟨111969290457200746951766423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74646193638133831301177615 111969290457200746951766423)
  ·
    refine ⟨167953935685801120427649635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111969290457200746951766423 167953935685801120427649635)
    ·
      refine ⟨251930903528701680641474453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167953935685801120427649635 251930903528701680641474453)
      ·
        refine ⟨11809261102907891280069115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 251930903528701680641474453 11809261102907891280069115)
        ·
          refine ⟨17713891654361836920103673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11809261102907891280069115 17713891654361836920103673)
          ·
            refine ⟨13285418740771377690077755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17713891654361836920103673 13285418740771377690077755)
            ·
              refine ⟨19928128111157066535116633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13285418740771377690077755 19928128111157066535116633)
              ·
                refine ⟨14946096083367799901337475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19928128111157066535116633 14946096083367799901337475)
                ·
                  refine ⟨22419144125051699852006213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14946096083367799901337475 22419144125051699852006213)
                  ·
                    refine ⟨4203589523447193722251165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22419144125051699852006213 4203589523447193722251165)
                    ·
                      refine ⟨1576346071292697645844187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4203589523447193722251165 1576346071292697645844187)
                      ·
                        rfl

theorem cell23_3069923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_3069923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3069923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3069923 prefixEnd_3069923 := by exact prefixLift 3069923
  have htrace : WordTrace (prefixWord ++ tailWord_3069923) baseStart_3069923 baseEnd_3069923 := by
    simpa [prefixWord, tailWord_3069923, baseEnd_3069923] using wordTrace_append hprefix tailTrace_3069923
  have hstable : (prefixWord ++ tailWord_3069923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3069923).length < 2 ^ (prefixWord ++ tailWord_3069923).sum := by decide
  have hdescent : baseEnd_3069923 < baseStart_3069923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3069923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070003 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 6, 4]
def baseStart_3070003 : Nat := 118140960795 + 3070003 * 2 ^ 59
def prefixEnd_3070003 : Nat := 4983230072969 + 3 ^ 40 * 3070003 * 2
def baseEnd_3070003 : Nat := 525462383248352444281273

theorem tailTrace_3070003 : CollatzResearch.WordTrace tailWord_3070003 prefixEnd_3070003 525462383248352444281273 := by
  unfold tailWord_3070003
  simp only [CollatzResearch.WordTrace]
  refine ⟨111972208296910920614678663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74648138864607280409785775 111972208296910920614678663)
  ·
    refine ⟨167958312445366380922017995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111972208296910920614678663 167958312445366380922017995)
    ·
      refine ⟨251937468668049571383026993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167958312445366380922017995 251937468668049571383026993)
      ·
        refine ⟨188953101501037178537270245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251937468668049571383026993 188953101501037178537270245)
        ·
          refine ⟨35428706531444470975738171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188953101501037178537270245 35428706531444470975738171)
          ·
            refine ⟨53143059797166706463607257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35428706531444470975738171 53143059797166706463607257)
            ·
              refine ⟨39857294847875029847705443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53143059797166706463607257 39857294847875029847705443)
              ·
                refine ⟨59785942271812544771558165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39857294847875029847705443 59785942271812544771558165)
                ·
                  refine ⟨2802466043991213036166789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59785942271812544771558165 2802466043991213036166789)
                  ·
                    refine ⟨525462383248352444281273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2802466043991213036166789 525462383248352444281273)
                    ·
                      rfl

theorem cell23_3070003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6, 4].length) (baseStart_3070003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070003 prefixEnd_3070003 := by exact prefixLift 3070003
  have htrace : WordTrace (prefixWord ++ tailWord_3070003) baseStart_3070003 baseEnd_3070003 := by
    simpa [prefixWord, tailWord_3070003, baseEnd_3070003] using wordTrace_append hprefix tailTrace_3070003
  have hstable : (prefixWord ++ tailWord_3070003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070003).length < 2 ^ (prefixWord ++ tailWord_3070003).sum := by decide
  have hdescent : baseEnd_3070003 < baseStart_3070003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070016 : List Nat := [2, 1, 1, 2, 2, 15]
def baseStart_3070016 : Nat := 118140960795 + 3070016 * 2 ^ 59
def prefixEnd_3070016 : Nat := 4983230072969 + 3 ^ 40 * 3070016 * 2
def baseEnd_3070016 : Nat := 6487217386804797456713

theorem tailTrace_3070016 : CollatzResearch.WordTrace tailWord_3070016 prefixEnd_3070016 6487217386804797456713 := by
  unfold tailWord_3070016
  simp only [CollatzResearch.WordTrace]
  refine ⟨55986341222931911917450951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74648454963909215889934601 55986341222931911917450951)
  ·
    refine ⟨83979511834397867876176427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55986341222931911917450951 83979511834397867876176427)
    ·
      refine ⟨125969267751596801814264641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83979511834397867876176427 125969267751596801814264641)
      ·
        refine ⟨94476950813697601360698481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125969267751596801814264641 94476950813697601360698481)
        ·
          refine ⟨70857713110273201020523861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94476950813697601360698481 70857713110273201020523861)
          ·
            refine ⟨6487217386804797456713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 70857713110273201020523861 6487217386804797456713)
            ·
              rfl

theorem cell23_3070016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 15].length) (baseStart_3070016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070016 prefixEnd_3070016 := by exact prefixLift 3070016
  have htrace : WordTrace (prefixWord ++ tailWord_3070016) baseStart_3070016 baseEnd_3070016 := by
    simpa [prefixWord, tailWord_3070016, baseEnd_3070016] using wordTrace_append hprefix tailTrace_3070016
  have hstable : (prefixWord ++ tailWord_3070016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070016).length < 2 ^ (prefixWord ++ tailWord_3070016).sum := by decide
  have hdescent : baseEnd_3070016 < baseStart_3070016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070023 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_3070023 : Nat := 118140960795 + 3070023 * 2 ^ 59
def prefixEnd_3070023 : Nat := 4983230072969 + 3 ^ 40 * 3070023 * 2
def baseEnd_3070023 : Nat := 1576397419358147254593727

theorem tailTrace_3070023 : CollatzResearch.WordTrace tailWord_3070023 prefixEnd_3070023 1576397419358147254593727 := by
  unfold tailWord_3070023
  simp only [CollatzResearch.WordTrace]
  refine ⟨111972937756838464030406723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74648625171225642686937815 111972937756838464030406723)
  ·
    refine ⟨167959406635257696045610085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111972937756838464030406723 167959406635257696045610085)
    ·
      refine ⟨31492388744110818008551891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167959406635257696045610085 31492388744110818008551891)
      ·
        refine ⟨47238583116166227012827837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31492388744110818008551891 47238583116166227012827837)
        ·
          refine ⟨17714468668562335129810439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47238583116166227012827837 17714468668562335129810439)
          ·
            refine ⟨26571703002843502694715659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17714468668562335129810439 26571703002843502694715659)
            ·
              refine ⟨39857554504265254042073489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26571703002843502694715659 39857554504265254042073489)
              ·
                refine ⟨29893165878198940531555117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39857554504265254042073489 29893165878198940531555117)
                ·
                  refine ⟨11209937204324602699333169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29893165878198940531555117 11209937204324602699333169)
                  ·
                    refine ⟨8407452903243452024499877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11209937204324602699333169 8407452903243452024499877)
                    ·
                      refine ⟨1576397419358147254593727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8407452903243452024499877 1576397419358147254593727)
                      ·
                        rfl

theorem cell23_3070023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_3070023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070023 prefixEnd_3070023 := by exact prefixLift 3070023
  have htrace : WordTrace (prefixWord ++ tailWord_3070023) baseStart_3070023 baseEnd_3070023 := by
    simpa [prefixWord, tailWord_3070023, baseEnd_3070023] using wordTrace_append hprefix tailTrace_3070023
  have hstable : (prefixWord ++ tailWord_3070023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070023).length < 2 ^ (prefixWord ++ tailWord_3070023).sum := by decide
  have hdescent : baseEnd_3070023 < baseStart_3070023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070030 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_3070030 : Nat := 118140960795 + 3070030 * 2 ^ 59
def prefixEnd_3070030 : Nat := 4983230072969 + 3 ^ 40 * 3070030 * 2
def baseEnd_3070030 : Nat := 1576401013722728727206195

theorem tailTrace_3070030 : CollatzResearch.WordTrace tailWord_3070030 prefixEnd_3070030 1576401013722728727206195 := by
  unfold tailWord_3070030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13996649133476638028238943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74648795378542069483941029 13996649133476638028238943)
  ·
    refine ⟨20994973700214957042358415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13996649133476638028238943 20994973700214957042358415)
    ·
      refine ⟨31492460550322435563537623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20994973700214957042358415 31492460550322435563537623)
      ·
        refine ⟨47238690825483653345306435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31492460550322435563537623 47238690825483653345306435)
        ·
          refine ⟨70858036238225480017959653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47238690825483653345306435 70858036238225480017959653)
          ·
            refine ⟨13285881794667277503367435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70858036238225480017959653 13285881794667277503367435)
            ·
              refine ⟨19928822692000916255051153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13285881794667277503367435 19928822692000916255051153)
              ·
                refine ⟨14946617019000687191288365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19928822692000916255051153 14946617019000687191288365)
                ·
                  refine ⟨5604981382125257696733137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14946617019000687191288365 5604981382125257696733137)
                  ·
                    refine ⟨4203736036593943272549853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5604981382125257696733137 4203736036593943272549853)
                    ·
                      refine ⟨1576401013722728727206195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4203736036593943272549853 1576401013722728727206195)
                      ·
                        rfl

theorem cell23_3070030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_3070030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070030 prefixEnd_3070030 := by exact prefixLift 3070030
  have htrace : WordTrace (prefixWord ++ tailWord_3070030) baseStart_3070030 baseEnd_3070030 := by
    simpa [prefixWord, tailWord_3070030, baseEnd_3070030] using wordTrace_append hprefix tailTrace_3070030
  have hstable : (prefixWord ++ tailWord_3070030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070030).length < 2 ^ (prefixWord ++ tailWord_3070030).sum := by decide
  have hdescent : baseEnd_3070030 < baseStart_3070030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070040 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 1, 2, 4]
def baseStart_3070040 : Nat := 118140960795 + 3070040 * 2 ^ 59
def prefixEnd_3070040 : Nat := 4983230072969 + 3 ^ 40 * 3070040 * 2
def baseEnd_3070040 : Nat := 1576406148529273688081149

theorem tailTrace_3070040 : CollatzResearch.WordTrace tailWord_3070040 prefixEnd_3070040 1576406148529273688081149 := by
  unfold tailWord_3070040
  simp only [CollatzResearch.WordTrace]
  refine ⟨55986778898888437966887787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74649038531851250622517049 55986778898888437966887787)
  ·
    refine ⟨83980168348332656950331681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55986778898888437966887787 83980168348332656950331681)
    ·
      refine ⟨62985126261249492712748761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83980168348332656950331681 62985126261249492712748761)
      ·
        refine ⟨47238844695937119534561571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62985126261249492712748761 47238844695937119534561571)
        ·
          refine ⟨70858267043905679301842357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47238844695937119534561571 70858267043905679301842357)
          ·
            refine ⟨6642962535366157434547721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70858267043905679301842357 6642962535366157434547721)
            ·
              refine ⟨4982221901524618075910791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6642962535366157434547721 4982221901524618075910791)
              ·
                refine ⟨7473332852286927113866187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982221901524618075910791 7473332852286927113866187)
                ·
                  refine ⟨11209999278430390670799281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7473332852286927113866187 11209999278430390670799281)
                  ·
                    refine ⟨8407499458822793003099461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11209999278430390670799281 8407499458822793003099461)
                    ·
                      refine ⟨1576406148529273688081149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8407499458822793003099461 1576406148529273688081149)
                      ·
                        rfl

theorem cell23_3070040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_3070040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070040 prefixEnd_3070040 := by exact prefixLift 3070040
  have htrace : WordTrace (prefixWord ++ tailWord_3070040) baseStart_3070040 baseEnd_3070040 := by
    simpa [prefixWord, tailWord_3070040, baseEnd_3070040] using wordTrace_append hprefix tailTrace_3070040
  have hstable : (prefixWord ++ tailWord_3070040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070040).length < 2 ^ (prefixWord ++ tailWord_3070040).sum := by decide
  have hdescent : baseEnd_3070040 < baseStart_3070040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070044 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_3070044 : Nat := 118140960795 + 3070044 * 2 ^ 59
def prefixEnd_3070044 : Nat := 4983230072969 + 3 ^ 40 * 3070044 * 2
def baseEnd_3070044 : Nat := 1576408202451891672431131

theorem tailTrace_3070044 : CollatzResearch.WordTrace tailWord_3070044 prefixEnd_3070044 1576408202451891672431131 := by
  unfold tailWord_3070044
  simp only [CollatzResearch.WordTrace]
  refine ⟨55986851844881192308460593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74649135793174923077947457 55986851844881192308460593)
  ·
    refine ⟨41990138883660894231345445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55986851844881192308460593 41990138883660894231345445)
    ·
      refine ⟨7873151040686417668377271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41990138883660894231345445 7873151040686417668377271)
      ·
        refine ⟨11809726561029626502565907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7873151040686417668377271 11809726561029626502565907)
        ·
          refine ⟨17714589841544439753848861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11809726561029626502565907 17714589841544439753848861)
          ·
            refine ⟨6642971190579164907693323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17714589841544439753848861 6642971190579164907693323)
            ·
              refine ⟨9964456785868747361539985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6642971190579164907693323 9964456785868747361539985)
              ·
                refine ⟨7473342589401560521154989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9964456785868747361539985 7473342589401560521154989)
                ·
                  refine ⟨2802503471025585195433121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7473342589401560521154989 2802503471025585195433121)
                  ·
                    refine ⟨2101877603269188896574841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2802503471025585195433121 2101877603269188896574841)
                    ·
                      refine ⟨1576408202451891672431131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101877603269188896574841 1576408202451891672431131)
                      ·
                        rfl

theorem cell23_3070044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_3070044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070044 prefixEnd_3070044 := by exact prefixLift 3070044
  have htrace : WordTrace (prefixWord ++ tailWord_3070044) baseStart_3070044 baseEnd_3070044 := by
    simpa [prefixWord, tailWord_3070044, baseEnd_3070044] using wordTrace_append hprefix tailTrace_3070044
  have hstable : (prefixWord ++ tailWord_3070044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070044).length < 2 ^ (prefixWord ++ tailWord_3070044).sum := by decide
  have hdescent : baseEnd_3070044 < baseStart_3070044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070060 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 3]
def baseStart_3070060 : Nat := 118140960795 + 3070060 * 2 ^ 59
def prefixEnd_3070060 : Nat := 4983230072969 + 3 ^ 40 * 3070060 * 2
def baseEnd_3070060 : Nat := 1576416418142363609831057

theorem tailTrace_3070060 : CollatzResearch.WordTrace tailWord_3070060 prefixEnd_3070060 1576416418142363609831057 := by
  unfold tailWord_3070060
  simp only [CollatzResearch.WordTrace]
  refine ⟨55987143628852209674751817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74649524838469612899669089 55987143628852209674751817)
  ·
    refine ⟨41990357721639157256063863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55987143628852209674751817 41990357721639157256063863)
    ·
      refine ⟨62985536582458735884095795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41990357721639157256063863 62985536582458735884095795)
      ·
        refine ⟨94478304873688103826143693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62985536582458735884095795 94478304873688103826143693)
        ·
          refine ⟨35429364327633038934803885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94478304873688103826143693 35429364327633038934803885)
          ·
            refine ⟨13286011622862389600551457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35429364327633038934803885 13286011622862389600551457)
            ·
              refine ⟨9964508717146792200413593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13286011622862389600551457 9964508717146792200413593)
              ·
                refine ⟨7473381537860094150310195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9964508717146792200413593 7473381537860094150310195)
                ·
                  refine ⟨11210072306790141225465293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7473381537860094150310195 11210072306790141225465293)
                  ·
                    refine ⟨4203777115046302959549485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11210072306790141225465293 4203777115046302959549485)
                    ·
                      refine ⟨1576416418142363609831057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4203777115046302959549485 1576416418142363609831057)
                      ·
                        rfl

theorem cell23_3070060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_3070060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070060 prefixEnd_3070060 := by exact prefixLift 3070060
  have htrace : WordTrace (prefixWord ++ tailWord_3070060) baseStart_3070060 baseEnd_3070060 := by
    simpa [prefixWord, tailWord_3070060, baseEnd_3070060] using wordTrace_append hprefix tailTrace_3070060
  have hstable : (prefixWord ++ tailWord_3070060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070060).length < 2 ^ (prefixWord ++ tailWord_3070060).sum := by decide
  have hdescent : baseEnd_3070060 < baseStart_3070060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070061 : List Nat := [1, 5, 1, 1, 2, 1, 4, 3, 1, 2, 2]
def baseStart_3070061 : Nat := 118140960795 + 3070061 * 2 ^ 59
def prefixEnd_3070061 : Nat := 4983230072969 + 3 ^ 40 * 3070061 * 2
def baseEnd_3070061 : Nat := 1576416931623018105918553

theorem tailTrace_3070061 : CollatzResearch.WordTrace tailWord_3070061 prefixEnd_3070061 1576416931623018105918553 := by
  unfold tailWord_3070061
  simp only [CollatzResearch.WordTrace]
  refine ⟨111974323730700796520290037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74649549153800531013526691 111974323730700796520290037)
  ·
    refine ⟨10497592849753199673777191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111974323730700796520290037 10497592849753199673777191)
    ·
      refine ⟨15746389274629799510665787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10497592849753199673777191 15746389274629799510665787)
      ·
        refine ⟨23619583911944699265998681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15746389274629799510665787 23619583911944699265998681)
        ·
          refine ⟨17714687933958524449499011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23619583911944699265998681 17714687933958524449499011)
          ·
            refine ⟨26572031900937786674248517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17714687933958524449499011 26572031900937786674248517)
            ·
              refine ⟨4982255981425835001421597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26572031900937786674248517 4982255981425835001421597)
              ·
                refine ⟨1868345993034688125533099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4982255981425835001421597 1868345993034688125533099)
                ·
                  refine ⟨2802518989552032188299649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868345993034688125533099 2802518989552032188299649)
                  ·
                    refine ⟨2101889242164024141224737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2802518989552032188299649 2101889242164024141224737)
                    ·
                      refine ⟨1576416931623018105918553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101889242164024141224737 1576416931623018105918553)
                      ·
                        rfl

theorem cell23_3070061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_3070061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070061 prefixEnd_3070061 := by exact prefixLift 3070061
  have htrace : WordTrace (prefixWord ++ tailWord_3070061) baseStart_3070061 baseEnd_3070061 := by
    simpa [prefixWord, tailWord_3070061, baseEnd_3070061] using wordTrace_append hprefix tailTrace_3070061
  have hstable : (prefixWord ++ tailWord_3070061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070061).length < 2 ^ (prefixWord ++ tailWord_3070061).sum := by decide
  have hdescent : baseEnd_3070061 < baseStart_3070061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070064 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 1, 2, 3]
def baseStart_3070064 : Nat := 118140960795 + 3070064 * 2 ^ 59
def prefixEnd_3070064 : Nat := 4983230072969 + 3 ^ 40 * 3070064 * 2
def baseEnd_3070064 : Nat := 1576418472064981594181039

theorem tailTrace_3070064 : CollatzResearch.WordTrace tailWord_3070064 prefixEnd_3070064 1576418472064981594181039 := by
  unfold tailWord_3070064
  simp only [CollatzResearch.WordTrace]
  refine ⟨55987216574844964016324623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74649622099793285355099497 55987216574844964016324623)
  ·
    refine ⟨83980824862267446024486935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55987216574844964016324623 83980824862267446024486935)
    ·
      refine ⟨125971237293401169036730403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83980824862267446024486935 125971237293401169036730403)
      ·
        refine ⟨188956855940101753555095605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125971237293401169036730403 188956855940101753555095605)
        ·
          refine ⟨17714705244384539395790213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188956855940101753555095605 17714705244384539395790213)
          ·
            refine ⟨3321507233322101136710665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17714705244384539395790213 3321507233322101136710665)
            ·
              refine ⟨2491130424991575852532999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3321507233322101136710665 2491130424991575852532999)
              ·
                refine ⟨3736695637487363778799499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491130424991575852532999 3736695637487363778799499)
                ·
                  refine ⟨5605043456231045668199249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736695637487363778799499 5605043456231045668199249)
                  ·
                    refine ⟨4203782592173284251149437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5605043456231045668199249 4203782592173284251149437)
                    ·
                      refine ⟨1576418472064981594181039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4203782592173284251149437 1576418472064981594181039)
                      ·
                        rfl

theorem cell23_3070064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 2, 3].length) (baseStart_3070064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070064 prefixEnd_3070064 := by exact prefixLift 3070064
  have htrace : WordTrace (prefixWord ++ tailWord_3070064) baseStart_3070064 baseEnd_3070064 := by
    simpa [prefixWord, tailWord_3070064, baseEnd_3070064] using wordTrace_append hprefix tailTrace_3070064
  have hstable : (prefixWord ++ tailWord_3070064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070064).length < 2 ^ (prefixWord ++ tailWord_3070064).sum := by decide
  have hdescent : baseEnd_3070064 < baseStart_3070064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070077 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_3070077 : Nat := 118140960795 + 3070077 * 2 ^ 59
def prefixEnd_3070077 : Nat := 4983230072969 + 3 ^ 40 * 3070077 * 2
def baseEnd_3070077 : Nat := 1576425147313490043318479

theorem tailTrace_3070077 : CollatzResearch.WordTrace tailWord_3070077 prefixEnd_3070077 1576425147313490043318479 := by
  unfold tailWord_3070077
  simp only [CollatzResearch.WordTrace]
  refine ⟨111974907298642831252872485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74649938199095220835248323 111974907298642831252872485)
  ·
    refine ⟨20995295118495530859913591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111974907298642831252872485 20995295118495530859913591)
    ·
      refine ⟨31492942677743296289870387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20995295118495530859913591 31492942677743296289870387)
      ·
        refine ⟨47239414016614944434805581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31492942677743296289870387 47239414016614944434805581)
        ·
          refine ⟨17714780256230604163052093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47239414016614944434805581 17714780256230604163052093)
          ·
            refine ⟨6643042596086476561144535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17714780256230604163052093 6643042596086476561144535)
            ·
              refine ⟨9964563894129714841716803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643042596086476561144535 9964563894129714841716803)
              ·
                refine ⟨14946845841194572262575205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9964563894129714841716803 14946845841194572262575205)
                ·
                  refine ⟨2802533595223982299232851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14946845841194572262575205 2802533595223982299232851)
                  ·
                    refine ⟨4203800392835973448849277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2802533595223982299232851 4203800392835973448849277)
                    ·
                      refine ⟨1576425147313490043318479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4203800392835973448849277 1576425147313490043318479)
                      ·
                        rfl

theorem cell23_3070077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_3070077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070077 prefixEnd_3070077 := by exact prefixLift 3070077
  have htrace : WordTrace (prefixWord ++ tailWord_3070077) baseStart_3070077 baseEnd_3070077 := by
    simpa [prefixWord, tailWord_3070077, baseEnd_3070077] using wordTrace_append hprefix tailTrace_3070077
  have hstable : (prefixWord ++ tailWord_3070077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070077).length < 2 ^ (prefixWord ++ tailWord_3070077).sum := by decide
  have hdescent : baseEnd_3070077 < baseStart_3070077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070094 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_3070094 : Nat := 118140960795 + 3070094 * 2 ^ 59
def prefixEnd_3070094 : Nat := 4983230072969 + 3 ^ 40 * 3070094 * 2
def baseEnd_3070094 : Nat := 1576433876484616476805901

theorem tailTrace_3070094 : CollatzResearch.WordTrace tailWord_3070094 prefixEnd_3070094 1576433876484616476805901 := by
  unfold tailWord_3070094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13996940917447655394530167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74650351559720828770827557 13996940917447655394530167)
  ·
    refine ⟨20995411376171483091795251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13996940917447655394530167 20995411376171483091795251)
    ·
      refine ⟨31493117064257224637692877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20995411376171483091795251 31493117064257224637692877)
      ·
        refine ⟨11809918899096459239134829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31493117064257224637692877 11809918899096459239134829)
        ·
          refine ⟨4428719587161172214675561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11809918899096459239134829 4428719587161172214675561)
          ·
            refine ⟨3321539690370879161006671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4428719587161172214675561 3321539690370879161006671)
            ·
              refine ⟨4982309535556318741510007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321539690370879161006671 4982309535556318741510007)
              ·
                refine ⟨7473464303334478112265011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982309535556318741510007 7473464303334478112265011)
                ·
                  refine ⟨11210196455001717168397517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7473464303334478112265011 11210196455001717168397517)
                  ·
                    refine ⟨4203823670625643938149069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11210196455001717168397517 4203823670625643938149069)
                    ·
                      refine ⟨1576433876484616476805901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4203823670625643938149069 1576433876484616476805901)
                      ·
                        rfl

theorem cell23_3070094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_3070094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070094 prefixEnd_3070094 := by exact prefixLift 3070094
  have htrace : WordTrace (prefixWord ++ tailWord_3070094) baseStart_3070094 baseEnd_3070094 := by
    simpa [prefixWord, tailWord_3070094, baseEnd_3070094] using wordTrace_append hprefix tailTrace_3070094
  have hstable : (prefixWord ++ tailWord_3070094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070094).length < 2 ^ (prefixWord ++ tailWord_3070094).sum := by decide
  have hdescent : baseEnd_3070094 < baseStart_3070094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070117 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 6, 2, 2]
def baseStart_3070117 : Nat := 118140960795 + 3070117 * 2 ^ 59
def prefixEnd_3070117 : Nat := 4983230072969 + 3 ^ 40 * 3070117 * 2
def baseEnd_3070117 : Nat := 1576445686539669886818295

theorem tailTrace_3070117 : CollatzResearch.WordTrace tailWord_3070117 prefixEnd_3070117 1576445686539669886818295 := by
  unfold tailWord_3070117
  simp only [CollatzResearch.WordTrace]
  refine ⟨111976366218497918084328605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74650910812331945389552403 111976366218497918084328605)
  ·
    refine ⟨41991137331936719281623227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111976366218497918084328605 41991137331936719281623227)
    ·
      refine ⟨62986705997905078922434841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41991137331936719281623227 62986705997905078922434841)
      ·
        refine ⟨47240029498428809191826131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62986705997905078922434841 47240029498428809191826131)
        ·
          refine ⟨70860044247643213787739197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47240029498428809191826131 70860044247643213787739197)
          ·
            refine ⟨26572516592866205170402199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70860044247643213787739197 26572516592866205170402199)
            ·
              refine ⟨39858774889299307755603299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26572516592866205170402199 39858774889299307755603299)
              ·
                refine ⟨59788162333948961633404949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39858774889299307755603299 59788162333948961633404949)
                ·
                  refine ⟨2802570109403857576565857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59788162333948961633404949 2802570109403857576565857)
                  ·
                    refine ⟨2101927582052893182424393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2802570109403857576565857 2101927582052893182424393)
                    ·
                      refine ⟨1576445686539669886818295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101927582052893182424393 1576445686539669886818295)
                      ·
                        rfl

theorem cell23_3070117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_3070117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070117 prefixEnd_3070117 := by exact prefixLift 3070117
  have htrace : WordTrace (prefixWord ++ tailWord_3070117) baseStart_3070117 baseEnd_3070117 := by
    simpa [prefixWord, tailWord_3070117, baseEnd_3070117] using wordTrace_append hprefix tailTrace_3070117
  have hstable : (prefixWord ++ tailWord_3070117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070117).length < 2 ^ (prefixWord ++ tailWord_3070117).sum := by decide
  have hdescent : baseEnd_3070117 < baseStart_3070117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070145 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_3070145 : Nat := 118140960795 + 3070145 * 2 ^ 59
def prefixEnd_3070145 : Nat := 4983230072969 + 3 ^ 40 * 3070145 * 2
def baseEnd_3070145 : Nat := 1576460063997995777268167

theorem tailTrace_3070145 : CollatzResearch.WordTrace tailWord_3070145 prefixEnd_3070145 1576460063997995777268167 := by
  unfold tailWord_3070145
  simp only [CollatzResearch.WordTrace]
  refine ⟨111977387462396478866347889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74651591641597652577565259 111977387462396478866347889)
  ·
    refine ⟨83983040596797359149760917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111977387462396478866347889 83983040596797359149760917)
    ·
      refine ⟨3936705027974876210145043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83983040596797359149760917 3936705027974876210145043)
      ·
        refine ⟨5905057541962314315217565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3936705027974876210145043 5905057541962314315217565)
        ·
          refine ⟨2214396578235867868206587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5905057541962314315217565 2214396578235867868206587)
          ·
            refine ⟨3321594867353801802309881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214396578235867868206587 3321594867353801802309881)
            ·
              refine ⟨2491196150515351351732411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3321594867353801802309881 2491196150515351351732411)
              ·
                refine ⟨3736794225773027027598617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491196150515351351732411 3736794225773027027598617)
                ·
                  refine ⟨2802595669329770270698963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3736794225773027027598617 2802595669329770270698963)
                  ·
                    refine ⟨4203893503994655406048445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2802595669329770270698963 4203893503994655406048445)
                    ·
                      refine ⟨1576460063997995777268167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4203893503994655406048445 1576460063997995777268167)
                      ·
                        rfl

theorem cell23_3070145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_3070145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070145 prefixEnd_3070145 := by exact prefixLift 3070145
  have htrace : WordTrace (prefixWord ++ tailWord_3070145) baseStart_3070145 baseEnd_3070145 := by
    simpa [prefixWord, tailWord_3070145, baseEnd_3070145] using wordTrace_append hprefix tailTrace_3070145
  have hstable : (prefixWord ++ tailWord_3070145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070145).length < 2 ^ (prefixWord ++ tailWord_3070145).sum := by decide
  have hdescent : baseEnd_3070145 < baseStart_3070145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070153 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 1, 7]
def baseStart_3070153 : Nat := 118140960795 + 3070153 * 2 ^ 59
def prefixEnd_3070153 : Nat := 4983230072969 + 3 ^ 40 * 3070153 * 2
def baseEnd_3070153 : Nat := 525488057281077248656043

theorem tailTrace_3070153 : CollatzResearch.WordTrace tailWord_3070153 prefixEnd_3070153 525488057281077248656043 := by
  unfold tailWord_3070153
  simp only [CollatzResearch.WordTrace]
  refine ⟨111977679246367496232639113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74651786164244997488426075 111977679246367496232639113)
  ·
    refine ⟨83983259434775622174479335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111977679246367496232639113 83983259434775622174479335)
    ·
      refine ⟨125974889152163433261719003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83983259434775622174479335 125974889152163433261719003)
      ·
        refine ⟨188962333728245149892578505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125974889152163433261719003 188962333728245149892578505)
        ·
          refine ⟨141721750296183862419433879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188962333728245149892578505 141721750296183862419433879)
          ·
            refine ⟨212582625444275793629150819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141721750296183862419433879 212582625444275793629150819)
            ·
              refine ⟨318873938166413690443726229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212582625444275793629150819 318873938166413690443726229)
              ·
                refine ⟨14947215851550641739549667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 318873938166413690443726229 14947215851550641739549667)
                ·
                  refine ⟨22420823777325962609324501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14947215851550641739549667 22420823777325962609324501)
                  ·
                    refine ⟨525488057281077248656043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22420823777325962609324501 525488057281077248656043)
                    ·
                      rfl

theorem cell23_3070153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_3070153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070153 prefixEnd_3070153 := by exact prefixLift 3070153
  have htrace : WordTrace (prefixWord ++ tailWord_3070153) baseStart_3070153 baseEnd_3070153 := by
    simpa [prefixWord, tailWord_3070153, baseEnd_3070153] using wordTrace_append hprefix tailTrace_3070153
  have hstable : (prefixWord ++ tailWord_3070153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070153).length < 2 ^ (prefixWord ++ tailWord_3070153).sum := by decide
  have hdescent : baseEnd_3070153 < baseStart_3070153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070163 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 5]
def baseStart_3070163 : Nat := 118140960795 + 3070163 * 2 ^ 59
def prefixEnd_3070163 : Nat := 4983230072969 + 3 ^ 40 * 3070163 * 2
def baseEnd_3070163 : Nat := 1576469306649776706843083

theorem tailTrace_3070163 : CollatzResearch.WordTrace tailWord_3070163 prefixEnd_3070163 1576469306649776706843083 := by
  unfold tailWord_3070163
  simp only [CollatzResearch.WordTrace]
  refine ⟨111978043976331267940503143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74652029317554178627002095 111978043976331267940503143)
  ·
    refine ⟨167967065964496901910754715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111978043976331267940503143 167967065964496901910754715)
    ·
      refine ⟨251950598946745352866132073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167967065964496901910754715 251950598946745352866132073)
      ·
        refine ⟨188962949210059014649599055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 251950598946745352866132073 188962949210059014649599055)
        ·
          refine ⟨283444423815088521974398583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188962949210059014649599055 283444423815088521974398583)
          ·
            refine ⟨425166635722632782961597875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283444423815088521974398583 425166635722632782961597875)
            ·
              refine ⟨637749953583949174442396813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425166635722632782961597875 637749953583949174442396813)
              ·
                refine ⟨239156232593980940415898805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 637749953583949174442396813 239156232593980940415898805)
                ·
                  refine ⟨22420896805685713163990513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239156232593980940415898805 22420896805685713163990513)
                  ·
                    refine ⟨16815672604264284872992885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22420896805685713163990513 16815672604264284872992885)
                    ·
                      refine ⟨1576469306649776706843083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16815672604264284872992885 1576469306649776706843083)
                      ·
                        rfl

theorem cell23_3070163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_3070163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070163 prefixEnd_3070163 := by exact prefixLift 3070163
  have htrace : WordTrace (prefixWord ++ tailWord_3070163) baseStart_3070163 baseEnd_3070163 := by
    simpa [prefixWord, tailWord_3070163, baseEnd_3070163] using wordTrace_append hprefix tailTrace_3070163
  have hstable : (prefixWord ++ tailWord_3070163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070163).length < 2 ^ (prefixWord ++ tailWord_3070163).sum := by decide
  have hdescent : baseEnd_3070163 < baseStart_3070163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070170 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_3070170 : Nat := 118140960795 + 3070170 * 2 ^ 59
def prefixEnd_3070170 : Nat := 4983230072969 + 3 ^ 40 * 3070170 * 2
def baseEnd_3070170 : Nat := 525490967004786059818517

theorem tailTrace_3070170 : CollatzResearch.WordTrace tailWord_3070170 prefixEnd_3070170 525490967004786059818517 := by
  unfold tailWord_3070170
  simp only [CollatzResearch.WordTrace]
  refine ⟨27994574821826477034001991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74652199524870605424005309 27994574821826477034001991)
  ·
    refine ⟨41991862232739715551002987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27994574821826477034001991 41991862232739715551002987)
    ·
      refine ⟨62987793349109573326504481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41991862232739715551002987 62987793349109573326504481)
      ·
        refine ⟨47240845011832179994878361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62987793349109573326504481 47240845011832179994878361)
        ·
          refine ⟨35430633758874134996158771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47240845011832179994878361 35430633758874134996158771)
          ·
            refine ⟨53145950638311202494238157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35430633758874134996158771 53145950638311202494238157)
            ·
              refine ⟨19929731489366700935339309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53145950638311202494238157 19929731489366700935339309)
              ·
                refine ⟨7473649308512512850752241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19929731489366700935339309 7473649308512512850752241)
                ·
                  refine ⟨5605236981384384638064181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7473649308512512850752241 5605236981384384638064181)
                  ·
                    refine ⟨525490967004786059818517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5605236981384384638064181 525490967004786059818517)
                    ·
                      rfl

theorem cell23_3070170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_3070170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070170 prefixEnd_3070170 := by exact prefixLift 3070170
  have htrace : WordTrace (prefixWord ++ tailWord_3070170) baseStart_3070170 baseEnd_3070170 := by
    simpa [prefixWord, tailWord_3070170, baseEnd_3070170] using wordTrace_append hprefix tailTrace_3070170
  have hstable : (prefixWord ++ tailWord_3070170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070170).length < 2 ^ (prefixWord ++ tailWord_3070170).sum := by decide
  have hdescent : baseEnd_3070170 < baseStart_3070170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070190 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_3070190 : Nat := 118140960795 + 3070190 * 2 ^ 59
def prefixEnd_3070190 : Nat := 4983230072969 + 3 ^ 40 * 3070190 * 2
def baseEnd_3070190 : Nat := 1576483170627448101205459

theorem tailTrace_3070190 : CollatzResearch.WordTrace tailWord_3070190 prefixEnd_3070190 1576483170627448101205459 := by
  unfold tailWord_3070190
  simp only [CollatzResearch.WordTrace]
  refine ⟨13997378593404181443967003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74652685831488967701157349 13997378593404181443967003)
  ·
    refine ⟨20996067890106272165950505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13997378593404181443967003 20996067890106272165950505)
    ·
      refine ⟨15747050917579704124462879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20996067890106272165950505 15747050917579704124462879)
      ·
        refine ⟨23620576376369556186694319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15747050917579704124462879 23620576376369556186694319)
        ·
          refine ⟨35430864564554334280041479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23620576376369556186694319 35430864564554334280041479)
          ·
            refine ⟨53146296846831501420062219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35430864564554334280041479 53146296846831501420062219)
            ·
              refine ⟨79719445270247252130093329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53146296846831501420062219 79719445270247252130093329)
              ·
                refine ⟨59789583952685439097569997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79719445270247252130093329 59789583952685439097569997)
                ·
                  refine ⟨22421093982257039661588749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59789583952685439097569997 22421093982257039661588749)
                  ·
                    refine ⟨8407910243346389873095781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22421093982257039661588749 8407910243346389873095781)
                    ·
                      refine ⟨1576483170627448101205459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8407910243346389873095781 1576483170627448101205459)
                      ·
                        rfl

theorem cell23_3070190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_3070190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070190 prefixEnd_3070190 := by exact prefixLift 3070190
  have htrace : WordTrace (prefixWord ++ tailWord_3070190) baseStart_3070190 baseEnd_3070190 := by
    simpa [prefixWord, tailWord_3070190, baseEnd_3070190] using wordTrace_append hprefix tailTrace_3070190
  have hstable : (prefixWord ++ tailWord_3070190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070190).length < 2 ^ (prefixWord ++ tailWord_3070190).sum := by decide
  have hdescent : baseEnd_3070190 < baseStart_3070190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070200 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 7, 4]
def baseStart_3070200 : Nat := 118140960795 + 3070200 * 2 ^ 59
def prefixEnd_3070200 : Nat := 4983230072969 + 3 ^ 40 * 3070200 * 2
def baseEnd_3070200 : Nat := 525496101811331020693471

theorem tailTrace_3070200 : CollatzResearch.WordTrace tailWord_3070200 prefixEnd_3070200 525496101811331020693471 := by
  unfold tailWord_3070200
  simp only [CollatzResearch.WordTrace]
  refine ⟨55989696738598611629800027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74652928984798148839733369 55989696738598611629800027)
  ·
    refine ⟨83984545107897917444700041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55989696738598611629800027 83984545107897917444700041)
    ·
      refine ⟨62988408830923438083525031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83984545107897917444700041 62988408830923438083525031)
      ·
        refine ⟨94482613246385157125287547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62988408830923438083525031 94482613246385157125287547)
        ·
          refine ⟨141723919869577735687931321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94482613246385157125287547 141723919869577735687931321)
          ·
            refine ⟨106292939902183301765948491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141723919869577735687931321 106292939902183301765948491)
            ·
              refine ⟨159439409853274952648922737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106292939902183301765948491 159439409853274952648922737)
              ·
                refine ⟨119579557389956214486692053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159439409853274952648922737 119579557389956214486692053)
                ·
                  refine ⟨2802645876327098777031845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119579557389956214486692053 2802645876327098777031845)
                  ·
                    refine ⟨525496101811331020693471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2802645876327098777031845 525496101811331020693471)
                    ·
                      rfl

theorem cell23_3070200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_3070200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070200 prefixEnd_3070200 := by exact prefixLift 3070200
  have htrace : WordTrace (prefixWord ++ tailWord_3070200) baseStart_3070200 baseEnd_3070200 := by
    simpa [prefixWord, tailWord_3070200, baseEnd_3070200] using wordTrace_append hprefix tailTrace_3070200
  have hstable : (prefixWord ++ tailWord_3070200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070200).length < 2 ^ (prefixWord ++ tailWord_3070200).sum := by decide
  have hdescent : baseEnd_3070200 < baseStart_3070200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070207 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 2, 4, 2]
def baseStart_3070207 : Nat := 118140960795 + 3070207 * 2 ^ 59
def prefixEnd_3070207 : Nat := 4983230072969 + 3 ^ 40 * 3070207 * 2
def baseEnd_3070207 : Nat := 1576491899798574534692881

theorem tailTrace_3070207 : CollatzResearch.WordTrace tailWord_3070207 prefixEnd_3070207 1576491899798574534692881 := by
  unfold tailWord_3070207
  simp only [CollatzResearch.WordTrace]
  refine ⟨111979648788171863455104875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74653099192114575636736583 111979648788171863455104875)
  ·
    refine ⟨167969473182257795182657313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111979648788171863455104875 167969473182257795182657313)
    ·
      refine ⟨125977104886693346386992985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167969473182257795182657313 125977104886693346386992985)
      ·
        refine ⟨94482828665020009790244739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125977104886693346386992985 94482828665020009790244739)
        ·
          refine ⟨141724242997530014685367109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94482828665020009790244739 141724242997530014685367109)
          ·
            refine ⟨26573295562036877753506333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141724242997530014685367109 26573295562036877753506333)
            ·
              refine ⟨9964985835763829157564875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26573295562036877753506333 9964985835763829157564875)
              ·
                refine ⟨14947478753645743736347313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9964985835763829157564875 14947478753645743736347313)
                ·
                  refine ⟨11210609065234307802260485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14947478753645743736347313 11210609065234307802260485)
                  ·
                    refine ⟨2101989199731432712923841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11210609065234307802260485 2101989199731432712923841)
                    ·
                      refine ⟨1576491899798574534692881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2101989199731432712923841 1576491899798574534692881)
                      ·
                        rfl

theorem cell23_3070207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 4, 2].length) (baseStart_3070207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070207 prefixEnd_3070207 := by exact prefixLift 3070207
  have htrace : WordTrace (prefixWord ++ tailWord_3070207) baseStart_3070207 baseEnd_3070207 := by
    simpa [prefixWord, tailWord_3070207, baseEnd_3070207] using wordTrace_append hprefix tailTrace_3070207
  have hstable : (prefixWord ++ tailWord_3070207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070207).length < 2 ^ (prefixWord ++ tailWord_3070207).sum := by decide
  have hdescent : baseEnd_3070207 < baseStart_3070207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070217 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 3, 4]
def baseStart_3070217 : Nat := 118140960795 + 3070217 * 2 ^ 59
def prefixEnd_3070217 : Nat := 4983230072969 + 3 ^ 40 * 3070217 * 2
def baseEnd_3070217 : Nat := 525499011535039831855945

theorem tailTrace_3070217 : CollatzResearch.WordTrace tailWord_3070217 prefixEnd_3070217 525499011535039831855945 := by
  unfold tailWord_3070217
  simp only [CollatzResearch.WordTrace]
  refine ⟨111980013518135635162968905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74653342345423756775312603 111980013518135635162968905)
  ·
    refine ⟨83985010138601726372226679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111980013518135635162968905 83985010138601726372226679)
    ·
      refine ⟨125977515207902589558340019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83985010138601726372226679 125977515207902589558340019)
      ·
        refine ⟨188966272811853884337510029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125977515207902589558340019 188966272811853884337510029)
        ·
          refine ⟨70862352304445206626566261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188966272811853884337510029 70862352304445206626566261)
          ·
            refine ⟨6643345528541738121240587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70862352304445206626566261 6643345528541738121240587)
            ·
              refine ⟨9965018292812607181860881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643345528541738121240587 9965018292812607181860881)
              ·
                refine ⟨7473763719609455386395661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9965018292812607181860881 7473763719609455386395661)
                ·
                  refine ⟨2802661394853545769898373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7473763719609455386395661 2802661394853545769898373)
                  ·
                    refine ⟨525499011535039831855945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2802661394853545769898373 525499011535039831855945)
                    ·
                      rfl

theorem cell23_3070217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 3, 4].length) (baseStart_3070217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070217 prefixEnd_3070217 := by exact prefixLift 3070217
  have htrace : WordTrace (prefixWord ++ tailWord_3070217) baseStart_3070217 baseEnd_3070217 := by
    simpa [prefixWord, tailWord_3070217, baseEnd_3070217] using wordTrace_append hprefix tailTrace_3070217
  have hstable : (prefixWord ++ tailWord_3070217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070217).length < 2 ^ (prefixWord ++ tailWord_3070217).sum := by decide
  have hdescent : baseEnd_3070217 < baseStart_3070217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070284 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 2, 3, 2]
def baseStart_3070284 : Nat := 118140960795 + 3070284 * 2 ^ 59
def prefixEnd_3070284 : Nat := 4983230072969 + 3 ^ 40 * 3070284 * 2
def baseEnd_3070284 : Nat := 1576531437808970733430027

theorem tailTrace_3070284 : CollatzResearch.WordTrace tailWord_3070284 prefixEnd_3070284 1576531437808970733430027 := by
  unfold tailWord_3070284
  simp only [CollatzResearch.WordTrace]
  refine ⟨55991228604446452802828953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74654971472595270403771937 55991228604446452802828953)
  ·
    refine ⟨41993421453334839602121715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55991228604446452802828953 41993421453334839602121715)
    ·
      refine ⟨62990132180002259403182573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41993421453334839602121715 62990132180002259403182573)
      ·
        refine ⟨23621299567500847276193465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62990132180002259403182573 23621299567500847276193465)
        ·
          refine ⟨17715974675625635457145099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23621299567500847276193465 17715974675625635457145099)
          ·
            refine ⟨26573962013438453185717649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17715974675625635457145099 26573962013438453185717649)
            ·
              refine ⟨19930471510078839889288237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26573962013438453185717649 19930471510078839889288237)
              ·
                refine ⟨7473926816279564958483089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19930471510078839889288237 7473926816279564958483089)
                ·
                  refine ⟨5605445112209673718862317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7473926816279564958483089 5605445112209673718862317)
                  ·
                    refine ⟨2102041917078627644573369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5605445112209673718862317 2102041917078627644573369)
                    ·
                      refine ⟨1576531437808970733430027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2102041917078627644573369 1576531437808970733430027)
                      ·
                        rfl

theorem cell23_3070284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_3070284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070284 prefixEnd_3070284 := by exact prefixLift 3070284
  have htrace : WordTrace (prefixWord ++ tailWord_3070284) baseStart_3070284 baseEnd_3070284 := by
    simpa [prefixWord, tailWord_3070284, baseEnd_3070284] using wordTrace_append hprefix tailTrace_3070284
  have hstable : (prefixWord ++ tailWord_3070284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070284).length < 2 ^ (prefixWord ++ tailWord_3070284).sum := by decide
  have hdescent : baseEnd_3070284 < baseStart_3070284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070302 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3070302 : Nat := 118140960795 + 3070302 * 2 ^ 59
def prefixEnd_3070302 : Nat := 4983230072969 + 3 ^ 40 * 3070302 * 2
def baseEnd_3070302 : Nat := 525513560153583887668315

theorem tailTrace_3070302 : CollatzResearch.WordTrace tailWord_3070302 prefixEnd_3070302 525513560153583887668315 := by
  unfold tailWord_3070302
  simp only [CollatzResearch.WordTrace]
  refine ⟨13997889215353461834976645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74655409148551796453208773 13997889215353461834976645)
  ·
    refine ⟨2624604227878774094058121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13997889215353461834976645 2624604227878774094058121)
    ·
      refine ⟨1968453170909080570543591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2624604227878774094058121 1968453170909080570543591)
      ·
        refine ⟨2952679756363620855815387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968453170909080570543591 2952679756363620855815387)
        ·
          refine ⟨4429019634545431283723081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952679756363620855815387 4429019634545431283723081)
          ·
            refine ⟨3321764725909073462792311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4429019634545431283723081 3321764725909073462792311)
            ·
              refine ⟨4982647088863610194188467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321764725909073462792311 4982647088863610194188467)
              ·
                refine ⟨7473970633295415291282701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982647088863610194188467 7473970633295415291282701)
                ·
                  refine ⟨2802738987485780734231013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7473970633295415291282701 2802738987485780734231013)
                  ·
                    refine ⟨525513560153583887668315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2802738987485780734231013 525513560153583887668315)
                    ·
                      rfl

theorem cell23_3070302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3070302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070302 prefixEnd_3070302 := by exact prefixLift 3070302
  have htrace : WordTrace (prefixWord ++ tailWord_3070302) baseStart_3070302 baseEnd_3070302 := by
    simpa [prefixWord, tailWord_3070302, baseEnd_3070302] using wordTrace_append hprefix tailTrace_3070302
  have hstable : (prefixWord ++ tailWord_3070302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070302).length < 2 ^ (prefixWord ++ tailWord_3070302).sum := by decide
  have hdescent : baseEnd_3070302 < baseStart_3070302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070307 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 4, 4]
def baseStart_3070307 : Nat := 118140960795 + 3070307 * 2 ^ 59
def prefixEnd_3070307 : Nat := 4983230072969 + 3 ^ 40 * 3070307 * 2
def baseEnd_3070307 : Nat := 525514415954674714480807

theorem tailTrace_3070307 : CollatzResearch.WordTrace tailWord_3070307 prefixEnd_3070307 525514415954674714480807 := by
  unfold tailWord_3070307
  simp only [CollatzResearch.WordTrace]
  refine ⟨111983296087809580533745175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74655530725206387022496783 111983296087809580533745175)
  ·
    refine ⟨167974944131714370800617763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111983296087809580533745175 167974944131714370800617763)
    ·
      refine ⟨251962416197571556200926645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167974944131714370800617763 251962416197571556200926645)
      ·
        refine ⟨23621476518522333393836873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 251962416197571556200926645 23621476518522333393836873)
        ·
          refine ⟨17716107388891750045377655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23621476518522333393836873 17716107388891750045377655)
          ·
            refine ⟨26574161083337625068066483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17716107388891750045377655 26574161083337625068066483)
            ·
              refine ⟨39861241625006437602099725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26574161083337625068066483 39861241625006437602099725)
              ·
                refine ⟨14947965609377414100787397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39861241625006437602099725 14947965609377414100787397)
                ·
                  refine ⟨2802743551758265143897637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14947965609377414100787397 2802743551758265143897637)
                  ·
                    refine ⟨525514415954674714480807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2802743551758265143897637 525514415954674714480807)
                    ·
                      rfl

theorem cell23_3070307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 4, 4].length) (baseStart_3070307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070307 prefixEnd_3070307 := by exact prefixLift 3070307
  have htrace : WordTrace (prefixWord ++ tailWord_3070307) baseStart_3070307 baseEnd_3070307 := by
    simpa [prefixWord, tailWord_3070307, baseEnd_3070307] using wordTrace_append hprefix tailTrace_3070307
  have hstable : (prefixWord ++ tailWord_3070307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070307).length < 2 ^ (prefixWord ++ tailWord_3070307).sum := by decide
  have hdescent : baseEnd_3070307 < baseStart_3070307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070308 : List Nat := [2, 3, 1, 1, 3, 1, 5, 2, 1, 1, 3]
def baseStart_3070308 : Nat := 118140960795 + 3070308 * 2 ^ 59
def prefixEnd_3070308 : Nat := 4983230072969 + 3 ^ 40 * 3070308 * 2
def baseEnd_3070308 : Nat := 1576543761344678639529917

theorem tailTrace_3070308 : CollatzResearch.WordTrace tailWord_3070308 prefixEnd_3070308 1576543761344678639529917 := by
  unfold tailWord_3070308
  simp only [CollatzResearch.WordTrace]
  refine ⟨55991666280402978852265789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74655555040537305136354385 55991666280402978852265789)
  ·
    refine ⟨20996874855151117069599671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55991666280402978852265789 20996874855151117069599671)
    ·
      refine ⟨31495312282726675604399507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20996874855151117069599671 31495312282726675604399507)
      ·
        refine ⟨47242968424090013406599261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31495312282726675604399507 47242968424090013406599261)
        ·
          refine ⟨17716113159033755027474723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47242968424090013406599261 17716113159033755027474723)
          ·
            refine ⟨26574169738550632541212085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17716113159033755027474723 26574169738550632541212085)
            ·
              refine ⟨2491328412989121800738633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26574169738550632541212085 2491328412989121800738633)
              ·
                refine ⟨1868496309741841350553975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2491328412989121800738633 1868496309741841350553975)
                ·
                  refine ⟨2802744464612762025830963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868496309741841350553975 2802744464612762025830963)
                  ·
                    refine ⟨4204116696919143038746445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2802744464612762025830963 4204116696919143038746445)
                    ·
                      refine ⟨1576543761344678639529917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4204116696919143038746445 1576543761344678639529917)
                      ·
                        rfl

theorem cell23_3070308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_3070308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070308 prefixEnd_3070308 := by exact prefixLift 3070308
  have htrace : WordTrace (prefixWord ++ tailWord_3070308) baseStart_3070308 baseEnd_3070308 := by
    simpa [prefixWord, tailWord_3070308, baseEnd_3070308] using wordTrace_append hprefix tailTrace_3070308
  have hstable : (prefixWord ++ tailWord_3070308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070308).length < 2 ^ (prefixWord ++ tailWord_3070308).sum := by decide
  have hdescent : baseEnd_3070308 < baseStart_3070308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070317 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3070317 : Nat := 118140960795 + 3070317 * 2 ^ 59
def prefixEnd_3070317 : Nat := 4983230072969 + 3 ^ 40 * 3070317 * 2
def baseEnd_3070317 : Nat := 1576548382670569104317375

theorem tailTrace_3070317 : CollatzResearch.WordTrace tailWord_3070317 prefixEnd_3070317 1576548382670569104317375 := by
  unfold tailWord_3070317
  simp only [CollatzResearch.WordTrace]
  refine ⟨111983660817773352241609205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74655773878515568161072803 111983660817773352241609205)
  ·
    refine ⟨10498468201666251772650863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111983660817773352241609205 10498468201666251772650863)
    ·
      refine ⟨15747702302499377658976295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10498468201666251772650863 15747702302499377658976295)
      ·
        refine ⟨23621553453749066488464443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15747702302499377658976295 23621553453749066488464443)
        ·
          refine ⟨35432330180623599732696665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23621553453749066488464443 35432330180623599732696665)
          ·
            refine ⟨26574247635467699799522499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35432330180623599732696665 26574247635467699799522499)
            ·
              refine ⟨39861371453201549699283749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26574247635467699799522499 39861371453201549699283749)
              ·
                refine ⟨7474007147475290568615703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39861371453201549699283749 7474007147475290568615703)
                ·
                  refine ⟨11211010721212935852923555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7474007147475290568615703 11211010721212935852923555)
                  ·
                    refine ⟨16816516081819403779385333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11211010721212935852923555 16816516081819403779385333)
                    ·
                      refine ⟨1576548382670569104317375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16816516081819403779385333 1576548382670569104317375)
                      ·
                        rfl

theorem cell23_3070317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3070317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070317 prefixEnd_3070317 := by exact prefixLift 3070317
  have htrace : WordTrace (prefixWord ++ tailWord_3070317) baseStart_3070317 baseEnd_3070317 := by
    simpa [prefixWord, tailWord_3070317, baseEnd_3070317] using wordTrace_append hprefix tailTrace_3070317
  have hstable : (prefixWord ++ tailWord_3070317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070317).length < 2 ^ (prefixWord ++ tailWord_3070317).sum := by decide
  have hdescent : baseEnd_3070317 < baseStart_3070317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070320 : List Nat := [2, 1, 1, 1, 4, 3, 1, 10]
def baseStart_3070320 : Nat := 118140960795 + 3070320 * 2 ^ 59
def prefixEnd_3070320 : Nat := 4983230072969 + 3 ^ 40 * 3070320 * 2
def baseEnd_3070320 : Nat := 58390737893056762688143

theorem tailTrace_3070320 : CollatzResearch.WordTrace tailWord_3070320 prefixEnd_3070320 58390737893056762688143 := by
  unfold tailWord_3070320
  simp only [CollatzResearch.WordTrace]
  refine ⟨55991885118381241876984207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74655846824508322502645609 55991885118381241876984207)
  ·
    refine ⟨83987827677571862815476311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55991885118381241876984207 83987827677571862815476311)
    ·
      refine ⟨125981741516357794223214467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83987827677571862815476311 125981741516357794223214467)
      ·
        refine ⟨188972612274536691334821701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125981741516357794223214467 188972612274536691334821701)
        ·
          refine ⟨35432364801475629625279069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188972612274536691334821701 35432364801475629625279069)
          ·
            refine ⟨13287136800553361109479651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35432364801475629625279069 13287136800553361109479651)
            ·
              refine ⟨19930705200830041664219477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13287136800553361109479651 19930705200830041664219477)
              ·
                refine ⟨58390737893056762688143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19930705200830041664219477 58390737893056762688143)
                ·
                  rfl

theorem cell23_3070320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 10].length) (baseStart_3070320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070320 prefixEnd_3070320 := by exact prefixLift 3070320
  have htrace : WordTrace (prefixWord ++ tailWord_3070320) baseStart_3070320 baseEnd_3070320 := by
    simpa [prefixWord, tailWord_3070320, baseEnd_3070320] using wordTrace_append hprefix tailTrace_3070320
  have hstable : (prefixWord ++ tailWord_3070320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070320).length < 2 ^ (prefixWord ++ tailWord_3070320).sum := by decide
  have hdescent : baseEnd_3070320 < baseStart_3070320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070337 : List Nat := [1, 2, 4, 3, 1, 1, 2, 9]
def baseStart_3070337 : Nat := 118140960795 + 3070337 * 2 ^ 59
def prefixEnd_3070337 : Nat := 4983230072969 + 3 ^ 40 * 3070337 * 2
def baseEnd_3070337 : Nat := 58391061195691075039529

theorem tailTrace_3070337 : CollatzResearch.WordTrace tailWord_3070337 prefixEnd_3070337 58391061195691075039529 := by
  unfold tailWord_3070337
  simp only [CollatzResearch.WordTrace]
  refine ⟨111984390277700895657337265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74656260185133930438224843 111984390277700895657337265)
  ·
    refine ⟨83988292708275671743002949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111984390277700895657337265 83988292708275671743002949)
    ·
      refine ⟨15747804882801688451813053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83988292708275671743002949 15747804882801688451813053)
      ·
        refine ⟨5905426831050633169429895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15747804882801688451813053 5905426831050633169429895)
        ·
          refine ⟨8858140246575949754144843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5905426831050633169429895 8858140246575949754144843)
          ·
            refine ⟨13287210369863924631217265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8858140246575949754144843 13287210369863924631217265)
            ·
              refine ⟨9965407777397943473412949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13287210369863924631217265 9965407777397943473412949)
              ·
                refine ⟨58391061195691075039529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9965407777397943473412949 58391061195691075039529)
                ·
                  rfl

theorem cell23_3070337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 9].length) (baseStart_3070337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070337 prefixEnd_3070337 := by exact prefixLift 3070337
  have htrace : WordTrace (prefixWord ++ tailWord_3070337) baseStart_3070337 baseEnd_3070337 := by
    simpa [prefixWord, tailWord_3070337, baseEnd_3070337] using wordTrace_append hprefix tailTrace_3070337
  have hstable : (prefixWord ++ tailWord_3070337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070337).length < 2 ^ (prefixWord ++ tailWord_3070337).sum := by decide
  have hdescent : baseEnd_3070337 < baseStart_3070337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070347 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 3]
def baseStart_3070347 : Nat := 118140960795 + 3070347 * 2 ^ 59
def prefixEnd_3070347 : Nat := 4983230072969 + 3 ^ 40 * 3070347 * 2
def baseEnd_3070347 : Nat := 1576563787090203986942237

theorem tailTrace_3070347 : CollatzResearch.WordTrace tailWord_3070347 prefixEnd_3070347 1576563787090203986942237 := by
  unfold tailWord_3070347
  simp only [CollatzResearch.WordTrace]
  refine ⟨111984755007664667365201295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74656503338443111576800863 111984755007664667365201295)
  ·
    refine ⟨167977132511497001047801943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111984755007664667365201295 167977132511497001047801943)
    ·
      refine ⟨251965698767245501571702915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167977132511497001047801943 251965698767245501571702915)
      ·
        refine ⟨377948548150868252357554373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251965698767245501571702915 377948548150868252357554373)
        ·
          refine ⟨70865352778287797317041445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 377948548150868252357554373 70865352778287797317041445)
          ·
            refine ⟨13287253645928961996945271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70865352778287797317041445 13287253645928961996945271)
            ·
              refine ⟨19930880468893442995417907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13287253645928961996945271 19930880468893442995417907)
              ·
                refine ⟨29896320703340164493126861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19930880468893442995417907 29896320703340164493126861)
                ·
                  refine ⟨11211120263752561684922573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29896320703340164493126861 11211120263752561684922573)
                  ·
                    refine ⟨4204170098907210631845965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11211120263752561684922573 4204170098907210631845965)
                    ·
                      refine ⟨1576563787090203986942237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4204170098907210631845965 1576563787090203986942237)
                      ·
                        rfl

theorem cell23_3070347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 3].length) (baseStart_3070347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070347 prefixEnd_3070347 := by exact prefixLift 3070347
  have htrace : WordTrace (prefixWord ++ tailWord_3070347) baseStart_3070347 baseEnd_3070347 := by
    simpa [prefixWord, tailWord_3070347, baseEnd_3070347] using wordTrace_append hprefix tailTrace_3070347
  have hstable : (prefixWord ++ tailWord_3070347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070347).length < 2 ^ (prefixWord ++ tailWord_3070347).sum := by decide
  have hdescent : baseEnd_3070347 < baseStart_3070347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070365 : List Nat := [1, 4, 2, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_3070365 : Nat := 118140960795 + 3070365 * 2 ^ 59
def prefixEnd_3070365 : Nat := 4983230072969 + 3 ^ 40 * 3070365 * 2
def baseEnd_3070365 : Nat := 1576573029741984916517155

theorem tailTrace_3070365 : CollatzResearch.WordTrace tailWord_3070365 prefixEnd_3070365 1576573029741984916517155 := by
  unfold tailWord_3070365
  simp only [CollatzResearch.WordTrace]
  refine ⟨111985411521599456439356549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74656941014399637626237699 111985411521599456439356549)
  ·
    refine ⟨20997264660299898082379353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111985411521599456439356549 20997264660299898082379353)
    ·
      refine ⟨15747948495224923561784515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20997264660299898082379353 15747948495224923561784515)
      ·
        refine ⟨23621922742837385342676773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15747948495224923561784515 23621922742837385342676773)
        ·
          refine ⟨4429110514282009751751895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23621922742837385342676773 4429110514282009751751895)
          ·
            refine ⟨6643665771423014627627843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4429110514282009751751895 6643665771423014627627843)
            ·
              refine ⟨9965498657134521941441765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643665771423014627627843 9965498657134521941441765)
              ·
                refine ⟨1868530998212722864020331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9965498657134521941441765 1868530998212722864020331)
                ·
                  refine ⟨2802796497319084296030497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868530998212722864020331 2802796497319084296030497)
                  ·
                    refine ⟨2102097372989313222022873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2802796497319084296030497 2102097372989313222022873)
                    ·
                      refine ⟨1576573029741984916517155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2102097372989313222022873 1576573029741984916517155)
                      ·
                        rfl

theorem cell23_3070365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_3070365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070365 prefixEnd_3070365 := by exact prefixLift 3070365
  have htrace : WordTrace (prefixWord ++ tailWord_3070365) baseStart_3070365 baseEnd_3070365 := by
    simpa [prefixWord, tailWord_3070365, baseEnd_3070365] using wordTrace_append hprefix tailTrace_3070365
  have hstable : (prefixWord ++ tailWord_3070365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070365).length < 2 ^ (prefixWord ++ tailWord_3070365).sum := by decide
  have hdescent : baseEnd_3070365 < baseStart_3070365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070388 : List Nat := [2, 5, 2, 2, 1, 1, 3, 7]
def baseStart_3070388 : Nat := 118140960795 + 3070388 * 2 ^ 59
def prefixEnd_3070388 : Nat := 4983230072969 + 3 ^ 40 * 3070388 * 2
def baseEnd_3070388 : Nat := 58392031103594012093687

theorem tailTrace_3070388 : CollatzResearch.WordTrace tailWord_3070388 prefixEnd_3070388 58392031103594012093687 := by
  unfold tailWord_3070388
  simp only [CollatzResearch.WordTrace]
  refine ⟨55993125200258065683721909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74657500267010754244962545 55993125200258065683721909)
  ·
    refine ⟨5249355487524193657848929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55993125200258065683721909 5249355487524193657848929)
    ·
      refine ⟨3937016615643145243386697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5249355487524193657848929 3937016615643145243386697)
      ·
        refine ⟨2952762461732358932540023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3937016615643145243386697 2952762461732358932540023)
        ·
          refine ⟨4429143692598538398810035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952762461732358932540023 4429143692598538398810035)
          ·
            refine ⟨6643715538897807598215053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4429143692598538398810035 6643715538897807598215053)
            ·
              refine ⟨2491393327086677849330645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6643715538897807598215053 2491393327086677849330645)
              ·
                refine ⟨58392031103594012093687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2491393327086677849330645 58392031103594012093687)
                ·
                  rfl

theorem cell23_3070388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 7].length) (baseStart_3070388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070388 prefixEnd_3070388 := by exact prefixLift 3070388
  have htrace : WordTrace (prefixWord ++ tailWord_3070388) baseStart_3070388 baseEnd_3070388 := by
    simpa [prefixWord, tailWord_3070388, baseEnd_3070388] using wordTrace_append hprefix tailTrace_3070388
  have hstable : (prefixWord ++ tailWord_3070388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070388).length < 2 ^ (prefixWord ++ tailWord_3070388).sum := by decide
  have hdescent : baseEnd_3070388 < baseStart_3070388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070408 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 1, 3, 2]
def baseStart_3070408 : Nat := 118140960795 + 3070408 * 2 ^ 59
def prefixEnd_3070408 : Nat := 4983230072969 + 3 ^ 40 * 3070408 * 2
def baseEnd_3070408 : Nat := 1576595109410128248279457

theorem tailTrace_3070408 : CollatzResearch.WordTrace tailWord_3070408 prefixEnd_3070408 1576595109410128248279457 := by
  unfold tailWord_3070408
  simp only [CollatzResearch.WordTrace]
  refine ⟨55993489930221837391585939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74657986573629116522114585 55993489930221837391585939)
  ·
    refine ⟨83990234895332756087378909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55993489930221837391585939 83990234895332756087378909)
    ·
      refine ⟨31496338085749783532767091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83990234895332756087378909 31496338085749783532767091)
      ·
        refine ⟨47244507128624675299150637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31496338085749783532767091 47244507128624675299150637)
        ·
          refine ⟨17716690173234253237181489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47244507128624675299150637 17716690173234253237181489)
          ·
            refine ⟨13287517629925689927886117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17716690173234253237181489 13287517629925689927886117)
            ·
              refine ⟨2491409555611066861478647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13287517629925689927886117 2491409555611066861478647)
              ·
                refine ⟨3737114333416600292217971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491409555611066861478647 3737114333416600292217971)
                ·
                  refine ⟨5605671500124900438326957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737114333416600292217971 5605671500124900438326957)
                  ·
                    refine ⟨2102126812546837664372609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5605671500124900438326957 2102126812546837664372609)
                    ·
                      refine ⟨1576595109410128248279457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2102126812546837664372609 1576595109410128248279457)
                      ·
                        rfl

theorem cell23_3070408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_3070408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070408 prefixEnd_3070408 := by exact prefixLift 3070408
  have htrace : WordTrace (prefixWord ++ tailWord_3070408) baseStart_3070408 baseEnd_3070408 := by
    simpa [prefixWord, tailWord_3070408, baseEnd_3070408] using wordTrace_append hprefix tailTrace_3070408
  have hstable : (prefixWord ++ tailWord_3070408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070408).length < 2 ^ (prefixWord ++ tailWord_3070408).sum := by decide
  have hdescent : baseEnd_3070408 < baseStart_3070408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070457 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 1, 7]
def baseStart_3070457 : Nat := 118140960795 + 3070457 * 2 ^ 59
def prefixEnd_3070457 : Nat := 4983230072969 + 3 ^ 40 * 3070457 * 2
def baseEnd_3070457 : Nat := 525540089987399518855577

theorem tailTrace_3070457 : CollatzResearch.WordTrace tailWord_3070457 prefixEnd_3070457 525540089987399518855577 := by
  unfold tailWord_3070457
  simp only [CollatzResearch.WordTrace]
  refine ⟨111988767037266156151705625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74659178024844104101137083 111988767037266156151705625)
  ·
    refine ⟨83991575277949617113779219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111988767037266156151705625 83991575277949617113779219)
    ·
      refine ⟨125987362916924425670668829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83991575277949617113779219 125987362916924425670668829)
      ·
        refine ⟨47245261093846659626500811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125987362916924425670668829 47245261093846659626500811)
        ·
          refine ⟨70867891640769989439751217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47245261093846659626500811 70867891640769989439751217)
          ·
            refine ⟨53150918730577492079813413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70867891640769989439751217 53150918730577492079813413)
            ·
              refine ⟨9965797261983279764965015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53150918730577492079813413 9965797261983279764965015)
              ·
                refine ⟨14948695892974919647447523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9965797261983279764965015 14948695892974919647447523)
                ·
                  refine ⟨22423043839462379471171285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14948695892974919647447523 22423043839462379471171285)
                  ·
                    refine ⟨525540089987399518855577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22423043839462379471171285 525540089987399518855577)
                    ·
                      rfl

theorem cell23_3070457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_3070457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070457 prefixEnd_3070457 := by exact prefixLift 3070457
  have htrace : WordTrace (prefixWord ++ tailWord_3070457) baseStart_3070457 baseEnd_3070457 := by
    simpa [prefixWord, tailWord_3070457, baseEnd_3070457] using wordTrace_append hprefix tailTrace_3070457
  have hstable : (prefixWord ++ tailWord_3070457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070457).length < 2 ^ (prefixWord ++ tailWord_3070457).sum := by decide
  have hdescent : baseEnd_3070457 < baseStart_3070457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070467 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 5]
def baseStart_3070467 : Nat := 118140960795 + 3070467 * 2 ^ 59
def prefixEnd_3070467 : Nat := 4983230072969 + 3 ^ 40 * 3070467 * 2
def baseEnd_3070467 : Nat := 1576625404768743517441685

theorem tailTrace_3070467 : CollatzResearch.WordTrace tailWord_3070467 prefixEnd_3070467 1576625404768743517441685 := by
  unfold tailWord_3070467
  simp only [CollatzResearch.WordTrace]
  refine ⟨111989131767229927859569655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74659421178153285239713103 111989131767229927859569655)
  ·
    refine ⟨167983697650844891789354483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111989131767229927859569655 167983697650844891789354483)
    ·
      refine ⟨251975546476267337684031725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167983697650844891789354483 251975546476267337684031725)
      ·
        refine ⟨94490829928600251631511897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251975546476267337684031725 94490829928600251631511897)
        ·
          refine ⟨70868122446450188723633923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94490829928600251631511897 70868122446450188723633923)
          ·
            refine ⟨106302183669675283085450885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70868122446450188723633923 106302183669675283085450885)
            ·
              refine ⟨19931659438064115578522041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106302183669675283085450885 19931659438064115578522041)
              ·
                refine ⟨14948744578548086683891531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19931659438064115578522041 14948744578548086683891531)
                ·
                  refine ⟨22423116867822130025837297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14948744578548086683891531 22423116867822130025837297)
                  ·
                    refine ⟨16817337650866597519377973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22423116867822130025837297 16817337650866597519377973)
                    ·
                      refine ⟨1576625404768743517441685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16817337650866597519377973 1576625404768743517441685)
                      ·
                        rfl

theorem cell23_3070467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_3070467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070467 prefixEnd_3070467 := by exact prefixLift 3070467
  have htrace : WordTrace (prefixWord ++ tailWord_3070467) baseStart_3070467 baseEnd_3070467 := by
    simpa [prefixWord, tailWord_3070467, baseEnd_3070467] using wordTrace_append hprefix tailTrace_3070467
  have hstable : (prefixWord ++ tailWord_3070467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070467).length < 2 ^ (prefixWord ++ tailWord_3070467).sum := by decide
  have hdescent : baseEnd_3070467 < baseStart_3070467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070474 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_3070474 : Nat := 118140960795 + 3070474 * 2 ^ 59
def prefixEnd_3070474 : Nat := 4983230072969 + 3 ^ 40 * 3070474 * 2
def baseEnd_3070474 : Nat := 525542999711108330018051

theorem tailTrace_3070474 : CollatzResearch.WordTrace tailWord_3070474 prefixEnd_3070474 525542999711108330018051 := by
  unfold tailWord_3070474
  simp only [CollatzResearch.WordTrace]
  refine ⟨27997346769551142013768619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74659591385469712036716317 27997346769551142013768619)
  ·
    refine ⟨41996020154326713020652929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27997346769551142013768619 41996020154326713020652929)
    ·
      refine ⟨31497015115745034765489697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41996020154326713020652929 31497015115745034765489697)
      ·
        refine ⟨23622761336808776074117273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31497015115745034765489697 23622761336808776074117273)
        ·
          refine ⟨17717071002606582055587955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23622761336808776074117273 17717071002606582055587955)
          ·
            refine ⟨26575606503909873083381933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17717071002606582055587955 26575606503909873083381933)
            ·
              refine ⟨9965852438966202406268225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26575606503909873083381933 9965852438966202406268225)
              ·
                refine ⟨7474389329224651804701169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9965852438966202406268225 7474389329224651804701169)
                ·
                  refine ⟨5605791996918488853525877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7474389329224651804701169 5605791996918488853525877)
                  ·
                    refine ⟨525542999711108330018051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5605791996918488853525877 525542999711108330018051)
                    ·
                      rfl

theorem cell23_3070474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_3070474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070474 prefixEnd_3070474 := by exact prefixLift 3070474
  have htrace : WordTrace (prefixWord ++ tailWord_3070474) baseStart_3070474 baseEnd_3070474 := by
    simpa [prefixWord, tailWord_3070474, baseEnd_3070474] using wordTrace_append hprefix tailTrace_3070474
  have hstable : (prefixWord ++ tailWord_3070474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070474).length < 2 ^ (prefixWord ++ tailWord_3070474).sum := by decide
  have hdescent : baseEnd_3070474 < baseStart_3070474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070478 : List Nat := [4, 1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_3070478 : Nat := 118140960795 + 3070478 * 2 ^ 59
def prefixEnd_3070478 : Nat := 4983230072969 + 3 ^ 40 * 3070478 * 2
def baseEnd_3070478 : Nat := 175181228117326997156015

theorem tailTrace_3070478 : CollatzResearch.WordTrace tailWord_3070478 prefixEnd_3070478 175181228117326997156015 := by
  unfold tailWord_3070478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13998691621273759592277511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74659688646793384492146725 13998691621273759592277511)
  ·
    refine ⟨20998037431910639388416267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13998691621273759592277511 20998037431910639388416267)
    ·
      refine ⟨31497056147865959082624401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20998037431910639388416267 31497056147865959082624401)
      ·
        refine ⟨23622792110899469311968301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31497056147865959082624401 23622792110899469311968301)
        ·
          refine ⟨8858547041587300991988113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23622792110899469311968301 8858547041587300991988113)
          ·
            refine ⟨6643910281190475743991085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8858547041587300991988113 6643910281190475743991085)
            ·
              refine ⟨2491466355446428403996657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6643910281190475743991085 2491466355446428403996657)
              ·
                refine ⟨1868599766584821302997493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2491466355446428403996657 1868599766584821302997493)
                ·
                  refine ⟨175181228117326997156015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1868599766584821302997493 175181228117326997156015)
                  ·
                    rfl

theorem cell23_3070478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_3070478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070478 prefixEnd_3070478 := by exact prefixLift 3070478
  have htrace : WordTrace (prefixWord ++ tailWord_3070478) baseStart_3070478 baseEnd_3070478 := by
    simpa [prefixWord, tailWord_3070478, baseEnd_3070478] using wordTrace_append hprefix tailTrace_3070478
  have hstable : (prefixWord ++ tailWord_3070478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070478).length < 2 ^ (prefixWord ++ tailWord_3070478).sum := by decide
  have hdescent : baseEnd_3070478 < baseStart_3070478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070507 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 4]
def baseStart_3070507 : Nat := 118140960795 + 3070507 * 2 ^ 59
def prefixEnd_3070507 : Nat := 4983230072969 + 3 ^ 40 * 3070507 * 2
def baseEnd_3070507 : Nat := 1576645943994923360941501

theorem tailTrace_3070507 : CollatzResearch.WordTrace tailWord_3070507 prefixEnd_3070507 1576645943994923360941501 := by
  unfold tailWord_3070507
  simp only [CollatzResearch.WordTrace]
  refine ⟨111990590687085014691025775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74660393791390009794017183 111990590687085014691025775)
  ·
    refine ⟨167985886030627522036538663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111990590687085014691025775 167985886030627522036538663)
    ·
      refine ⟨251978829045941283054807995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167985886030627522036538663 251978829045941283054807995)
      ·
        refine ⟨377968243568911924582211993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251978829045941283054807995 377968243568911924582211993)
        ·
          refine ⟨283476182676683943436658995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377968243568911924582211993 283476182676683943436658995)
          ·
            refine ⟨425214274015025915154988493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283476182676683943436658995 425214274015025915154988493)
            ·
              refine ⟨159455352755634718183120685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 425214274015025915154988493 159455352755634718183120685)
              ·
                refine ⟨59795757283363019318670257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159455352755634718183120685 59795757283363019318670257)
                ·
                  refine ⟨44846817962522264489002693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59795757283363019318670257 44846817962522264489002693)
                  ·
                    refine ⟨8408778367972924591688005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44846817962522264489002693 8408778367972924591688005)
                    ·
                      refine ⟨1576645943994923360941501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8408778367972924591688005 1576645943994923360941501)
                      ·
                        rfl

theorem cell23_3070507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 4].length) (baseStart_3070507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070507 prefixEnd_3070507 := by exact prefixLift 3070507
  have htrace : WordTrace (prefixWord ++ tailWord_3070507) baseStart_3070507 baseEnd_3070507 := by
    simpa [prefixWord, tailWord_3070507, baseEnd_3070507] using wordTrace_append hprefix tailTrace_3070507
  have hstable : (prefixWord ++ tailWord_3070507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070507).length < 2 ^ (prefixWord ++ tailWord_3070507).sum := by decide
  have hdescent : baseEnd_3070507 < baseStart_3070507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070514 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_3070514 : Nat := 118140960795 + 3070514 * 2 ^ 59
def prefixEnd_3070514 : Nat := 4983230072969 + 3 ^ 40 * 3070514 * 2
def baseEnd_3070514 : Nat := 1576649538359504833553969

theorem tailTrace_3070514 : CollatzResearch.WordTrace tailWord_3070514 prefixEnd_3070514 1576649538359504833553969 := by
  unfold tailWord_3070514
  simp only [CollatzResearch.WordTrace]
  refine ⟨27997711499514913721632649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74660563998706436591020397 27997711499514913721632649)
  ·
    refine ⟨20998283624636185291224487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27997711499514913721632649 20998283624636185291224487)
    ·
      refine ⟨31497425436954277936836731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20998283624636185291224487 31497425436954277936836731)
      ·
        refine ⟨47246138155431416905255097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31497425436954277936836731 47246138155431416905255097)
        ·
          refine ⟨35434603616573562678941323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47246138155431416905255097 35434603616573562678941323)
          ·
            refine ⟨53151905424860344018411985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35434603616573562678941323 53151905424860344018411985)
            ·
              refine ⟨39863929068645258013808989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53151905424860344018411985 39863929068645258013808989)
              ·
                refine ⟨14948973400741971755178371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39863929068645258013808989 14948973400741971755178371)
                ·
                  refine ⟨22423460101112957632767557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14948973400741971755178371 22423460101112957632767557)
                  ·
                    refine ⟨4204398768958679556143917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22423460101112957632767557 4204398768958679556143917)
                    ·
                      refine ⟨1576649538359504833553969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4204398768958679556143917 1576649538359504833553969)
                      ·
                        rfl

theorem cell23_3070514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_3070514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070514 prefixEnd_3070514 := by exact prefixLift 3070514
  have htrace : WordTrace (prefixWord ++ tailWord_3070514) baseStart_3070514 baseEnd_3070514 := by
    simpa [prefixWord, tailWord_3070514, baseEnd_3070514] using wordTrace_append hprefix tailTrace_3070514
  have hstable : (prefixWord ++ tailWord_3070514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070514).length < 2 ^ (prefixWord ++ tailWord_3070514).sum := by decide
  have hdescent : baseEnd_3070514 < baseStart_3070514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070538 : List Nat := [3, 1, 2, 1, 1, 5, 1, 4, 1, 4]
def baseStart_3070538 : Nat := 118140960795 + 3070538 * 2 ^ 59
def prefixEnd_3070538 : Nat := 4983230072969 + 3 ^ 40 * 3070538 * 2
def baseEnd_3070538 : Nat := 525553953965070913217953

theorem tailTrace_3070538 : CollatzResearch.WordTrace tailWord_3070538 prefixEnd_3070538 525553953965070913217953 := by
  unfold tailWord_3070538
  simp only [CollatzResearch.WordTrace]
  refine ⟨27997930337493176746351067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74661147566648471323602845 27997930337493176746351067)
  ·
    refine ⟨41996895506239765119526601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27997930337493176746351067 41996895506239765119526601)
    ·
      refine ⟨31497671629679823839644951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41996895506239765119526601 31497671629679823839644951)
      ·
        refine ⟨47246507444519735759467427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31497671629679823839644951 47246507444519735759467427)
        ·
          refine ⟨70869761166779603639201141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47246507444519735759467427 70869761166779603639201141)
          ·
            refine ⟨6644040109385587841175107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70869761166779603639201141 6644040109385587841175107)
            ·
              refine ⟨9966060164078381761762661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6644040109385587841175107 9966060164078381761762661)
              ·
                refine ⟨1868636280764696580330499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9966060164078381761762661 1868636280764696580330499)
                ·
                  refine ⟨2802954421147044870495749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868636280764696580330499 2802954421147044870495749)
                  ·
                    refine ⟨525553953965070913217953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2802954421147044870495749 525553953965070913217953)
                    ·
                      rfl

theorem cell23_3070538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_3070538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070538 prefixEnd_3070538 := by exact prefixLift 3070538
  have htrace : WordTrace (prefixWord ++ tailWord_3070538) baseStart_3070538 baseEnd_3070538 := by
    simpa [prefixWord, tailWord_3070538, baseEnd_3070538] using wordTrace_append hprefix tailTrace_3070538
  have hstable : (prefixWord ++ tailWord_3070538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070538).length < 2 ^ (prefixWord ++ tailWord_3070538).sum := by decide
  have hdescent : baseEnd_3070538 < baseStart_3070538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070561 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 5, 1, 3]
def baseStart_3070561 : Nat := 118140960795 + 3070561 * 2 ^ 59
def prefixEnd_3070561 : Nat := 4983230072969 + 3 ^ 40 * 3070561 * 2
def baseEnd_3070561 : Nat := 1576673671950266149666253

theorem tailTrace_3070561 : CollatzResearch.WordTrace tailWord_3070561 prefixEnd_3070561 1576673671950266149666253 := by
  unfold tailWord_3070561
  simp only [CollatzResearch.WordTrace]
  refine ⟨111992560228889381913491537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74661706819259587942327691 111992560228889381913491537)
  ·
    refine ⟨83994420171667036435118653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111992560228889381913491537 83994420171667036435118653)
    ·
      refine ⟨31497907564375138663169495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83994420171667036435118653 31497907564375138663169495)
      ·
        refine ⟨47246861346562707994754243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31497907564375138663169495 47246861346562707994754243)
        ·
          refine ⟨70870292019844061992131365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47246861346562707994754243 70870292019844061992131365)
          ·
            refine ⟨13288179753720761623524631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70870292019844061992131365 13288179753720761623524631)
            ·
              refine ⟨19932269630581142435286947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13288179753720761623524631 19932269630581142435286947)
              ·
                refine ⟨29898404445871713652930421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19932269630581142435286947 29898404445871713652930421)
                ·
                  refine ⟨2802975416800473154962227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29898404445871713652930421 2802975416800473154962227)
                  ·
                    refine ⟨4204463125200709732443341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2802975416800473154962227 4204463125200709732443341)
                    ·
                      refine ⟨1576673671950266149666253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4204463125200709732443341 1576673671950266149666253)
                      ·
                        rfl

theorem cell23_3070561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_3070561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070561 prefixEnd_3070561 := by exact prefixLift 3070561
  have htrace : WordTrace (prefixWord ++ tailWord_3070561) baseStart_3070561 baseEnd_3070561 := by
    simpa [prefixWord, tailWord_3070561, baseEnd_3070561] using wordTrace_append hprefix tailTrace_3070561
  have hstable : (prefixWord ++ tailWord_3070561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070561).length < 2 ^ (prefixWord ++ tailWord_3070561).sum := by decide
  have hdescent : baseEnd_3070561 < baseStart_3070561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070562 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3070562 : Nat := 118140960795 + 3070562 * 2 ^ 59
def prefixEnd_3070562 : Nat := 4983230072969 + 3 ^ 40 * 3070562 * 2
def baseEnd_3070562 : Nat := 1576674185430920645753749

theorem tailTrace_3070562 : CollatzResearch.WordTrace tailWord_3070562 prefixEnd_3070562 1576674185430920645753749 := by
  unfold tailWord_3070562
  simp only [CollatzResearch.WordTrace]
  refine ⟨27998149175471439771069485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74661731134590506056185293 27998149175471439771069485)
  ·
    refine ⟨10499305940801789914151057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27998149175471439771069485 10499305940801789914151057)
    ·
      refine ⟨7874479455601342435613293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10499305940801789914151057 7874479455601342435613293)
      ·
        refine ⟨2952929795850503413354985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7874479455601342435613293 2952929795850503413354985)
        ·
          refine ⟨2214697346887877560016239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2952929795850503413354985 2214697346887877560016239)
          ·
            refine ⟨3322046020331816340024359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214697346887877560016239 3322046020331816340024359)
            ·
              refine ⟨4983069030497724510036539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322046020331816340024359 4983069030497724510036539)
              ·
                refine ⟨7474603545746586765054809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4983069030497724510036539 7474603545746586765054809)
                ·
                  refine ⟨5605952659309940073791107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7474603545746586765054809 5605952659309940073791107)
                  ·
                    refine ⟨8408928988964910110686661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5605952659309940073791107 8408928988964910110686661)
                    ·
                      refine ⟨1576674185430920645753749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8408928988964910110686661 1576674185430920645753749)
                      ·
                        rfl

theorem cell23_3070562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3070562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070562 prefixEnd_3070562 := by exact prefixLift 3070562
  have htrace : WordTrace (prefixWord ++ tailWord_3070562) baseStart_3070562 baseEnd_3070562 := by
    simpa [prefixWord, tailWord_3070562, baseEnd_3070562] using wordTrace_append hprefix tailTrace_3070562
  have hstable : (prefixWord ++ tailWord_3070562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070562).length < 2 ^ (prefixWord ++ tailWord_3070562).sum := by decide
  have hdescent : baseEnd_3070562 < baseStart_3070562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070564 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_3070564 : Nat := 118140960795 + 3070564 * 2 ^ 59
def prefixEnd_3070564 : Nat := 4983230072969 + 3 ^ 40 * 3070564 * 2
def baseEnd_3070564 : Nat := 525558404130743212642913

theorem tailTrace_3070564 : CollatzResearch.WordTrace tailWord_3070564 prefixEnd_3070564 525558404130743212642913 := by
  unfold tailWord_3070564
  simp only [CollatzResearch.WordTrace]
  refine ⟨55996334823939256712925373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74661779765252342283900497 55996334823939256712925373)
  ·
    refine ⟨20998625558977221267347015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55996334823939256712925373 20998625558977221267347015)
    ·
      refine ⟨31497938338465831901020523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20998625558977221267347015 31497938338465831901020523)
      ·
        refine ⟨47246907507698747851530785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31497938338465831901020523 47246907507698747851530785)
        ·
          refine ⟨35435180630774060888648089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47246907507698747851530785 35435180630774060888648089)
          ·
            refine ⟨26576385473080545666486067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35435180630774060888648089 26576385473080545666486067)
            ·
              refine ⟨39864578209620818499729101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26576385473080545666486067 39864578209620818499729101)
              ·
                refine ⟨14949216828607806937398413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39864578209620818499729101 14949216828607806937398413)
                ·
                  refine ⟨5605956310727927601524405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14949216828607806937398413 5605956310727927601524405)
                  ·
                    refine ⟨525558404130743212642913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5605956310727927601524405 525558404130743212642913)
                    ·
                      rfl

theorem cell23_3070564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_3070564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070564 prefixEnd_3070564 := by exact prefixLift 3070564
  have htrace : WordTrace (prefixWord ++ tailWord_3070564) baseStart_3070564 baseEnd_3070564 := by
    simpa [prefixWord, tailWord_3070564, baseEnd_3070564] using wordTrace_append hprefix tailTrace_3070564
  have hstable : (prefixWord ++ tailWord_3070564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070564).length < 2 ^ (prefixWord ++ tailWord_3070564).sum := by decide
  have hdescent : baseEnd_3070564 < baseStart_3070564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070565 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 2, 2, 3]
def baseStart_3070565 : Nat := 118140960795 + 3070565 * 2 ^ 59
def prefixEnd_3070565 : Nat := 4983230072969 + 3 ^ 40 * 3070565 * 2
def baseEnd_3070565 : Nat := 1576675725872884134016235

theorem tailTrace_3070565 : CollatzResearch.WordTrace tailWord_3070565 prefixEnd_3070565 1576675725872884134016235 := by
  unfold tailWord_3070565
  simp only [CollatzResearch.WordTrace]
  refine ⟨111992706120874890596637149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74661804080583260397758099 111992706120874890596637149)
  ·
    refine ⟨41997264795328083973738931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111992706120874890596637149 41997264795328083973738931)
    ·
      refine ⟨62995897192992125960608397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41997264795328083973738931 62995897192992125960608397)
      ·
        refine ⟨23623461447372047235228149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62995897192992125960608397 23623461447372047235228149)
        ·
          refine ⟨2214699510691129428302639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23623461447372047235228149 2214699510691129428302639)
          ·
            refine ⟨3322049266036694142453959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214699510691129428302639 3322049266036694142453959)
            ·
              refine ⟨4983073899055041213680939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322049266036694142453959 4983073899055041213680939)
              ·
                refine ⟨7474610848582561820521409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4983073899055041213680939 7474610848582561820521409)
                ·
                  refine ⟨5605958136436921365391057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7474610848582561820521409 5605958136436921365391057)
                  ·
                    refine ⟨4204468602327691024043293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5605958136436921365391057 4204468602327691024043293)
                    ·
                      refine ⟨1576675725872884134016235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4204468602327691024043293 1576675725872884134016235)
                      ·
                        rfl

theorem cell23_3070565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_3070565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070565 prefixEnd_3070565 := by exact prefixLift 3070565
  have htrace : WordTrace (prefixWord ++ tailWord_3070565) baseStart_3070565 baseEnd_3070565 := by
    simpa [prefixWord, tailWord_3070565, baseEnd_3070565] using wordTrace_append hprefix tailTrace_3070565
  have hstable : (prefixWord ++ tailWord_3070565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070565).length < 2 ^ (prefixWord ++ tailWord_3070565).sum := by decide
  have hdescent : baseEnd_3070565 < baseStart_3070565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070571 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 2, 3, 2]
def baseStart_3070571 : Nat := 118140960795 + 3070571 * 2 ^ 59
def prefixEnd_3070571 : Nat := 4983230072969 + 3 ^ 40 * 3070571 * 2
def baseEnd_3070571 : Nat := 1576678806756811110541207

theorem tailTrace_3070571 : CollatzResearch.WordTrace tailWord_3070571 prefixEnd_3070571 1576678806756811110541207 := by
  unfold tailWord_3070571
  simp only [CollatzResearch.WordTrace]
  refine ⟨111992924958853153621355567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74661949972568769080903711 111992924958853153621355567)
  ·
    refine ⟨167989387438279730432033351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111992924958853153621355567 167989387438279730432033351)
    ·
      refine ⟨251984081157419595648050027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167989387438279730432033351 251984081157419595648050027)
      ·
        refine ⟨377976121736129393472075041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251984081157419595648050027 377976121736129393472075041)
        ·
          refine ⟨283482091302097045104056281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377976121736129393472075041 283482091302097045104056281)
          ·
            refine ⟨212611568476572783828042211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283482091302097045104056281 212611568476572783828042211)
            ·
              refine ⟨318917352714859175742063317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212611568476572783828042211 318917352714859175742063317)
              ·
                refine ⟨7474625454254511931454609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 318917352714859175742063317 7474625454254511931454609)
                ·
                  refine ⟨5605969090690883948590957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7474625454254511931454609 5605969090690883948590957)
                  ·
                    refine ⟨2102238409009081480721609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5605969090690883948590957 2102238409009081480721609)
                    ·
                      refine ⟨1576678806756811110541207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2102238409009081480721609 1576678806756811110541207)
                      ·
                        rfl

theorem cell23_3070571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 3, 2].length) (baseStart_3070571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070571 prefixEnd_3070571 := by exact prefixLift 3070571
  have htrace : WordTrace (prefixWord ++ tailWord_3070571) baseStart_3070571 baseEnd_3070571 := by
    simpa [prefixWord, tailWord_3070571, baseEnd_3070571] using wordTrace_append hprefix tailTrace_3070571
  have hstable : (prefixWord ++ tailWord_3070571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070571).length < 2 ^ (prefixWord ++ tailWord_3070571).sum := by decide
  have hdescent : baseEnd_3070571 < baseStart_3070571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070604 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 2, 6, 3]
def baseStart_3070604 : Nat := 118140960795 + 3070604 * 2 ^ 59
def prefixEnd_3070604 : Nat := 4983230072969 + 3 ^ 40 * 3070604 * 2
def baseEnd_3070604 : Nat := 1576695751618409481428555

theorem tailTrace_3070604 : CollatzResearch.WordTrace tailWord_3070604 prefixEnd_3070604 1576695751618409481428555 := by
  unfold tailWord_3070604
  simp only [CollatzResearch.WordTrace]
  refine ⟨55997064283866800128653433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74662752378489066838204577 55997064283866800128653433)
  ·
    refine ⟨41997798212900100096490075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55997064283866800128653433 41997798212900100096490075)
    ·
      refine ⟨62996697319350150144735113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41997798212900100096490075 62996697319350150144735113)
      ·
        refine ⟨47247522989512612608551335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62996697319350150144735113 47247522989512612608551335)
        ·
          refine ⟨70871284484268918912827003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47247522989512612608551335 70871284484268918912827003)
          ·
            refine ⟨106306926726403378369240505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70871284484268918912827003 106306926726403378369240505)
            ·
              refine ⟨79730195044802533776930379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106306926726403378369240505 79730195044802533776930379)
              ·
                refine ⟨119595292567203800665395569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79730195044802533776930379 119595292567203800665395569)
                ·
                  refine ⟨89696469425402850499046677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119595292567203800665395569 89696469425402850499046677)
                  ·
                    refine ⟨4204522004315758617142813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89696469425402850499046677 4204522004315758617142813)
                    ·
                      refine ⟨1576695751618409481428555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4204522004315758617142813 1576695751618409481428555)
                      ·
                        rfl

theorem cell23_3070604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_3070604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070604 prefixEnd_3070604 := by exact prefixLift 3070604
  have htrace : WordTrace (prefixWord ++ tailWord_3070604) baseStart_3070604 baseEnd_3070604 := by
    simpa [prefixWord, tailWord_3070604, baseEnd_3070604] using wordTrace_append hprefix tailTrace_3070604
  have hstable : (prefixWord ++ tailWord_3070604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070604).length < 2 ^ (prefixWord ++ tailWord_3070604).sum := by decide
  have hdescent : baseEnd_3070604 < baseStart_3070604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070621 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_3070621 : Nat := 118140960795 + 3070621 * 2 ^ 59
def prefixEnd_3070621 : Nat := 4983230072969 + 3 ^ 40 * 3070621 * 2
def baseEnd_3070621 : Nat := 1576704480789535914915977

theorem tailTrace_3070621 : CollatzResearch.WordTrace tailWord_3070621 prefixEnd_3070621 1576704480789535914915977 := by
  unfold tailWord_3070621
  simp only [CollatzResearch.WordTrace]
  refine ⟨111994748608672012160675717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74663165739114674773783811 111994748608672012160675717)
  ·
    refine ⟨20999015364126002280126697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111994748608672012160675717 20999015364126002280126697)
    ·
      refine ⟨15749261523094501710095023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20999015364126002280126697 15749261523094501710095023)
      ·
        refine ⟨23623892284641752565142535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15749261523094501710095023 23623892284641752565142535)
        ·
          refine ⟨35435838426962628847713803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23623892284641752565142535 35435838426962628847713803)
          ·
            refine ⟨53153757640443943271570705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35435838426962628847713803 53153757640443943271570705)
            ·
              refine ⟨39865318230332957453678029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53153757640443943271570705 39865318230332957453678029)
              ·
                refine ⟨14949494336374859045129261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39865318230332957453678029 14949494336374859045129261)
                ·
                  refine ⟨5606060376140572141923473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14949494336374859045129261 5606060376140572141923473)
                  ·
                    refine ⟨4204545282105429106442605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5606060376140572141923473 4204545282105429106442605)
                    ·
                      refine ⟨1576704480789535914915977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4204545282105429106442605 1576704480789535914915977)
                      ·
                        rfl

theorem cell23_3070621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_3070621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070621 prefixEnd_3070621 := by exact prefixLift 3070621
  have htrace : WordTrace (prefixWord ++ tailWord_3070621) baseStart_3070621 baseEnd_3070621 := by
    simpa [prefixWord, tailWord_3070621, baseEnd_3070621] using wordTrace_append hprefix tailTrace_3070621
  have hstable : (prefixWord ++ tailWord_3070621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070621).length < 2 ^ (prefixWord ++ tailWord_3070621).sum := by decide
  have hdescent : baseEnd_3070621 < baseStart_3070621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070638 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3070638 : Nat := 118140960795 + 3070638 * 2 ^ 59
def prefixEnd_3070638 : Nat := 4983230072969 + 3 ^ 40 * 3070638 * 2
def baseEnd_3070638 : Nat := 1576713209960662348403399

theorem tailTrace_3070638 : CollatzResearch.WordTrace tailWord_3070638 prefixEnd_3070638 1576713209960662348403399 := by
  unfold tailWord_3070638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13999421081201303008005571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74663579099740282709363045 13999421081201303008005571)
  ·
    refine ⟨20999131621801954512008357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13999421081201303008005571 20999131621801954512008357)
    ·
      refine ⟨3937337179087866471001567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20999131621801954512008357 3937337179087866471001567)
      ·
        refine ⟨5906005768631799706502351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3937337179087866471001567 5906005768631799706502351)
        ·
          refine ⟨8859008652947699559753527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5906005768631799706502351 8859008652947699559753527)
          ·
            refine ⟨13288512979421549339630291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8859008652947699559753527 13288512979421549339630291)
            ·
              refine ⟨19932769469132324009445437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13288512979421549339630291 19932769469132324009445437)
              ·
                refine ⟨7474788550924621503542039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19932769469132324009445437 7474788550924621503542039)
                ·
                  refine ⟨11212182826386932255313059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7474788550924621503542039 11212182826386932255313059)
                  ·
                    refine ⟨16818274239580398382969589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11212182826386932255313059 16818274239580398382969589)
                    ·
                      refine ⟨1576713209960662348403399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16818274239580398382969589 1576713209960662348403399)
                      ·
                        rfl

theorem cell23_3070638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3070638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070638 prefixEnd_3070638 := by exact prefixLift 3070638
  have htrace : WordTrace (prefixWord ++ tailWord_3070638) baseStart_3070638 baseEnd_3070638 := by
    simpa [prefixWord, tailWord_3070638, baseEnd_3070638] using wordTrace_append hprefix tailTrace_3070638
  have hstable : (prefixWord ++ tailWord_3070638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070638).length < 2 ^ (prefixWord ++ tailWord_3070638).sum := by decide
  have hdescent : baseEnd_3070638 < baseStart_3070638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070646 : List Nat := [5, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_3070646 : Nat := 118140960795 + 3070646 * 2 ^ 59
def prefixEnd_3070646 : Nat := 4983230072969 + 3 ^ 40 * 3070646 * 2
def baseEnd_3070646 : Nat := 1576717317805898317103363

theorem tailTrace_3070646 : CollatzResearch.WordTrace tailWord_3070646 prefixEnd_3070646 1576717317805898317103363 := by
  unfold tailWord_3070646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6999728777098840089395987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74663773622387627620223861 6999728777098840089395987)
  ·
    refine ⟨10499593165648260134093981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6999728777098840089395987 10499593165648260134093981)
    ·
      refine ⟨3937347437118097550285243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10499593165648260134093981 3937347437118097550285243)
      ·
        refine ⟨5906021155677146325427865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3937347437118097550285243 5906021155677146325427865)
        ·
          refine ⟨4429515866757859744070899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5906021155677146325427865 4429515866757859744070899)
          ·
            refine ⟨6644273800136789616106349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4429515866757859744070899 6644273800136789616106349)
            ·
              refine ⟨2491602675051296106039881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6644273800136789616106349 2491602675051296106039881)
              ·
                refine ⟨1868702006288472079529911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2491602675051296106039881 1868702006288472079529911)
                ·
                  refine ⟨2803053009432708119294867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868702006288472079529911 2803053009432708119294867)
                  ·
                    refine ⟨4204579514149062178942301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2803053009432708119294867 4204579514149062178942301)
                    ·
                      refine ⟨1576717317805898317103363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4204579514149062178942301 1576717317805898317103363)
                      ·
                        rfl

theorem cell23_3070646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_3070646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070646 prefixEnd_3070646 := by exact prefixLift 3070646
  have htrace : WordTrace (prefixWord ++ tailWord_3070646) baseStart_3070646 baseEnd_3070646 := by
    simpa [prefixWord, tailWord_3070646, baseEnd_3070646] using wordTrace_append hprefix tailTrace_3070646
  have hstable : (prefixWord ++ tailWord_3070646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070646).length < 2 ^ (prefixWord ++ tailWord_3070646).sum := by decide
  have hdescent : baseEnd_3070646 < baseStart_3070646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070669 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_3070669 : Nat := 118140960795 + 3070669 * 2 ^ 59
def prefixEnd_3070669 : Nat := 4983230072969 + 3 ^ 40 * 3070669 * 2
def baseEnd_3070669 : Nat := 1576729127860951727115757

theorem tailTrace_3070669 : CollatzResearch.WordTrace tailWord_3070669 prefixEnd_3070669 1576729127860951727115757 := by
  unfold tailWord_3070669
  simp only [CollatzResearch.WordTrace]
  refine ⟨111996499312498116358423061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74664332874998744238948707 111996499312498116358423061)
  ·
    refine ⟨5249835905273349204301081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111996499312498116358423061 5249835905273349204301081)
    ·
      refine ⟨3937376928955011903225811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5249835905273349204301081 3937376928955011903225811)
      ·
        refine ⟨5906065393432517854838717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3937376928955011903225811 5906065393432517854838717)
        ·
          refine ⟨2214774522537194195564519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5906065393432517854838717 2214774522537194195564519)
          ·
            refine ⟨3322161783805791293346779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214774522537194195564519 3322161783805791293346779)
            ·
              refine ⟨4983242675708686940020169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322161783805791293346779 4983242675708686940020169)
              ·
                refine ⟨3737432006781515205015127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4983242675708686940020169 3737432006781515205015127)
                ·
                  refine ⟨5606148010172272807522691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737432006781515205015127 5606148010172272807522691)
                  ·
                    refine ⟨8409222015258409211284037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5606148010172272807522691 8409222015258409211284037)
                    ·
                      refine ⟨1576729127860951727115757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8409222015258409211284037 1576729127860951727115757)
                      ·
                        rfl

theorem cell23_3070669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_3070669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070669 prefixEnd_3070669 := by exact prefixLift 3070669
  have htrace : WordTrace (prefixWord ++ tailWord_3070669) baseStart_3070669 baseEnd_3070669 := by
    simpa [prefixWord, tailWord_3070669, baseEnd_3070669] using wordTrace_append hprefix tailTrace_3070669
  have hstable : (prefixWord ++ tailWord_3070669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070669).length < 2 ^ (prefixWord ++ tailWord_3070669).sum := by decide
  have hdescent : baseEnd_3070669 < baseStart_3070669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070701 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_3070701 : Nat := 118140960795 + 3070701 * 2 ^ 59
def prefixEnd_3070701 : Nat := 4983230072969 + 3 ^ 40 * 3070701 * 2
def baseEnd_3070701 : Nat := 525581853080631867305203

theorem tailTrace_3070701 : CollatzResearch.WordTrace tailWord_3070701 prefixEnd_3070701 525581853080631867305203 := by
  unfold tailWord_3070701
  simp only [CollatzResearch.WordTrace]
  refine ⟨111997666448382185823587957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74665110965588123882391971 111997666448382185823587957)
  ·
    refine ⟨10499781229535829920961371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111997666448382185823587957 10499781229535829920961371)
    ·
      refine ⟨15749671844303744881442057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10499781229535829920961371 15749671844303744881442057)
      ·
        refine ⟨11812253883227808661081543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15749671844303744881442057 11812253883227808661081543)
        ·
          refine ⟨17718380824841712991622315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11812253883227808661081543 17718380824841712991622315)
          ·
            refine ⟨26577571237262569487433473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17718380824841712991622315 26577571237262569487433473)
            ·
              refine ⟨19933178427946927115575105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26577571237262569487433473 19933178427946927115575105)
              ·
                refine ⟨14949883820960195336681329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19933178427946927115575105 14949883820960195336681329)
                ·
                  refine ⟨11212412865720146502510997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14949883820960195336681329 11212412865720146502510997)
                  ·
                    refine ⟨525581853080631867305203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11212412865720146502510997 525581853080631867305203)
                    ·
                      rfl

theorem cell23_3070701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_3070701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070701 prefixEnd_3070701 := by exact prefixLift 3070701
  have htrace : WordTrace (prefixWord ++ tailWord_3070701) baseStart_3070701 baseEnd_3070701 := by
    simpa [prefixWord, tailWord_3070701, baseEnd_3070701] using wordTrace_append hprefix tailTrace_3070701
  have hstable : (prefixWord ++ tailWord_3070701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070701).length < 2 ^ (prefixWord ++ tailWord_3070701).sum := by decide
  have hdescent : baseEnd_3070701 < baseStart_3070701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070718 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_3070718 : Nat := 118140960795 + 3070718 * 2 ^ 59
def prefixEnd_3070718 : Nat := 4983230072969 + 3 ^ 40 * 3070718 * 2
def baseEnd_3070718 : Nat := 525584762804340678467677

theorem tailTrace_3070718 : CollatzResearch.WordTrace tailWord_3070718 prefixEnd_3070718 525584762804340678467677 := by
  unfold tailWord_3070718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13999785811165074715869601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74665524326213731817971205 13999785811165074715869601)
  ·
    refine ⟨10499839358373806036902201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13999785811165074715869601 10499839358373806036902201)
    ·
      refine ⟨7874879518780354527676651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10499839358373806036902201 7874879518780354527676651)
      ·
        refine ⟨11812319278170531791514977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7874879518780354527676651 11812319278170531791514977)
        ·
          refine ⟨8859239458627898843636233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11812319278170531791514977 8859239458627898843636233)
          ·
            refine ⟨6644429593970924132727175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8859239458627898843636233 6644429593970924132727175)
            ·
              refine ⟨9966644390956386199090763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6644429593970924132727175 9966644390956386199090763)
              ·
                refine ⟨14949966586434579298636145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9966644390956386199090763 14949966586434579298636145)
                ·
                  refine ⟨11212474939825934473977109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14949966586434579298636145 11212474939825934473977109)
                  ·
                    refine ⟨525584762804340678467677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11212474939825934473977109 525584762804340678467677)
                    ·
                      rfl

theorem cell23_3070718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_3070718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070718 prefixEnd_3070718 := by exact prefixLift 3070718
  have htrace : WordTrace (prefixWord ++ tailWord_3070718) baseStart_3070718 baseEnd_3070718 := by
    simpa [prefixWord, tailWord_3070718, baseEnd_3070718] using wordTrace_append hprefix tailTrace_3070718
  have hstable : (prefixWord ++ tailWord_3070718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070718).length < 2 ^ (prefixWord ++ tailWord_3070718).sum := by decide
  have hdescent : baseEnd_3070718 < baseStart_3070718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070741 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_3070741 : Nat := 118140960795 + 3070741 * 2 ^ 59
def prefixEnd_3070741 : Nat := 4983230072969 + 3 ^ 40 * 3070741 * 2
def baseEnd_3070741 : Nat := 1576766098468075445415425

theorem tailTrace_3070741 : CollatzResearch.WordTrace tailWord_3070741 prefixEnd_3070741 1576766098468075445415425 := by
  unfold tailWord_3070741
  simp only [CollatzResearch.WordTrace]
  refine ⟨111999125368237272655044077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74666083578824848436696051 111999125368237272655044077)
  ·
    refine ⟨41999672013088977245641529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111999125368237272655044077 41999672013088977245641529)
    ·
      refine ⟨31499754009816732934231147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41999672013088977245641529 31499754009816732934231147)
      ·
        refine ⟨47249631014725099401346721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31499754009816732934231147 47249631014725099401346721)
        ·
          refine ⟨35437223261043824551010041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47249631014725099401346721 35437223261043824551010041)
          ·
            refine ⟨26577917445782868413257531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35437223261043824551010041 26577917445782868413257531)
            ·
              refine ⟨39866876168674302619886297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26577917445782868413257531 39866876168674302619886297)
              ·
                refine ⟨29900157126505726964914723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39866876168674302619886297 29900157126505726964914723)
                ·
                  refine ⟨44850235689758590447372085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29900157126505726964914723 44850235689758590447372085)
                  ·
                    refine ⟨4204709595914867854441133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44850235689758590447372085 4204709595914867854441133)
                    ·
                      refine ⟨1576766098468075445415425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4204709595914867854441133 1576766098468075445415425)
                      ·
                        rfl

theorem cell23_3070741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_3070741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070741 prefixEnd_3070741 := by exact prefixLift 3070741
  have htrace : WordTrace (prefixWord ++ tailWord_3070741) baseStart_3070741 baseEnd_3070741 := by
    simpa [prefixWord, tailWord_3070741, baseEnd_3070741] using wordTrace_append hprefix tailTrace_3070741
  have hstable : (prefixWord ++ tailWord_3070741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070741).length < 2 ^ (prefixWord ++ tailWord_3070741).sum := by decide
  have hdescent : baseEnd_3070741 < baseStart_3070741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070748 : List Nat := [2, 2, 3, 1, 1, 3, 1, 5, 5]
def baseStart_3070748 : Nat := 118140960795 + 3070748 * 2 ^ 59
def prefixEnd_3070748 : Nat := 4983230072969 + 3 ^ 40 * 3070748 * 2
def baseEnd_3070748 : Nat := 175196632536961879780877

theorem tailTrace_3070748 : CollatzResearch.WordTrace tailWord_3070748 prefixEnd_3070748 175196632536961879780877 := by
  unfold tailWord_3070748
  simp only [CollatzResearch.WordTrace]
  refine ⟨55999690339605956425274449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74666253786141275233699265 55999690339605956425274449)
  ·
    refine ⟨41999767754704467318955837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55999690339605956425274449 41999767754704467318955837)
    ·
      refine ⟨15749912908014175244608439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41999767754704467318955837 15749912908014175244608439)
      ·
        refine ⟨23624869362021262866912659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15749912908014175244608439 23624869362021262866912659)
        ·
          refine ⟨35437304043031894300368989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23624869362021262866912659 35437304043031894300368989)
          ·
            refine ⟨13288989016136960362638371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35437304043031894300368989 13288989016136960362638371)
            ·
              refine ⟨19933483524205440543957557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13288989016136960362638371 19933483524205440543957557)
              ·
                refine ⟨1868764080394260050996021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19933483524205440543957557 1868764080394260050996021)
                ·
                  refine ⟨175196632536961879780877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1868764080394260050996021 175196632536961879780877)
                  ·
                    rfl

theorem cell23_3070748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_3070748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070748 prefixEnd_3070748 := by exact prefixLift 3070748
  have htrace : WordTrace (prefixWord ++ tailWord_3070748) baseStart_3070748 baseEnd_3070748 := by
    simpa [prefixWord, tailWord_3070748, baseEnd_3070748] using wordTrace_append hprefix tailTrace_3070748
  have hstable : (prefixWord ++ tailWord_3070748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070748).length < 2 ^ (prefixWord ++ tailWord_3070748).sum := by decide
  have hdescent : baseEnd_3070748 < baseStart_3070748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070798 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2]
def baseStart_3070798 : Nat := 118140960795 + 3070798 * 2 ^ 59
def prefixEnd_3070798 : Nat := 4983230072969 + 3 ^ 40 * 3070798 * 2
def baseEnd_3070798 : Nat := 1576795366865381722402663

theorem tailTrace_3070798 : CollatzResearch.WordTrace tailWord_3070798 prefixEnd_3070798 1576795366865381722402663 := by
  unfold tailWord_3070798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14000150541128846423733631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74667469552687180926579365 14000150541128846423733631)
  ·
    refine ⟨21000225811693269635600447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14000150541128846423733631 21000225811693269635600447)
    ·
      refine ⟨31500338717539904453400671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21000225811693269635600447 31500338717539904453400671)
      ·
        refine ⟨47250508076309856680101007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31500338717539904453400671 47250508076309856680101007)
        ·
          refine ⟨70875762114464785020151511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47250508076309856680101007 70875762114464785020151511)
          ·
            refine ⟨106313643171697177530227267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70875762114464785020151511 106313643171697177530227267)
            ·
              refine ⟨159470464757545766295340901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106313643171697177530227267 159470464757545766295340901)
              ·
                refine ⟨29900712142039831180376419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159470464757545766295340901 29900712142039831180376419)
                ·
                  refine ⟨44851068213059746770564629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29900712142039831180376419 44851068213059746770564629)
                  ·
                    refine ⟨2102393822487175629870217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44851068213059746770564629 2102393822487175629870217)
                    ·
                      refine ⟨1576795366865381722402663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2102393822487175629870217 1576795366865381722402663)
                      ·
                        rfl

theorem cell23_3070798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_3070798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070798 prefixEnd_3070798 := by exact prefixLift 3070798
  have htrace : WordTrace (prefixWord ++ tailWord_3070798) baseStart_3070798 baseEnd_3070798 := by
    simpa [prefixWord, tailWord_3070798, baseEnd_3070798] using wordTrace_append hprefix tailTrace_3070798
  have hstable : (prefixWord ++ tailWord_3070798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070798).length < 2 ^ (prefixWord ++ tailWord_3070798).sum := by decide
  have hdescent : baseEnd_3070798 < baseStart_3070798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070821 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 8]
def baseStart_3070821 : Nat := 118140960795 + 3070821 * 2 ^ 59
def prefixEnd_3070821 : Nat := 4983230072969 + 3 ^ 40 * 3070821 * 2
def baseEnd_3070821 : Nat := 175200797435603903601673

theorem tailTrace_3070821 : CollatzResearch.WordTrace tailWord_3070821 prefixEnd_3070821 175200797435603903601673 := by
  unfold tailWord_3070821
  simp only [CollatzResearch.WordTrace]
  refine ⟨112002043207947446317956317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74668028805298297545304211 112002043207947446317956317)
  ·
    refine ⟨42000766202980292369233619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112002043207947446317956317 42000766202980292369233619)
    ·
      refine ⟨63001149304470438553850429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42000766202980292369233619 63001149304470438553850429)
      ·
        refine ⟨23625430989176414457693911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63001149304470438553850429 23625430989176414457693911)
        ·
          refine ⟨35438146483764621686540867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23625430989176414457693911 35438146483764621686540867)
          ·
            refine ⟨53157219725646932529811301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35438146483764621686540867 53157219725646932529811301)
            ·
              refine ⟨9966978698558799849339619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53157219725646932529811301 9966978698558799849339619)
              ·
                refine ⟨14950468047838199774009429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9966978698558799849339619 14950468047838199774009429)
                ·
                  refine ⟨175200797435603903601673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14950468047838199774009429 175200797435603903601673)
                  ·
                    rfl

theorem cell23_3070821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_3070821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070821 prefixEnd_3070821 := by exact prefixLift 3070821
  have htrace : WordTrace (prefixWord ++ tailWord_3070821) baseStart_3070821 baseEnd_3070821 := by
    simpa [prefixWord, tailWord_3070821, baseEnd_3070821] using wordTrace_append hprefix tailTrace_3070821
  have hstable : (prefixWord ++ tailWord_3070821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070821).length < 2 ^ (prefixWord ++ tailWord_3070821).sum := by decide
  have hdescent : baseEnd_3070821 < baseStart_3070821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070876 : List Nat := [2, 2, 3, 3, 2, 2, 2, 2, 1, 4]
def baseStart_3070876 : Nat := 118140960795 + 3070876 * 2 ^ 59
def prefixEnd_3070876 : Nat := 4983230072969 + 3 ^ 40 * 3070876 * 2
def baseEnd_3070876 : Nat := 525611806118810805742435

theorem tailTrace_3070876 : CollatzResearch.WordTrace tailWord_3070876 prefixEnd_3070876 525611806118810805742435 := by
  unfold tailWord_3070876
  simp only [CollatzResearch.WordTrace]
  refine ⟨56002024611374095355604241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74669366148498793807472321 56002024611374095355604241)
  ·
    refine ⟨42001518458530571516703181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56002024611374095355604241 42001518458530571516703181)
    ·
      refine ⟨15750569421948964318763693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42001518458530571516703181 15750569421948964318763693)
      ·
        refine ⟨5906463533230861619536385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15750569421948964318763693 5906463533230861619536385)
        ·
          refine ⟨4429847649923146214652289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5906463533230861619536385 4429847649923146214652289)
          ·
            refine ⟨3322385737442359660989217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4429847649923146214652289 3322385737442359660989217)
            ·
              refine ⟨2491789303081769745741913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3322385737442359660989217 2491789303081769745741913)
              ·
                refine ⟨1868841977311327309306435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2491789303081769745741913 1868841977311327309306435)
                ·
                  refine ⟨2803262965966990963959653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868841977311327309306435 2803262965966990963959653)
                  ·
                    refine ⟨525611806118810805742435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2803262965966990963959653 525611806118810805742435)
                    ·
                      rfl

theorem cell23_3070876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_3070876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070876 prefixEnd_3070876 := by exact prefixLift 3070876
  have htrace : WordTrace (prefixWord ++ tailWord_3070876) baseStart_3070876 baseEnd_3070876 := by
    simpa [prefixWord, tailWord_3070876, baseEnd_3070876] using wordTrace_append hprefix tailTrace_3070876
  have hstable : (prefixWord ++ tailWord_3070876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070876).length < 2 ^ (prefixWord ++ tailWord_3070876).sum := by decide
  have hdescent : baseEnd_3070876 < baseStart_3070876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070898 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_3070898 : Nat := 118140960795 + 3070898 * 2 ^ 59
def prefixEnd_3070898 : Nat := 4983230072969 + 3 ^ 40 * 3070898 * 2
def baseEnd_3070898 : Nat := 525615571643610443717401

theorem tailTrace_3070898 : CollatzResearch.WordTrace tailWord_3070898 prefixEnd_3070898 525615571643610443717401 := by
  unfold tailWord_3070898
  simp only [CollatzResearch.WordTrace]
  refine ⟨28001212907167122117127337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74669901085778992312339565 28001212907167122117127337)
  ·
    refine ⟨21000909680375341587845503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28001212907167122117127337 21000909680375341587845503)
    ·
      refine ⟨31501364520563012381768255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21000909680375341587845503 31501364520563012381768255)
      ·
        refine ⟨47252046780844518572652383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31501364520563012381768255 47252046780844518572652383)
        ·
          refine ⟨70878070171266777858978575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47252046780844518572652383 70878070171266777858978575)
          ·
            refine ⟨106317105256900166788467863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70878070171266777858978575 106317105256900166788467863)
            ·
              refine ⟨159475657885350250182701795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106317105256900166788467863 159475657885350250182701795)
              ·
                refine ⟨239213486828025375274052693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159475657885350250182701795 239213486828025375274052693)
                ·
                  refine ⟨2803283048765922366492805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 239213486828025375274052693 2803283048765922366492805)
                  ·
                    refine ⟨525615571643610443717401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2803283048765922366492805 525615571643610443717401)
                    ·
                      rfl

theorem cell23_3070898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_3070898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070898 prefixEnd_3070898 := by exact prefixLift 3070898
  have htrace : WordTrace (prefixWord ++ tailWord_3070898) baseStart_3070898 baseEnd_3070898 := by
    simpa [prefixWord, tailWord_3070898, baseEnd_3070898] using wordTrace_append hprefix tailTrace_3070898
  have hstable : (prefixWord ++ tailWord_3070898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070898).length < 2 ^ (prefixWord ++ tailWord_3070898).sum := by decide
  have hdescent : baseEnd_3070898 < baseStart_3070898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070909 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 2, 3, 2]
def baseStart_3070909 : Nat := 118140960795 + 3070909 * 2 ^ 59
def prefixEnd_3070909 : Nat := 4983230072969 + 3 ^ 40 * 3070909 * 2
def baseEnd_3070909 : Nat := 1576852363218030788114653

theorem tailTrace_3070909 : CollatzResearch.WordTrace tailWord_3070909 prefixEnd_3070909 1576852363218030788114653 := by
  unfold tailWord_3070909
  simp only [CollatzResearch.WordTrace]
  refine ⟨112005252831628637347159781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74670168554419091564773187 112005252831628637347159781)
  ·
    refine ⟨21000984905930369502592459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112005252831628637347159781 21000984905930369502592459)
    ·
      refine ⟨31501477358895554253888689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21000984905930369502592459 31501477358895554253888689)
      ·
        refine ⟨23626108019171665690416517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31501477358895554253888689 23626108019171665690416517)
        ·
          refine ⟨4429895253594687316953097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23626108019171665690416517 4429895253594687316953097)
          ·
            refine ⟨3322421440196015487714823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4429895253594687316953097 3322421440196015487714823)
            ·
              refine ⟨4983632160294023231572235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322421440196015487714823 4983632160294023231572235)
              ·
                refine ⟨7475448240441034847358353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4983632160294023231572235 7475448240441034847358353)
                ·
                  refine ⟨5606586180330776135518765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7475448240441034847358353 5606586180330776135518765)
                  ·
                    refine ⟨2102469817624041050819537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5606586180330776135518765 2102469817624041050819537)
                    ·
                      refine ⟨1576852363218030788114653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2102469817624041050819537 1576852363218030788114653)
                      ·
                        rfl

theorem cell23_3070909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_3070909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070909 prefixEnd_3070909 := by exact prefixLift 3070909
  have htrace : WordTrace (prefixWord ++ tailWord_3070909) baseStart_3070909 baseEnd_3070909 := by
    simpa [prefixWord, tailWord_3070909, baseEnd_3070909] using wordTrace_append hprefix tailTrace_3070909
  have hstable : (prefixWord ++ tailWord_3070909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070909).length < 2 ^ (prefixWord ++ tailWord_3070909).sum := by decide
  have hdescent : baseEnd_3070909 < baseStart_3070909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070932 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_3070932 : Nat := 118140960795 + 3070932 * 2 ^ 59
def prefixEnd_3070932 : Nat := 4983230072969 + 3 ^ 40 * 3070932 * 2
def baseEnd_3070932 : Nat := 525621391091028066042349

theorem tailTrace_3070932 : CollatzResearch.WordTrace tailWord_3070932 prefixEnd_3070932 525621391091028066042349 := by
  unfold tailWord_3070932
  simp only [CollatzResearch.WordTrace]
  refine ⟨56003045855272656137623525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74670727807030208183498033 56003045855272656137623525)
  ·
    refine ⟨10500571097863623025804411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56003045855272656137623525 10500571097863623025804411)
    ·
      refine ⟨15750856646795434538706617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10500571097863623025804411 15750856646795434538706617)
      ·
        refine ⟨11813142485096575904029963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15750856646795434538706617 11813142485096575904029963)
        ·
          refine ⟨17719713727644863856044945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11813142485096575904029963 17719713727644863856044945)
          ·
            refine ⟨13289785295733647892033709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17719713727644863856044945 13289785295733647892033709)
            ·
              refine ⟨4983669485900117959512641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13289785295733647892033709 4983669485900117959512641)
              ·
                refine ⟨3737752114425088469634481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4983669485900117959512641 3737752114425088469634481)
                ·
                  refine ⟨2803314085818816352225861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3737752114425088469634481 2803314085818816352225861)
                  ·
                    refine ⟨525621391091028066042349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2803314085818816352225861 525621391091028066042349)
                    ·
                      rfl

theorem cell23_3070932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_3070932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070932 prefixEnd_3070932 := by exact prefixLift 3070932
  have htrace : WordTrace (prefixWord ++ tailWord_3070932) baseStart_3070932 baseEnd_3070932 := by
    simpa [prefixWord, tailWord_3070932, baseEnd_3070932] using wordTrace_append hprefix tailTrace_3070932
  have hstable : (prefixWord ++ tailWord_3070932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070932).length < 2 ^ (prefixWord ++ tailWord_3070932).sum := by decide
  have hdescent : baseEnd_3070932 < baseStart_3070932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3070949 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 1, 6]
def baseStart_3070949 : Nat := 118140960795 + 3070949 * 2 ^ 59
def prefixEnd_3070949 : Nat := 4983230072969 + 3 ^ 40 * 3070949 * 2
def baseEnd_3070949 : Nat := 525624300814736877204823

theorem tailTrace_3070949 : CollatzResearch.WordTrace tailWord_3070949 prefixEnd_3070949 525624300814736877204823 := by
  unfold tailWord_3070949
  simp only [CollatzResearch.WordTrace]
  refine ⟨112006711751483724178615901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74671141167655816119077267 112006711751483724178615901)
  ·
    refine ⟨42002516906806396566980963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112006711751483724178615901 42002516906806396566980963)
    ·
      refine ⟨63003775360209594850471445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42002516906806396566980963 63003775360209594850471445)
      ·
        refine ⟨2953301970009824758615849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63003775360209594850471445 2953301970009824758615849)
        ·
          refine ⟨2214976477507368568961887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2953301970009824758615849 2214976477507368568961887)
          ·
            refine ⟨3322464716261052853442831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214976477507368568961887 3322464716261052853442831)
            ·
              refine ⟨4983697074391579280164247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322464716261052853442831 4983697074391579280164247)
              ·
                refine ⟨7475545611587368920246371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4983697074391579280164247 7475545611587368920246371)
                ·
                  refine ⟨11213318417381053380369557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7475545611587368920246371 11213318417381053380369557)
                  ·
                    refine ⟨525624300814736877204823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11213318417381053380369557 525624300814736877204823)
                    ·
                      rfl

theorem cell23_3070949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_3070949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3070949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3070949 prefixEnd_3070949 := by exact prefixLift 3070949
  have htrace : WordTrace (prefixWord ++ tailWord_3070949) baseStart_3070949 baseEnd_3070949 := by
    simpa [prefixWord, tailWord_3070949, baseEnd_3070949] using wordTrace_append hprefix tailTrace_3070949
  have hstable : (prefixWord ++ tailWord_3070949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3070949).length < 2 ^ (prefixWord ++ tailWord_3070949).sum := by decide
  have hdescent : baseEnd_3070949 < baseStart_3070949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3070949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071082 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 2, 5]
def baseStart_3071082 : Nat := 118140960795 + 3071082 * 2 ^ 59
def prefixEnd_3071082 : Nat := 4983230072969 + 3 ^ 40 * 3071082 * 2
def baseEnd_3071082 : Nat := 525647065123752870417119

theorem tailTrace_3071082 : CollatzResearch.WordTrace tailWord_3071082 prefixEnd_3071082 525647065123752870417119 := by
  unfold tailWord_3071082
  simp only [CollatzResearch.WordTrace]
  refine ⟨28002890665000471973301875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74674375106667925262138333 28002890665000471973301875)
  ·
    refine ⟨42004335997500707959952813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28002890665000471973301875 42004335997500707959952813)
    ·
      refine ⟨15751625999062765484982305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42004335997500707959952813 15751625999062765484982305)
      ·
        refine ⟨11813719499297074113736729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15751625999062765484982305 11813719499297074113736729)
        ·
          refine ⟨8860289624472805585302547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11813719499297074113736729 8860289624472805585302547)
          ·
            refine ⟨13290434436709208377953821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8860289624472805585302547 13290434436709208377953821)
            ·
              refine ⟨4983912913765953141732683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13290434436709208377953821 4983912913765953141732683)
              ·
                refine ⟨7475869370648929712599025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4983912913765953141732683 7475869370648929712599025)
                ·
                  refine ⟨5606902027986697284449269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7475869370648929712599025 5606902027986697284449269)
                  ·
                    refine ⟨525647065123752870417119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5606902027986697284449269 525647065123752870417119)
                    ·
                      rfl

theorem cell23_3071082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_3071082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071082 prefixEnd_3071082 := by exact prefixLift 3071082
  have htrace : WordTrace (prefixWord ++ tailWord_3071082) baseStart_3071082 baseEnd_3071082 := by
    simpa [prefixWord, tailWord_3071082, baseEnd_3071082] using wordTrace_append hprefix tailTrace_3071082
  have hstable : (prefixWord ++ tailWord_3071082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071082).length < 2 ^ (prefixWord ++ tailWord_3071082).sum := by decide
  have hdescent : baseEnd_3071082 < baseStart_3071082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071095 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 5, 4]
def baseStart_3071095 : Nat := 118140960795 + 3071095 * 2 ^ 59
def prefixEnd_3071095 : Nat := 4983230072969 + 3 ^ 40 * 3071095 * 2
def baseEnd_3071095 : Nat := 525649290206589020129599

theorem tailTrace_3071095 : CollatzResearch.WordTrace tailWord_3071095 prefixEnd_3071095 525649290206589020129599 := by
  unfold tailWord_3071095
  simp only [CollatzResearch.WordTrace]
  refine ⟨112012036808954791113430739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74674691205969860742287159 112012036808954791113430739)
  ·
    refine ⟨168018055213432186670146109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112012036808954791113430739 168018055213432186670146109)
    ·
      refine ⟨63006770705037070001304791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168018055213432186670146109 63006770705037070001304791)
      ·
        refine ⟨94510156057555605001957187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63006770705037070001304791 94510156057555605001957187)
        ·
          refine ⟨141765234086333407502935781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94510156057555605001957187 141765234086333407502935781)
          ·
            refine ⟨26580981391187513906800459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141765234086333407502935781 26580981391187513906800459)
            ·
              refine ⟨39871472086781270860200689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26580981391187513906800459 39871472086781270860200689)
              ·
                refine ⟨29903604065085953145150517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39871472086781270860200689 29903604065085953145150517)
                ·
                  refine ⟨2803462881101808107357861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29903604065085953145150517 2803462881101808107357861)
                  ·
                    refine ⟨525649290206589020129599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2803462881101808107357861 525649290206589020129599)
                    ·
                      rfl

theorem cell23_3071095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_3071095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071095 prefixEnd_3071095 := by exact prefixLift 3071095
  have htrace : WordTrace (prefixWord ++ tailWord_3071095) baseStart_3071095 baseEnd_3071095 := by
    simpa [prefixWord, tailWord_3071095, baseEnd_3071095] using wordTrace_append hprefix tailTrace_3071095
  have hstable : (prefixWord ++ tailWord_3071095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071095).length < 2 ^ (prefixWord ++ tailWord_3071095).sum := by decide
  have hdescent : baseEnd_3071095 < baseStart_3071095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071122 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_3071122 : Nat := 118140960795 + 3071122 * 2 ^ 59
def prefixEnd_3071122 : Nat := 4983230072969 + 3 ^ 40 * 3071122 * 2
def baseEnd_3071122 : Nat := 1576961734597438454751173

theorem tailTrace_3071122 : CollatzResearch.WordTrace tailWord_3071122 prefixEnd_3071122 1576961734597438454751173 := by
  unfold tailWord_3071122
  simp only [CollatzResearch.WordTrace]
  refine ⟨28003255394964243681165905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74675347719904649816442413 28003255394964243681165905)
  ·
    refine ⟨21002441546223182760874429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28003255394964243681165905 21002441546223182760874429)
    ·
      refine ⟨7875915579833693535327911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21002441546223182760874429 7875915579833693535327911)
      ·
        refine ⟨11813873369750540302991867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7875915579833693535327911 11813873369750540302991867)
        ·
          refine ⟨17720810054625810454487801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11813873369750540302991867 17720810054625810454487801)
          ·
            refine ⟨13290607540969357840865851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17720810054625810454487801 13290607540969357840865851)
            ·
              refine ⟨19935911311454036761298777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13290607540969357840865851 19935911311454036761298777)
              ·
                refine ⟨14951933483590527570974083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19935911311454036761298777 14951933483590527570974083)
                ·
                  refine ⟨22427900225385791356461125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14951933483590527570974083 22427900225385791356461125)
                  ·
                    refine ⟨4205231292259835879336461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22427900225385791356461125 4205231292259835879336461)
                    ·
                      refine ⟨1576961734597438454751173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4205231292259835879336461 1576961734597438454751173)
                      ·
                        rfl

theorem cell23_3071122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_3071122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071122 prefixEnd_3071122 := by exact prefixLift 3071122
  have htrace : WordTrace (prefixWord ++ tailWord_3071122) baseStart_3071122 baseEnd_3071122 := by
    simpa [prefixWord, tailWord_3071122, baseEnd_3071122] using wordTrace_append hprefix tailTrace_3071122
  have hstable : (prefixWord ++ tailWord_3071122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071122).length < 2 ^ (prefixWord ++ tailWord_3071122).sum := by decide
  have hdescent : baseEnd_3071122 < baseStart_3071122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071185 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 1, 6]
def baseStart_3071185 : Nat := 118140960795 + 3071185 * 2 ^ 59
def prefixEnd_3071185 : Nat := 4983230072969 + 3 ^ 40 * 3071185 * 2
def baseEnd_3071185 : Nat := 525664694626223902754461

theorem tailTrace_3071185 : CollatzResearch.WordTrace tailWord_3071185 prefixEnd_3071185 525664694626223902754461 := by
  unfold tailWord_3071185
  simp only [CollatzResearch.WordTrace]
  refine ⟨112015319378628736484207009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74676879585752490989471339 112015319378628736484207009)
  ·
    refine ⟨84011489533971552363155257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112015319378628736484207009 84011489533971552363155257)
    ·
      refine ⟨63008617150478664272366443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84011489533971552363155257 63008617150478664272366443)
      ·
        refine ⟨94512925725717996408549665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63008617150478664272366443 94512925725717996408549665)
        ·
          refine ⟨70884694294288497306412249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94512925725717996408549665 70884694294288497306412249)
          ·
            refine ⟨53163520720716372979809187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70884694294288497306412249 53163520720716372979809187)
            ·
              refine ⟨79745281081074559469713781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53163520720716372979809187 79745281081074559469713781)
              ·
                refine ⟨7476120101350739950285667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79745281081074559469713781 7476120101350739950285667)
                ·
                  refine ⟨11214180152026109925428501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7476120101350739950285667 11214180152026109925428501)
                  ·
                    refine ⟨525664694626223902754461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11214180152026109925428501 525664694626223902754461)
                    ·
                      rfl

theorem cell23_3071185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_3071185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071185 prefixEnd_3071185 := by exact prefixLift 3071185
  have htrace : WordTrace (prefixWord ++ tailWord_3071185) baseStart_3071185 baseEnd_3071185 := by
    simpa [prefixWord, tailWord_3071185, baseEnd_3071185] using wordTrace_append hprefix tailTrace_3071185
  have hstable : (prefixWord ++ tailWord_3071185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071185).length < 2 ^ (prefixWord ++ tailWord_3071185).sum := by decide
  have hdescent : baseEnd_3071185 < baseStart_3071185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071189 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 1, 5]
def baseStart_3071189 : Nat := 118140960795 + 3071189 * 2 ^ 59
def prefixEnd_3071189 : Nat := 4983230072969 + 3 ^ 40 * 3071189 * 2
def baseEnd_3071189 : Nat := 525665379267096564204455

theorem tailTrace_3071189 : CollatzResearch.WordTrace tailWord_3071189 prefixEnd_3071189 525665379267096564204455 := by
  unfold tailWord_3071189
  simp only [CollatzResearch.WordTrace]
  refine ⟨112015465270614245167352621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74676976847076163444901747 112015465270614245167352621)
  ·
    refine ⟨42005799476480341937757233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112015465270614245167352621 42005799476480341937757233)
    ·
      refine ⟨31504349607360256453317925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42005799476480341937757233 31504349607360256453317925)
      ·
        refine ⟨5907065551380048084997111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31504349607360256453317925 5907065551380048084997111)
        ·
          refine ⟨8860598327070072127495667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5907065551380048084997111 8860598327070072127495667)
          ·
            refine ⟨13290897490605108191243501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8860598327070072127495667 13290897490605108191243501)
            ·
              refine ⟨4984086558976915571716313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13290897490605108191243501 4984086558976915571716313)
              ·
                refine ⟨3738064919232686678787235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4984086558976915571716313 3738064919232686678787235)
                ·
                  refine ⟨5607097378849030018180853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738064919232686678787235 5607097378849030018180853)
                  ·
                    refine ⟨525665379267096564204455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5607097378849030018180853 525665379267096564204455)
                    ·
                      rfl

theorem cell23_3071189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_3071189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071189 prefixEnd_3071189 := by exact prefixLift 3071189
  have htrace : WordTrace (prefixWord ++ tailWord_3071189) baseStart_3071189 baseEnd_3071189 := by
    simpa [prefixWord, tailWord_3071189, baseEnd_3071189] using wordTrace_append hprefix tailTrace_3071189
  have hstable : (prefixWord ++ tailWord_3071189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071189).length < 2 ^ (prefixWord ++ tailWord_3071189).sum := by decide
  have hdescent : baseEnd_3071189 < baseStart_3071189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071212 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 5]
def baseStart_3071212 : Nat := 118140960795 + 3071212 * 2 ^ 59
def prefixEnd_3071212 : Nat := 4983230072969 + 3 ^ 40 * 3071212 * 2
def baseEnd_3071212 : Nat := 1577007947856343102625759

theorem tailTrace_3071212 : CollatzResearch.WordTrace tailWord_3071212 prefixEnd_3071212 1577007947856343102625759 := by
  unfold tailWord_3071212
  simp only [CollatzResearch.WordTrace]
  refine ⟨56008152074765460047719945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74677536099687280063626593 56008152074765460047719945)
  ·
    refine ⟨42006114056074095035789959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56008152074765460047719945 42006114056074095035789959)
    ·
      refine ⟨63009171084111142553684939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42006114056074095035789959 63009171084111142553684939)
      ·
        refine ⟨94513756626166713830527409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63009171084111142553684939 94513756626166713830527409)
        ·
          refine ⟨70885317469625035372895557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94513756626166713830527409 70885317469625035372895557)
          ·
            refine ⟨13290997025554694132417917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70885317469625035372895557 13290997025554694132417917)
            ·
              refine ⟨4984123884583010299656719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13290997025554694132417917 4984123884583010299656719)
              ·
                refine ⟨7476185826874515449485079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4984123884583010299656719 7476185826874515449485079)
                ·
                  refine ⟨11214278740311773174227619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7476185826874515449485079 11214278740311773174227619)
                  ·
                    refine ⟨16821418110467659761341429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11214278740311773174227619 16821418110467659761341429)
                    ·
                      refine ⟨1577007947856343102625759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16821418110467659761341429 1577007947856343102625759)
                      ·
                        rfl

theorem cell23_3071212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_3071212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071212 prefixEnd_3071212 := by exact prefixLift 3071212
  have htrace : WordTrace (prefixWord ++ tailWord_3071212) baseStart_3071212 baseEnd_3071212 := by
    simpa [prefixWord, tailWord_3071212, baseEnd_3071212] using wordTrace_append hprefix tailTrace_3071212
  have hstable : (prefixWord ++ tailWord_3071212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071212).length < 2 ^ (prefixWord ++ tailWord_3071212).sum := by decide
  have hdescent : baseEnd_3071212 < baseStart_3071212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071215 : List Nat := [1, 1, 2, 1, 7, 11]
def baseStart_3071215 : Nat := 118140960795 + 3071215 * 2 ^ 59
def prefixEnd_3071215 : Nat := 4983230072969 + 3 ^ 40 * 3071215 * 2
def baseEnd_3071215 : Nat := 6489750980651467452215

theorem tailTrace_3071215 : CollatzResearch.WordTrace tailWord_3071215 prefixEnd_3071215 6489750980651467452215 := by
  unfold tailWord_3071215
  simp only [CollatzResearch.WordTrace]
  refine ⟨112016413568520051607799099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74677609045680034405199399 112016413568520051607799099)
  ·
    refine ⟨168024620352780077411698649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112016413568520051607799099 168024620352780077411698649)
    ·
      refine ⟨126018465264585058058773987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168024620352780077411698649 126018465264585058058773987)
      ·
        refine ⟨189027697896877587088160981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126018465264585058058773987 189027697896877587088160981)
        ·
          refine ⟨4430336669458068447378773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 189027697896877587088160981 4430336669458068447378773)
          ·
            refine ⟨6489750980651467452215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4430336669458068447378773 6489750980651467452215)
            ·
              rfl

theorem cell23_3071215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 11].length) (baseStart_3071215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071215 prefixEnd_3071215 := by exact prefixLift 3071215
  have htrace : WordTrace (prefixWord ++ tailWord_3071215) baseStart_3071215 baseEnd_3071215 := by
    simpa [prefixWord, tailWord_3071215, baseEnd_3071215] using wordTrace_append hprefix tailTrace_3071215
  have hstable : (prefixWord ++ tailWord_3071215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071215).length < 2 ^ (prefixWord ++ tailWord_3071215).sum := by decide
  have hdescent : baseEnd_3071215 < baseStart_3071215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071219 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 2, 4]
def baseStart_3071219 : Nat := 118140960795 + 3071219 * 2 ^ 59
def prefixEnd_3071219 : Nat := 4983230072969 + 3 ^ 40 * 3071219 * 2
def baseEnd_3071219 : Nat := 525670514073641525079409

theorem tailTrace_3071219 : CollatzResearch.WordTrace tailWord_3071219 prefixEnd_3071219 525670514073641525079409 := by
  unfold tailWord_3071219
  simp only [CollatzResearch.WordTrace]
  refine ⟨112016559460505560290944711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74677706307003706860629807 112016559460505560290944711)
  ·
    refine ⟨168024839190758340436417067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112016559460505560290944711 168024839190758340436417067)
    ·
      refine ⟨252037258786137510654625601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168024839190758340436417067 252037258786137510654625601)
      ·
        refine ⟨189027944089603132990969201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252037258786137510654625601 189027944089603132990969201)
        ·
          refine ⟨141770958067202349743226901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189027944089603132990969201 141770958067202349743226901)
          ·
            refine ⟨6645513659400110144213761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141770958067202349743226901 6645513659400110144213761)
            ·
              refine ⟨4984135244550082608160321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6645513659400110144213761 4984135244550082608160321)
              ·
                refine ⟨3738101433412561956120241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4984135244550082608160321 3738101433412561956120241)
                ·
                  refine ⟨2803576075059421467090181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3738101433412561956120241 2803576075059421467090181)
                  ·
                    refine ⟨525670514073641525079409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2803576075059421467090181 525670514073641525079409)
                    ·
                      rfl

theorem cell23_3071219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2, 4].length) (baseStart_3071219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071219 prefixEnd_3071219 := by exact prefixLift 3071219
  have htrace : WordTrace (prefixWord ++ tailWord_3071219) baseStart_3071219 baseEnd_3071219 := by
    simpa [prefixWord, tailWord_3071219, baseEnd_3071219] using wordTrace_append hprefix tailTrace_3071219
  have hstable : (prefixWord ++ tailWord_3071219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071219).length < 2 ^ (prefixWord ++ tailWord_3071219).sum := by decide
  have hdescent : baseEnd_3071219 < baseStart_3071219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071222 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_3071222 : Nat := 118140960795 + 3071222 * 2 ^ 59
def prefixEnd_3071222 : Nat := 4983230072969 + 3 ^ 40 * 3071222 * 2
def baseEnd_3071222 : Nat := 1577013082662888063500713

theorem tailTrace_3071222 : CollatzResearch.WordTrace tailWord_3071222 prefixEnd_3071222 1577013082662888063500713 := by
  unfold tailWord_3071222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001041804968418237706495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74677779252996461202202613 7001041804968418237706495)
  ·
    refine ⟨10501562707452627356559743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7001041804968418237706495 10501562707452627356559743)
    ·
      refine ⟨15752344061178941034839615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10501562707452627356559743 15752344061178941034839615)
      ·
        refine ⟨23628516091768411552259423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15752344061178941034839615 23628516091768411552259423)
        ·
          refine ⟨35442774137652617328389135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23628516091768411552259423 35442774137652617328389135)
          ·
            refine ⟨53164161206478925992583703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35442774137652617328389135 53164161206478925992583703)
            ·
              refine ⟨79746241809718388988875555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53164161206478925992583703 79746241809718388988875555)
              ·
                refine ⟨119619362714577583483313333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79746241809718388988875555 119619362714577583483313333)
                ·
                  refine ⟨11214315254491648451560625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119619362714577583483313333 11214315254491648451560625)
                  ·
                    refine ⟨8410736440868736338670469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11214315254491648451560625 8410736440868736338670469)
                    ·
                      refine ⟨1577013082662888063500713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8410736440868736338670469 1577013082662888063500713)
                      ·
                        rfl

theorem cell23_3071222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_3071222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071222 prefixEnd_3071222 := by exact prefixLift 3071222
  have htrace : WordTrace (prefixWord ++ tailWord_3071222) baseStart_3071222 baseEnd_3071222 := by
    simpa [prefixWord, tailWord_3071222, baseEnd_3071222] using wordTrace_append hprefix tailTrace_3071222
  have hstable : (prefixWord ++ tailWord_3071222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071222).length < 2 ^ (prefixWord ++ tailWord_3071222).sum := by decide
  have hdescent : baseEnd_3071222 < baseStart_3071222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071263 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 1, 2, 3]
def baseStart_3071263 : Nat := 118140960795 + 3071263 * 2 ^ 59
def prefixEnd_3071263 : Nat := 4983230072969 + 3 ^ 40 * 3071263 * 2
def baseEnd_3071263 : Nat := 1577034135369722403088025

theorem tailTrace_3071263 : CollatzResearch.WordTrace tailWord_3071263 prefixEnd_3071263 1577034135369722403088025 := by
  unfold tailWord_3071263
  simp only [CollatzResearch.WordTrace]
  refine ⟨112018164272346155805546443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74678776181564103870364295 112018164272346155805546443)
  ·
    refine ⟨168027246408519233708319665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112018164272346155805546443 168027246408519233708319665)
    ·
      refine ⟨126020434806389425281239749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168027246408519233708319665 126020434806389425281239749)
      ·
        refine ⟨23628831526198017240232453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126020434806389425281239749 23628831526198017240232453)
        ·
          refine ⟨4430405911162128232543585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23628831526198017240232453 4430405911162128232543585)
          ·
            refine ⟨3322804433371596174407689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4430405911162128232543585 3322804433371596174407689)
            ·
              refine ⟨2492103325028697130805767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3322804433371596174407689 2492103325028697130805767)
              ·
                refine ⟨3738154987543045696208651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492103325028697130805767 3738154987543045696208651)
                ·
                  refine ⟨5607232481314568544312977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738154987543045696208651 5607232481314568544312977)
                  ·
                    refine ⟨4205424360985926408234733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5607232481314568544312977 4205424360985926408234733)
                    ·
                      refine ⟨1577034135369722403088025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4205424360985926408234733 1577034135369722403088025)
                      ·
                        rfl

theorem cell23_3071263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_3071263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071263 prefixEnd_3071263 := by exact prefixLift 3071263
  have htrace : WordTrace (prefixWord ++ tailWord_3071263) baseStart_3071263 baseEnd_3071263 := by
    simpa [prefixWord, tailWord_3071263, baseEnd_3071263] using wordTrace_append hprefix tailTrace_3071263
  have hstable : (prefixWord ++ tailWord_3071263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071263).length < 2 ^ (prefixWord ++ tailWord_3071263).sum := by decide
  have hdescent : baseEnd_3071263 < baseStart_3071263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071292 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 2, 6]
def baseStart_3071292 : Nat := 118140960795 + 3071292 * 2 ^ 59
def prefixEnd_3071292 : Nat := 4983230072969 + 3 ^ 40 * 3071292 * 2
def baseEnd_3071292 : Nat := 525683008769567596541797

theorem tailTrace_3071292 : CollatzResearch.WordTrace tailWord_3071292 prefixEnd_3071292 525683008769567596541797 := by
  unfold tailWord_3071292
  simp only [CollatzResearch.WordTrace]
  refine ⟨56009610994620546879176065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74679481326160729172234753 56009610994620546879176065)
  ·
    refine ⟨42007208245965410159382049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56009610994620546879176065 42007208245965410159382049)
    ·
      refine ⟨31505406184474057619536537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42007208245965410159382049 31505406184474057619536537)
      ·
        refine ⟨23629054638355543214652403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31505406184474057619536537 23629054638355543214652403)
        ·
          refine ⟨35443581957533314821978605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23629054638355543214652403 35443581957533314821978605)
          ·
            refine ⟨13291343234074993058241977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35443581957533314821978605 13291343234074993058241977)
            ·
              refine ⟨9968507425556244793681483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13291343234074993058241977 9968507425556244793681483)
              ·
                refine ⟨14952761138334367190522225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9968507425556244793681483 14952761138334367190522225)
                ·
                  refine ⟨11214570853750775392891669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14952761138334367190522225 11214570853750775392891669)
                  ·
                    refine ⟨525683008769567596541797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11214570853750775392891669 525683008769567596541797)
                    ·
                      rfl

theorem cell23_3071292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_3071292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071292 prefixEnd_3071292 := by exact prefixLift 3071292
  have htrace : WordTrace (prefixWord ++ tailWord_3071292) baseStart_3071292 baseEnd_3071292 := by
    simpa [prefixWord, tailWord_3071292, baseEnd_3071292] using wordTrace_append hprefix tailTrace_3071292
  have hstable : (prefixWord ++ tailWord_3071292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071292).length < 2 ^ (prefixWord ++ tailWord_3071292).sum := by decide
  have hdescent : baseEnd_3071292 < baseStart_3071292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071293 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3071293 : Nat := 118140960795 + 3071293 * 2 ^ 59
def prefixEnd_3071293 : Nat := 4983230072969 + 3 ^ 40 * 3071293 * 2
def baseEnd_3071293 : Nat := 1577049539789357285712887

theorem tailTrace_3071293 : CollatzResearch.WordTrace tailWord_3071293 prefixEnd_3071293 1577049539789357285712887 := by
  unfold tailWord_3071293
  simp only [CollatzResearch.WordTrace]
  refine ⟨112019258462237470929138533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74679505641491647286092355 112019258462237470929138533)
  ·
    refine ⟨21003610961669525799213475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112019258462237470929138533 21003610961669525799213475)
    ·
      refine ⟨31505416442504288698820213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21003610961669525799213475 31505416442504288698820213)
      ·
        refine ⟨2953632791484777065514395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31505416442504288698820213 2953632791484777065514395)
        ·
          refine ⟨4430449187227165598271593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2953632791484777065514395 4430449187227165598271593)
          ·
            refine ⟨3322836890420374198703695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4430449187227165598271593 3322836890420374198703695)
            ·
              refine ⟨4984255335630561298055543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322836890420374198703695 4984255335630561298055543)
              ·
                refine ⟨7476383003445841947083315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4984255335630561298055543 7476383003445841947083315)
                ·
                  refine ⟨11214574505168762920624973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7476383003445841947083315 11214574505168762920624973)
                  ·
                    refine ⟨4205465439438286095234365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11214574505168762920624973 4205465439438286095234365)
                    ·
                      refine ⟨1577049539789357285712887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4205465439438286095234365 1577049539789357285712887)
                      ·
                        rfl

theorem cell23_3071293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3071293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071293 prefixEnd_3071293 := by exact prefixLift 3071293
  have htrace : WordTrace (prefixWord ++ tailWord_3071293) baseStart_3071293 baseEnd_3071293 := by
    simpa [prefixWord, tailWord_3071293, baseEnd_3071293] using wordTrace_append hprefix tailTrace_3071293
  have hstable : (prefixWord ++ tailWord_3071293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071293).length < 2 ^ (prefixWord ++ tailWord_3071293).sum := by decide
  have hdescent : baseEnd_3071293 < baseStart_3071293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071316 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_3071316 : Nat := 118140960795 + 3071316 * 2 ^ 59
def prefixEnd_3071316 : Nat := 4983230072969 + 3 ^ 40 * 3071316 * 2
def baseEnd_3071316 : Nat := 1577061349844410695725281

theorem tailTrace_3071316 : CollatzResearch.WordTrace tailWord_3071316 prefixEnd_3071316 1577061349844410695725281 := by
  unfold tailWord_3071316
  simp only [CollatzResearch.WordTrace]
  refine ⟨56010048670577072928612901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74680064894102763904817201 56010048670577072928612901)
  ·
    refine ⟨10501884125733201174114919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56010048670577072928612901 10501884125733201174114919)
    ·
      refine ⟨15752826188599801761172379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10501884125733201174114919 15752826188599801761172379)
      ·
        refine ⟨23629239282899702641758569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15752826188599801761172379 23629239282899702641758569)
        ·
          refine ⟨17721929462174776981318927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23629239282899702641758569 17721929462174776981318927)
          ·
            refine ⟨26582894193262165471978391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17721929462174776981318927 26582894193262165471978391)
            ·
              refine ⟨39874341289893248207967587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26582894193262165471978391 39874341289893248207967587)
              ·
                refine ⟨59811511934839872311951381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39874341289893248207967587 59811511934839872311951381)
                ·
                  refine ⟨2803664621945619014622721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59811511934839872311951381 2803664621945619014622721)
                  ·
                    refine ⟨2102748466459214260967041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2803664621945619014622721 2102748466459214260967041)
                    ·
                      refine ⟨1577061349844410695725281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2102748466459214260967041 1577061349844410695725281)
                      ·
                        rfl

theorem cell23_3071316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_3071316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071316 prefixEnd_3071316 := by exact prefixLift 3071316
  have htrace : WordTrace (prefixWord ++ tailWord_3071316) baseStart_3071316 baseEnd_3071316 := by
    simpa [prefixWord, tailWord_3071316, baseEnd_3071316] using wordTrace_append hprefix tailTrace_3071316
  have hstable : (prefixWord ++ tailWord_3071316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071316).length < 2 ^ (prefixWord ++ tailWord_3071316).sum := by decide
  have hdescent : baseEnd_3071316 < baseStart_3071316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071392 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3071392 : Nat := 118140960795 + 3071392 * 2 ^ 59
def prefixEnd_3071392 : Nat := 4983230072969 + 3 ^ 40 * 3071392 * 2
def baseEnd_3071392 : Nat := 1577100374374152398374931

theorem tailTrace_3071392 : CollatzResearch.WordTrace tailWord_3071392 prefixEnd_3071392 1577100374374152398374931 := by
  unfold tailWord_3071392
  simp only [CollatzResearch.WordTrace]
  refine ⟨56011434644439405418496215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74681912859252540557994953 56011434644439405418496215)
  ·
    refine ⟨84017151966659108127744323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56011434644439405418496215 84017151966659108127744323)
    ·
      refine ⟨126025727949988662191616485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84017151966659108127744323 126025727949988662191616485)
      ·
        refine ⟨23629823990622874160928091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126025727949988662191616485 23629823990622874160928091)
        ·
          refine ⟨35444735985934311241392137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23629823990622874160928091 35444735985934311241392137)
          ·
            refine ⟨26583551989450733431044103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35444735985934311241392137 26583551989450733431044103)
            ·
              refine ⟨39875327984176100146566155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26583551989450733431044103 39875327984176100146566155)
              ·
                refine ⟨59812991976264150219849233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39875327984176100146566155 59812991976264150219849233)
                ·
                  refine ⟨44859743982198112664886925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59812991976264150219849233 44859743982198112664886925)
                  ·
                    refine ⟨16822403993324292249332597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44859743982198112664886925 16822403993324292249332597)
                    ·
                      refine ⟨1577100374374152398374931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16822403993324292249332597 1577100374374152398374931)
                      ·
                        rfl

theorem cell23_3071392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3071392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071392 prefixEnd_3071392 := by exact prefixLift 3071392
  have htrace : WordTrace (prefixWord ++ tailWord_3071392) baseStart_3071392 baseEnd_3071392 := by
    simpa [prefixWord, tailWord_3071392, baseEnd_3071392] using wordTrace_append hprefix tailTrace_3071392
  have hstable : (prefixWord ++ tailWord_3071392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071392).length < 2 ^ (prefixWord ++ tailWord_3071392).sum := by decide
  have hdescent : baseEnd_3071392 < baseStart_3071392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071409 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 1, 4, 3]
def baseStart_3071409 : Nat := 118140960795 + 3071409 * 2 ^ 59
def prefixEnd_3071409 : Nat := 4983230072969 + 3 ^ 40 * 3071409 * 2
def baseEnd_3071409 : Nat := 1577109103545278831862353

theorem tailTrace_3071409 : CollatzResearch.WordTrace tailWord_3071409 prefixEnd_3071409 1577109103545278831862353 := by
  unfold tailWord_3071409
  simp only [CollatzResearch.WordTrace]
  refine ⟨112023489329817222740361281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74682326219878148493574187 112023489329817222740361281)
  ·
    refine ⟨84017616997362917055270961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112023489329817222740361281 84017616997362917055270961)
    ·
      refine ⟨63013212748022187791453221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84017616997362917055270961 63013212748022187791453221)
      ·
        refine ⟨11814977390254160210897479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63013212748022187791453221 11814977390254160210897479)
        ·
          refine ⟨17722466085381240316346219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11814977390254160210897479 17722466085381240316346219)
          ·
            refine ⟨26583699128071860474519329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17722466085381240316346219 26583699128071860474519329)
            ·
              refine ⟨19937774346053895355889497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26583699128071860474519329 19937774346053895355889497)
              ·
                refine ⟨14953330759540421516917123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19937774346053895355889497 14953330759540421516917123)
                ·
                  refine ⟨22429996139310632275375685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14953330759540421516917123 22429996139310632275375685)
                  ·
                    refine ⟨4205624276120743551632941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22429996139310632275375685 4205624276120743551632941)
                    ·
                      refine ⟨1577109103545278831862353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4205624276120743551632941 1577109103545278831862353)
                      ·
                        rfl

theorem cell23_3071409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_3071409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071409 prefixEnd_3071409 := by exact prefixLift 3071409
  have htrace : WordTrace (prefixWord ++ tailWord_3071409) baseStart_3071409 baseEnd_3071409 := by
    simpa [prefixWord, tailWord_3071409, baseEnd_3071409] using wordTrace_append hprefix tailTrace_3071409
  have hstable : (prefixWord ++ tailWord_3071409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071409).length < 2 ^ (prefixWord ++ tailWord_3071409).sum := by decide
  have hdescent : baseEnd_3071409 < baseStart_3071409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071446 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_3071446 : Nat := 118140960795 + 3071446 * 2 ^ 59
def prefixEnd_3071446 : Nat := 4983230072969 + 3 ^ 40 * 3071446 * 2
def baseEnd_3071446 : Nat := 175236455814388354122187

theorem tailTrace_3071446 : CollatzResearch.WordTrace tailWord_3071446 prefixEnd_3071446 175236455814388354122187 := by
  unfold tailWord_3071446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001552426917698628716137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 74683225887122118706305461 7001552426917698628716137)
  ·
    refine ⟨5251164320188273971537103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7001552426917698628716137 5251164320188273971537103)
    ·
      refine ⟨7876746480282410957305655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251164320188273971537103 7876746480282410957305655)
      ·
        refine ⟨11815119720423616435958483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7876746480282410957305655 11815119720423616435958483)
        ·
          refine ⟨17722679580635424653937725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11815119720423616435958483 17722679580635424653937725)
          ·
            refine ⟨6646004842738284245226647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17722679580635424653937725 6646004842738284245226647)
            ·
              refine ⟨9969007264107426367839971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6646004842738284245226647 9969007264107426367839971)
              ·
                refine ⟨14953510896161139551759957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9969007264107426367839971 14953510896161139551759957)
                ·
                  refine ⟨175236455814388354122187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14953510896161139551759957 175236455814388354122187)
                  ·
                    rfl

theorem cell23_3071446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_3071446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071446 prefixEnd_3071446 := by exact prefixLift 3071446
  have htrace : WordTrace (prefixWord ++ tailWord_3071446) baseStart_3071446 baseEnd_3071446 := by
    simpa [prefixWord, tailWord_3071446, baseEnd_3071446] using wordTrace_append hprefix tailTrace_3071446
  have hstable : (prefixWord ++ tailWord_3071446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071446).length < 2 ^ (prefixWord ++ tailWord_3071446).sum := by decide
  have hdescent : baseEnd_3071446 < baseStart_3071446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071496 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_3071496 : Nat := 118140960795 + 3071496 * 2 ^ 59
def prefixEnd_3071496 : Nat := 4983230072969 + 3 ^ 40 * 3071496 * 2
def baseEnd_3071496 : Nat := 1577153776362219991474453

theorem tailTrace_3071496 : CollatzResearch.WordTrace tailWord_3071496 prefixEnd_3071496 1577153776362219991474453 := by
  unfold tailWord_3071496
  simp only [CollatzResearch.WordTrace]
  refine ⟨56013331240251018299389171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74684441653668024399185561 56013331240251018299389171)
  ·
    refine ⟨84019996860376527449083757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56013331240251018299389171 84019996860376527449083757)
    ·
      refine ⟨31507498822641197793406409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84019996860376527449083757 31507498822641197793406409)
      ·
        refine ⟨23630624116980898345054807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31507498822641197793406409 23630624116980898345054807)
        ·
          refine ⟨35445936175471347517582211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23630624116980898345054807 35445936175471347517582211)
          ·
            refine ⟨53168904263207021276373317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35445936175471347517582211 53168904263207021276373317)
            ·
              refine ⟨9969169549351316489319997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53168904263207021276373317 9969169549351316489319997)
              ·
                refine ⟨3738438581006743683494999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9969169549351316489319997 3738438581006743683494999)
                ·
                  refine ⟨5607657871510115525242499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738438581006743683494999 5607657871510115525242499)
                  ·
                    refine ⟨8411486807265173287863749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5607657871510115525242499 8411486807265173287863749)
                    ·
                      refine ⟨1577153776362219991474453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8411486807265173287863749 1577153776362219991474453)
                      ·
                        rfl

theorem cell23_3071496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_3071496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071496 prefixEnd_3071496 := by exact prefixLift 3071496
  have htrace : WordTrace (prefixWord ++ tailWord_3071496) baseStart_3071496 baseEnd_3071496 := by
    simpa [prefixWord, tailWord_3071496, baseEnd_3071496] using wordTrace_append hprefix tailTrace_3071496
  have hstable : (prefixWord ++ tailWord_3071496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071496).length < 2 ^ (prefixWord ++ tailWord_3071496).sum := by decide
  have hdescent : baseEnd_3071496 < baseStart_3071496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071509 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_3071509 : Nat := 118140960795 + 3071509 * 2 ^ 59
def prefixEnd_3071509 : Nat := 4983230072969 + 3 ^ 40 * 3071509 * 2
def baseEnd_3071509 : Nat := 1577160451610728440611893

theorem tailTrace_3071509 : CollatzResearch.WordTrace tailWord_3071509 prefixEnd_3071509 1577160451610728440611893 := by
  unfold tailWord_3071509
  simp only [CollatzResearch.WordTrace]
  refine ⟨112027136629454939819001581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74684757752969959879334387 112027136629454939819001581)
  ·
    refine ⟨42010176236045602432125593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112027136629454939819001581 42010176236045602432125593)
    ·
      refine ⟨31507632177034201824094195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42010176236045602432125593 31507632177034201824094195)
      ·
        refine ⟨47261448265551302736141293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31507632177034201824094195 47261448265551302736141293)
        ·
          refine ⟨17723043099581738526052985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47261448265551302736141293 17723043099581738526052985)
          ·
            refine ⟨13292282324686303894539739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17723043099581738526052985 13292282324686303894539739)
            ·
              refine ⟨19938423487029455841809609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13292282324686303894539739 19938423487029455841809609)
              ·
                refine ⟨14953817615272091881357207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19938423487029455841809609 14953817615272091881357207)
                ·
                  refine ⟨22430726422908137822035811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14953817615272091881357207 22430726422908137822035811)
                  ·
                    refine ⟨33646089634362206733053717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22430726422908137822035811 33646089634362206733053717)
                    ·
                      refine ⟨1577160451610728440611893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33646089634362206733053717 1577160451610728440611893)
                      ·
                        rfl

theorem cell23_3071509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_3071509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071509 prefixEnd_3071509 := by exact prefixLift 3071509
  have htrace : WordTrace (prefixWord ++ tailWord_3071509) baseStart_3071509 baseEnd_3071509 := by
    simpa [prefixWord, tailWord_3071509, baseEnd_3071509] using wordTrace_append hprefix tailTrace_3071509
  have hstable : (prefixWord ++ tailWord_3071509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071509).length < 2 ^ (prefixWord ++ tailWord_3071509).sum := by decide
  have hdescent : baseEnd_3071509 < baseStart_3071509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071516 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_3071516 : Nat := 118140960795 + 3071516 * 2 ^ 59
def prefixEnd_3071516 : Nat := 4983230072969 + 3 ^ 40 * 3071516 * 2
def baseEnd_3071516 : Nat := 1577164045975309913224361

theorem tailTrace_3071516 : CollatzResearch.WordTrace tailWord_3071516 prefixEnd_3071516 1577164045975309913224361 := by
  unfold tailWord_3071516
  simp only [CollatzResearch.WordTrace]
  refine ⟨56013695970214790007253201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74684927960286386676337601 56013695970214790007253201)
  ·
    refine ⟨42010271977661092505439901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56013695970214790007253201 42010271977661092505439901)
    ·
      refine ⟨15753851991622909689539963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42010271977661092505439901 15753851991622909689539963)
      ·
        refine ⟨23630777987434364534309945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15753851991622909689539963 23630777987434364534309945)
        ·
          refine ⟨17723083490575773400732459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23630777987434364534309945 17723083490575773400732459)
          ·
            refine ⟨26584625235863660101098689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17723083490575773400732459 26584625235863660101098689)
            ·
              refine ⟨19938468926897745075824017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26584625235863660101098689 19938468926897745075824017)
              ·
                refine ⟨14953851695173308806868013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19938468926897745075824017 14953851695173308806868013)
                ·
                  refine ⟨5607694385689990802575505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14953851695173308806868013 5607694385689990802575505)
                  ·
                    refine ⟨4205770789267493101931629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5607694385689990802575505 4205770789267493101931629)
                    ·
                      refine ⟨1577164045975309913224361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4205770789267493101931629 1577164045975309913224361)
                      ·
                        rfl

theorem cell23_3071516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_3071516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071516 prefixEnd_3071516 := by exact prefixLift 3071516
  have htrace : WordTrace (prefixWord ++ tailWord_3071516) baseStart_3071516 baseEnd_3071516 := by
    simpa [prefixWord, tailWord_3071516, baseEnd_3071516] using wordTrace_append hprefix tailTrace_3071516
  have hstable : (prefixWord ++ tailWord_3071516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071516).length < 2 ^ (prefixWord ++ tailWord_3071516).sum := by decide
  have hdescent : baseEnd_3071516 < baseStart_3071516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071523 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 2, 4]
def baseStart_3071523 : Nat := 118140960795 + 3071523 * 2 ^ 59
def prefixEnd_3071523 : Nat := 4983230072969 + 3 ^ 40 * 3071523 * 2
def baseEnd_3071523 : Nat := 525722546779963795278943

theorem tailTrace_3071523 : CollatzResearch.WordTrace tailWord_3071523 prefixEnd_3071523 525722546779963795278943 := by
  unfold tailWord_3071523
  simp only [CollatzResearch.WordTrace]
  refine ⟨112027647251404220210011223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74685098167602813473340815 112027647251404220210011223)
  ·
    refine ⟨168041470877106330315016835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112027647251404220210011223 168041470877106330315016835)
    ·
      refine ⟨252062206315659495472525253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168041470877106330315016835 252062206315659495472525253)
      ·
        refine ⟨47261663684186155401098485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252062206315659495472525253 47261663684186155401098485)
        ·
          refine ⟨4430780970392452068852983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47261663684186155401098485 4430780970392452068852983)
          ·
            refine ⟨6646171455588678103279475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4430780970392452068852983 6646171455588678103279475)
            ·
              refine ⟨9969257183383017154919213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6646171455588678103279475 9969257183383017154919213)
              ·
                refine ⟨3738471443768631433094705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9969257183383017154919213 3738471443768631433094705)
                ·
                  refine ⟨2803853582826473574821029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3738471443768631433094705 2803853582826473574821029)
                  ·
                    refine ⟨525722546779963795278943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2803853582826473574821029 525722546779963795278943)
                    ·
                      rfl

theorem cell23_3071523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 4].length) (baseStart_3071523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071523 prefixEnd_3071523 := by exact prefixLift 3071523
  have htrace : WordTrace (prefixWord ++ tailWord_3071523) baseStart_3071523 baseEnd_3071523 := by
    simpa [prefixWord, tailWord_3071523, baseEnd_3071523] using wordTrace_append hprefix tailTrace_3071523
  have hstable : (prefixWord ++ tailWord_3071523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071523).length < 2 ^ (prefixWord ++ tailWord_3071523).sum := by decide
  have hdescent : baseEnd_3071523 < baseStart_3071523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071546 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3]
def baseStart_3071546 : Nat := 118140960795 + 3071546 * 2 ^ 59
def prefixEnd_3071546 : Nat := 4983230072969 + 3 ^ 40 * 3071546 * 2
def baseEnd_3071546 : Nat := 1577179450394944795849223

theorem tailTrace_3071546 : CollatzResearch.WordTrace tailWord_3071546 prefixEnd_3071546 1577179450394944795849223 := by
  unfold tailWord_3071546
  simp only [CollatzResearch.WordTrace]
  refine ⟨28007121532580223784524623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74685657420213930092065661 28007121532580223784524623)
  ·
    refine ⟨42010682298870335676786935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28007121532580223784524623 42010682298870335676786935)
    ·
      refine ⟨63016023448305503515180403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42010682298870335676786935 63016023448305503515180403)
      ·
        refine ⟨94524035172458255272770605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63016023448305503515180403 94524035172458255272770605)
        ·
          refine ⟨35446513189671845727288977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94524035172458255272770605 35446513189671845727288977)
          ·
            refine ⟨26584884892253884295466733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35446513189671845727288977 26584884892253884295466733)
            ·
              refine ⟨9969331834595206610800025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26584884892253884295466733 9969331834595206610800025)
              ·
                refine ⟨7476998875946404958100019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9969331834595206610800025 7476998875946404958100019)
                ·
                  refine ⟨11215498313919607437150029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7476998875946404958100019 11215498313919607437150029)
                  ·
                    refine ⟨4205811867719852788931261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11215498313919607437150029 4205811867719852788931261)
                    ·
                      refine ⟨1577179450394944795849223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4205811867719852788931261 1577179450394944795849223)
                      ·
                        rfl

theorem cell23_3071546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_3071546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071546 prefixEnd_3071546 := by exact prefixLift 3071546
  have htrace : WordTrace (prefixWord ++ tailWord_3071546) baseStart_3071546 baseEnd_3071546 := by
    simpa [prefixWord, tailWord_3071546, baseEnd_3071546] using wordTrace_append hprefix tailTrace_3071546
  have hstable : (prefixWord ++ tailWord_3071546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071546).length < 2 ^ (prefixWord ++ tailWord_3071546).sum := by decide
  have hdescent : baseEnd_3071546 < baseStart_3071546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071558 : List Nat := [6, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_3071558 : Nat := 118140960795 + 3071558 * 2 ^ 59
def prefixEnd_3071558 : Nat := 4983230072969 + 3 ^ 40 * 3071558 * 2
def baseEnd_3071558 : Nat := 1577185612162798748899169

theorem tailTrace_3071558 : CollatzResearch.WordTrace tailWord_3071558 prefixEnd_3071558 1577185612162798748899169 := by
  unfold tailWord_3071558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500903868946169412110479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74685949204184947458356885 3500903868946169412110479)
  ·
    refine ⟨5251355803419254118165719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3500903868946169412110479 5251355803419254118165719)
    ·
      refine ⟨7877033705128881177248579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251355803419254118165719 7877033705128881177248579)
      ·
        refine ⟨11815550557693321765872869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7877033705128881177248579 11815550557693321765872869)
        ·
          refine ⟨2215415729567497831101163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11815550557693321765872869 2215415729567497831101163)
          ·
            refine ⟨3323123594351246746651745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215415729567497831101163 3323123594351246746651745)
            ·
              refine ⟨2492342695763435059988809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3323123594351246746651745 2492342695763435059988809)
              ·
                refine ⟨1869257021822576294991607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2492342695763435059988809 1869257021822576294991607)
                ·
                  refine ⟨2803885532733864442487411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869257021822576294991607 2803885532733864442487411)
                  ·
                    refine ⟨4205828299100796663731117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2803885532733864442487411 4205828299100796663731117)
                    ·
                      refine ⟨1577185612162798748899169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4205828299100796663731117 1577185612162798748899169)
                      ·
                        rfl

theorem cell23_3071558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_3071558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071558 prefixEnd_3071558 := by exact prefixLift 3071558
  have htrace : WordTrace (prefixWord ++ tailWord_3071558) baseStart_3071558 baseEnd_3071558 := by
    simpa [prefixWord, tailWord_3071558, baseEnd_3071558] using wordTrace_append hprefix tailTrace_3071558
  have hstable : (prefixWord ++ tailWord_3071558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071558).length < 2 ^ (prefixWord ++ tailWord_3071558).sum := by decide
  have hdescent : baseEnd_3071558 < baseStart_3071558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071564 : List Nat := [2, 2, 1, 3, 1, 5, 2, 2, 1, 2, 2]
def baseStart_3071564 : Nat := 118140960795 + 3071564 * 2 ^ 59
def prefixEnd_3071564 : Nat := 4983230072969 + 3 ^ 40 * 3071564 * 2
def baseEnd_3071564 : Nat := 1577188693046725725424141

theorem tailTrace_3071564 : CollatzResearch.WordTrace tailWord_3071564 prefixEnd_3071564 1577188693046725725424141 := by
  unfold tailWord_3071564
  simp only [CollatzResearch.WordTrace]
  refine ⟨56014571322127842106126873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74686095096170456141502497 56014571322127842106126873)
  ·
    refine ⟨42010928491595881579595155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56014571322127842106126873 42010928491595881579595155)
    ·
      refine ⟨63016392737393822369392733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42010928491595881579595155 63016392737393822369392733)
      ·
        refine ⟨23631147276522683388522275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63016392737393822369392733 23631147276522683388522275)
        ·
          refine ⟨35446720914784025082783413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23631147276522683388522275 35446720914784025082783413)
          ·
            refine ⟨3323130085761002351510945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35446720914784025082783413 3323130085761002351510945)
            ·
              refine ⟨2492347564320751763633209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3323130085761002351510945 2492347564320751763633209)
              ·
                refine ⟨1869260673240563822724907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2492347564320751763633209 1869260673240563822724907)
                ·
                  refine ⟨2803891009860845734087361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869260673240563822724907 2803891009860845734087361)
                  ·
                    refine ⟨2102918257395634300565521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2803891009860845734087361 2102918257395634300565521)
                    ·
                      refine ⟨1577188693046725725424141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2102918257395634300565521 1577188693046725725424141)
                      ·
                        rfl

theorem cell23_3071564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_3071564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071564 prefixEnd_3071564 := by exact prefixLift 3071564
  have htrace : WordTrace (prefixWord ++ tailWord_3071564) baseStart_3071564 baseEnd_3071564 := by
    simpa [prefixWord, tailWord_3071564, baseEnd_3071564] using wordTrace_append hprefix tailTrace_3071564
  have hstable : (prefixWord ++ tailWord_3071564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071564).length < 2 ^ (prefixWord ++ tailWord_3071564).sum := by decide
  have hdescent : baseEnd_3071564 < baseStart_3071564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071569 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_3071569 : Nat := 118140960795 + 3071569 * 2 ^ 59
def prefixEnd_3071569 : Nat := 4983230072969 + 3 ^ 40 * 3071569 * 2
def baseEnd_3071569 : Nat := 1577191260449998205861617

theorem tailTrace_3071569 : CollatzResearch.WordTrace tailWord_3071569 prefixEnd_3071569 1577191260449998205861617 := by
  unfold tailWord_3071569
  simp only [CollatzResearch.WordTrace]
  refine ⟨112029325009237570066185761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74686216672825046710790507 112029325009237570066185761)
  ·
    refine ⟨84021993756928177549639321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112029325009237570066185761 84021993756928177549639321)
    ·
      refine ⟨63016495317696133162229491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84021993756928177549639321 63016495317696133162229491)
      ·
        refine ⟨94524742976544199743344237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63016495317696133162229491 94524742976544199743344237)
        ·
          refine ⟨35446778616204074903754089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94524742976544199743344237 35446778616204074903754089)
          ·
            refine ⟨26585083962153056177815567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35446778616204074903754089 26585083962153056177815567)
            ·
              refine ⟨39877625943229584266723351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26585083962153056177815567 39877625943229584266723351)
              ·
                refine ⟨59816438914844376400085027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39877625943229584266723351 59816438914844376400085027)
                ·
                  refine ⟨89724658372266564600127541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59816438914844376400085027 89724658372266564600127541)
                  ·
                    refine ⟨8411686722399990431261957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89724658372266564600127541 8411686722399990431261957)
                    ·
                      refine ⟨1577191260449998205861617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8411686722399990431261957 1577191260449998205861617)
                      ·
                        rfl

theorem cell23_3071569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_3071569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071569 prefixEnd_3071569 := by exact prefixLift 3071569
  have htrace : WordTrace (prefixWord ++ tailWord_3071569) baseStart_3071569 baseEnd_3071569 := by
    simpa [prefixWord, tailWord_3071569, baseEnd_3071569] using wordTrace_append hprefix tailTrace_3071569
  have hstable : (prefixWord ++ tailWord_3071569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071569).length < 2 ^ (prefixWord ++ tailWord_3071569).sum := by decide
  have hdescent : baseEnd_3071569 < baseStart_3071569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071580 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_3071580 : Nat := 118140960795 + 3071580 * 2 ^ 59
def prefixEnd_3071580 : Nat := 4983230072969 + 3 ^ 40 * 3071580 * 2
def baseEnd_3071580 : Nat := 1577196908737197662824067

theorem tailTrace_3071580 : CollatzResearch.WordTrace tailWord_3071580 prefixEnd_3071580 1577196908737197662824067 := by
  unfold tailWord_3071580
  simp only [CollatzResearch.WordTrace]
  refine ⟨56014863106098859472418097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74686484141465145963224129 56014863106098859472418097)
  ·
    refine ⟨42011147329574144604313573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56014863106098859472418097 42011147329574144604313573)
    ·
      refine ⟨7877090124295152113308795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42011147329574144604313573 7877090124295152113308795)
      ·
        refine ⟨11815635186442728169963193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7877090124295152113308795 11815635186442728169963193)
        ·
          refine ⟨8861726389832046127472395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11815635186442728169963193 8861726389832046127472395)
          ·
            refine ⟨13292589584748069191208593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8861726389832046127472395 13292589584748069191208593)
            ·
              refine ⟨9969442188561051893406445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13292589584748069191208593 9969442188561051893406445)
              ·
                refine ⟨3738540820710394460027417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9969442188561051893406445 3738540820710394460027417)
                ·
                  refine ⟨2803905615532795845020563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3738540820710394460027417 2803905615532795845020563)
                  ·
                    refine ⟨4205858423299193767530845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2803905615532795845020563 4205858423299193767530845)
                    ·
                      refine ⟨1577196908737197662824067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4205858423299193767530845 1577196908737197662824067)
                      ·
                        rfl

theorem cell23_3071580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_3071580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071580 prefixEnd_3071580 := by exact prefixLift 3071580
  have htrace : WordTrace (prefixWord ++ tailWord_3071580) baseStart_3071580 baseEnd_3071580 := by
    simpa [prefixWord, tailWord_3071580, baseEnd_3071580] using wordTrace_append hprefix tailTrace_3071580
  have hstable : (prefixWord ++ tailWord_3071580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071580).length < 2 ^ (prefixWord ++ tailWord_3071580).sum := by decide
  have hdescent : baseEnd_3071580 < baseStart_3071580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071599 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 4]
def baseStart_3071599 : Nat := 118140960795 + 3071599 * 2 ^ 59
def prefixEnd_3071599 : Nat := 4983230072969 + 3 ^ 40 * 3071599 * 2
def baseEnd_3071599 : Nat := 1577206664869633088486479

theorem tailTrace_3071599 : CollatzResearch.WordTrace tailWord_3071599 prefixEnd_3071599 1577206664869633088486479 := by
  unfold tailWord_3071599
  simp only [CollatzResearch.WordTrace]
  refine ⟨112030419199128885189777851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74686946132752590126518567 112030419199128885189777851)
  ·
    refine ⟨168045628798693327784666777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112030419199128885189777851 168045628798693327784666777)
    ·
      refine ⟨126034221599019995838500083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168045628798693327784666777 126034221599019995838500083)
      ·
        refine ⟨189051332398529993757750125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126034221599019995838500083 189051332398529993757750125)
        ·
          refine ⟨70894249649448747659156297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189051332398529993757750125 70894249649448747659156297)
          ·
            refine ⟨53170687237086560744367223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70894249649448747659156297 53170687237086560744367223)
            ·
              refine ⟨79756030855629841116550835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53170687237086560744367223 79756030855629841116550835)
              ·
                refine ⟨119634046283444761674826253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79756030855629841116550835 119634046283444761674826253)
                ·
                  refine ⟨44862767356291785628059845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119634046283444761674826253 44862767356291785628059845)
                  ·
                    refine ⟨8411768879304709805261221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44862767356291785628059845 8411768879304709805261221)
                    ·
                      refine ⟨1577206664869633088486479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8411768879304709805261221 1577206664869633088486479)
                      ·
                        rfl

theorem cell23_3071599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_3071599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071599 prefixEnd_3071599 := by exact prefixLift 3071599
  have htrace : WordTrace (prefixWord ++ tailWord_3071599) baseStart_3071599 baseEnd_3071599 := by
    simpa [prefixWord, tailWord_3071599, baseEnd_3071599] using wordTrace_append hprefix tailTrace_3071599
  have hstable : (prefixWord ++ tailWord_3071599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071599).length < 2 ^ (prefixWord ++ tailWord_3071599).sum := by decide
  have hdescent : baseEnd_3071599 < baseStart_3071599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071609 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 9]
def baseStart_3071609 : Nat := 118140960795 + 3071609 * 2 ^ 59
def prefixEnd_3071609 : Nat := 4983230072969 + 3 ^ 40 * 3071609 * 2
def baseEnd_3071609 : Nat := 175245755519575338817937

theorem tailTrace_3071609 : CollatzResearch.WordTrace tailWord_3071609 prefixEnd_3071609 175245755519575338817937 := by
  unfold tailWord_3071609
  simp only [CollatzResearch.WordTrace]
  refine ⟨112030783929092656897641881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74687189286061771265094587 112030783929092656897641881)
  ·
    refine ⟨84023087946819492673231411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112030783929092656897641881 84023087946819492673231411)
    ·
      refine ⟨126034631920229239009847117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84023087946819492673231411 126034631920229239009847117)
      ·
        refine ⟨47262986970085964628692669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126034631920229239009847117 47262986970085964628692669)
        ·
          refine ⟨17723620113782236735759751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47262986970085964628692669 17723620113782236735759751)
          ·
            refine ⟨26585430170673355103639627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17723620113782236735759751 26585430170673355103639627)
            ·
              refine ⟨39878145256010032655459441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26585430170673355103639627 39878145256010032655459441)
              ·
                refine ⟨29908608942007524491594581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39878145256010032655459441 29908608942007524491594581)
                ·
                  refine ⟨175245755519575338817937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29908608942007524491594581 175245755519575338817937)
                  ·
                    rfl

theorem cell23_3071609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 9].length) (baseStart_3071609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071609 prefixEnd_3071609 := by exact prefixLift 3071609
  have htrace : WordTrace (prefixWord ++ tailWord_3071609) baseStart_3071609 baseEnd_3071609 := by
    simpa [prefixWord, tailWord_3071609, baseEnd_3071609] using wordTrace_append hprefix tailTrace_3071609
  have hstable : (prefixWord ++ tailWord_3071609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071609).length < 2 ^ (prefixWord ++ tailWord_3071609).sum := by decide
  have hdescent : baseEnd_3071609 < baseStart_3071609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071626 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 7]
def baseStart_3071626 : Nat := 118140960795 + 3071626 * 2 ^ 59
def prefixEnd_3071626 : Nat := 4983230072969 + 3 ^ 40 * 3071626 * 2
def baseEnd_3071626 : Nat := 175246725427478275872095

theorem tailTrace_3071626 : CollatzResearch.WordTrace tailWord_3071626 prefixEnd_3071626 175246725427478275872095 := by
  unfold tailWord_3071626
  simp only [CollatzResearch.WordTrace]
  refine ⟨28007850992507767200252683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74687602646687379200673821 28007850992507767200252683)
  ·
    refine ⟨42011776488761650800379025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28007850992507767200252683 42011776488761650800379025)
    ·
      refine ⟨31508832366571238100284269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42011776488761650800379025 31508832366571238100284269)
      ·
        refine ⟨11815812137464214287606601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31508832366571238100284269 11815812137464214287606601)
        ·
          refine ⟨8861859103098160715704951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11815812137464214287606601 8861859103098160715704951)
          ·
            refine ⟨13292788654647241073557427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8861859103098160715704951 13292788654647241073557427)
            ·
              refine ⟨19939182981970861610336141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13292788654647241073557427 19939182981970861610336141)
              ·
                refine ⟨7477193618239073103876053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19939182981970861610336141 7477193618239073103876053)
                ·
                  refine ⟨175246725427478275872095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7477193618239073103876053 175246725427478275872095)
                  ·
                    rfl

theorem cell23_3071626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_3071626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071626 prefixEnd_3071626 := by exact prefixLift 3071626
  have htrace : WordTrace (prefixWord ++ tailWord_3071626) baseStart_3071626 baseEnd_3071626 := by
    simpa [prefixWord, tailWord_3071626, baseEnd_3071626] using wordTrace_append hprefix tailTrace_3071626
  have hstable : (prefixWord ++ tailWord_3071626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071626).length < 2 ^ (prefixWord ++ tailWord_3071626).sum := by decide
  have hdescent : baseEnd_3071626 < baseStart_3071626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071696 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 3]
def baseStart_3071696 : Nat := 118140960795 + 3071696 * 2 ^ 59
def prefixEnd_3071696 : Nat := 4983230072969 + 3 ^ 40 * 3071696 * 2
def baseEnd_3071696 : Nat := 1577256472493119208973533

theorem tailTrace_3071696 : CollatzResearch.WordTrace tailWord_3071696 prefixEnd_3071696 1577256472493119208973533 := by
  unfold tailWord_3071696
  simp only [CollatzResearch.WordTrace]
  refine ⟨56016978539888735378029471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74689304719851647170705961 56016978539888735378029471)
  ·
    refine ⟨84025467809833103067044207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56016978539888735378029471 84025467809833103067044207)
    ·
      refine ⟨126038201714749654600566311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84025467809833103067044207 126038201714749654600566311)
      ·
        refine ⟨189057302572124481900849467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126038201714749654600566311 189057302572124481900849467)
        ·
          refine ⟨283585953858186722851274201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189057302572124481900849467 283585953858186722851274201)
          ·
            refine ⟨212689465393640042138455651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283585953858186722851274201 212689465393640042138455651)
            ·
              refine ⟨319034198090460063207683477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212689465393640042138455651 319034198090460063207683477)
              ·
                refine ⟨14954728035490315462860163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 319034198090460063207683477 14954728035490315462860163)
                ·
                  refine ⟨22432092053235473194290245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14954728035490315462860163 22432092053235473194290245)
                  ·
                    refine ⟨4206017259981651223929421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22432092053235473194290245 4206017259981651223929421)
                    ·
                      refine ⟨1577256472493119208973533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4206017259981651223929421 1577256472493119208973533)
                      ·
                        rfl

theorem cell23_3071696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 3].length) (baseStart_3071696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071696 prefixEnd_3071696 := by exact prefixLift 3071696
  have htrace : WordTrace (prefixWord ++ tailWord_3071696) baseStart_3071696 baseEnd_3071696 := by
    simpa [prefixWord, tailWord_3071696, baseEnd_3071696] using wordTrace_append hprefix tailTrace_3071696
  have hstable : (prefixWord ++ tailWord_3071696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071696).length < 2 ^ (prefixWord ++ tailWord_3071696).sum := by decide
  have hdescent : baseEnd_3071696 < baseStart_3071696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071753 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 1, 5, 2]
def baseStart_3071753 : Nat := 118140960795 + 3071753 * 2 ^ 59
def prefixEnd_3071753 : Nat := 4983230072969 + 3 ^ 40 * 3071753 * 2
def baseEnd_3071753 : Nat := 1577285740890425485960771

theorem tailTrace_3071753 : CollatzResearch.WordTrace tailWord_3071753 prefixEnd_3071753 1577285740890425485960771 := by
  unfold tailWord_3071753
  simp only [CollatzResearch.WordTrace]
  refine ⟨112036036040570969490883913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74690690693713979660589275 112036036040570969490883913)
  ·
    refine ⟨84027027030428227118162935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112036036040570969490883913 84027027030428227118162935)
    ·
      refine ⟨126040540545642340677244403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84027027030428227118162935 126040540545642340677244403)
      ·
        refine ⟨189060810818463511015866605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126040540545642340677244403 189060810818463511015866605)
        ·
          refine ⟨70897804056923816630949977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189060810818463511015866605 70897804056923816630949977)
          ·
            refine ⟨53173353042692862473212483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70897804056923816630949977 53173353042692862473212483)
            ·
              refine ⟨79760029564039293709818725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53173353042692862473212483 79760029564039293709818725)
              ·
                refine ⟨14955005543257367570591011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79760029564039293709818725 14955005543257367570591011)
                ·
                  refine ⟨22432508314886051355886517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14955005543257367570591011 22432508314886051355886517)
                  ·
                    refine ⟨2103047654520567314614361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22432508314886051355886517 2103047654520567314614361)
                    ·
                      refine ⟨1577285740890425485960771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103047654520567314614361 1577285740890425485960771)
                      ·
                        rfl

theorem cell23_3071753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 5, 2].length) (baseStart_3071753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071753 prefixEnd_3071753 := by exact prefixLift 3071753
  have htrace : WordTrace (prefixWord ++ tailWord_3071753) baseStart_3071753 baseEnd_3071753 := by
    simpa [prefixWord, tailWord_3071753, baseEnd_3071753] using wordTrace_append hprefix tailTrace_3071753
  have hstable : (prefixWord ++ tailWord_3071753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071753).length < 2 ^ (prefixWord ++ tailWord_3071753).sum := by decide
  have hdescent : baseEnd_3071753 < baseStart_3071753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071764 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3071764 : Nat := 118140960795 + 3071764 * 2 ^ 59
def prefixEnd_3071764 : Nat := 4983230072969 + 3 ^ 40 * 3071764 * 2
def baseEnd_3071764 : Nat := 1577291389177624942923221

theorem tailTrace_3071764 : CollatzResearch.WordTrace tailWord_3071764 prefixEnd_3071764 1577291389177624942923221 := by
  unfold tailWord_3071764
  simp only [CollatzResearch.WordTrace]
  refine ⟨56018218621765559184767173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74690958162354078913022897 56018218621765559184767173)
  ·
    refine ⟨10503415991581042347143845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56018218621765559184767173 10503415991581042347143845)
    ·
      refine ⟨1969390498421445440089471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10503415991581042347143845 1969390498421445440089471)
      ·
        refine ⟨2954085747632168160134207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1969390498421445440089471 2954085747632168160134207)
        ·
          refine ⟨4431128621448252240201311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2954085747632168160134207 4431128621448252240201311)
          ·
            refine ⟨6646692932172378360301967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4431128621448252240201311 6646692932172378360301967)
            ·
              refine ⟨9970039398258567540452951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6646692932172378360301967 9970039398258567540452951)
              ·
                refine ⟨14955059097387851310679427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9970039398258567540452951 14955059097387851310679427)
                ·
                  refine ⟨22432588646081776966019141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14955059097387851310679427 22432588646081776966019141)
                  ·
                    refine ⟨4206110371140333181128589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22432588646081776966019141 4206110371140333181128589)
                    ·
                      refine ⟨1577291389177624942923221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4206110371140333181128589 1577291389177624942923221)
                      ·
                        rfl

theorem cell23_3071764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3071764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071764 prefixEnd_3071764 := by exact prefixLift 3071764
  have htrace : WordTrace (prefixWord ++ tailWord_3071764) baseStart_3071764 baseEnd_3071764 := by
    simpa [prefixWord, tailWord_3071764, baseEnd_3071764] using wordTrace_append hprefix tailTrace_3071764
  have hstable : (prefixWord ++ tailWord_3071764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071764).length < 2 ^ (prefixWord ++ tailWord_3071764).sum := by decide
  have hdescent : baseEnd_3071764 < baseStart_3071764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071770 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2]
def baseStart_3071770 : Nat := 118140960795 + 3071770 * 2 ^ 59
def prefixEnd_3071770 : Nat := 4983230072969 + 3 ^ 40 * 3071770 * 2
def baseEnd_3071770 : Nat := 1577294470061551919448193

theorem tailTrace_3071770 : CollatzResearch.WordTrace tailWord_3071770 prefixEnd_3071770 1577294470061551919448193 := by
  unfold tailWord_3071770
  simp only [CollatzResearch.WordTrace]
  refine ⟨28009164020377345348563191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74691104054339587596168509 28009164020377345348563191)
  ·
    refine ⟨42013746030566018022844787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28009164020377345348563191 42013746030566018022844787)
    ·
      refine ⟨63020619045849027034267181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42013746030566018022844787 63020619045849027034267181)
      ·
        refine ⟨23632732142193385137850193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63020619045849027034267181 23632732142193385137850193)
        ·
          refine ⟨17724549106645038853387645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23632732142193385137850193 17724549106645038853387645)
          ·
            refine ⟨6646705914991889570020367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17724549106645038853387645 6646705914991889570020367)
            ·
              refine ⟨9970058872487834355030551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6646705914991889570020367 9970058872487834355030551)
              ·
                refine ⟨14955088308731751532545827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9970058872487834355030551 14955088308731751532545827)
                ·
                  refine ⟨22432632463097627298818741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14955088308731751532545827 22432632463097627298818741)
                  ·
                    refine ⟨2103059293415402559264257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22432632463097627298818741 2103059293415402559264257)
                    ·
                      refine ⟨1577294470061551919448193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103059293415402559264257 1577294470061551919448193)
                      ·
                        rfl

theorem cell23_3071770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_3071770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071770 prefixEnd_3071770 := by exact prefixLift 3071770
  have htrace : WordTrace (prefixWord ++ tailWord_3071770) baseStart_3071770 baseEnd_3071770 := by
    simpa [prefixWord, tailWord_3071770, baseEnd_3071770] using wordTrace_append hprefix tailTrace_3071770
  have hstable : (prefixWord ++ tailWord_3071770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071770).length < 2 ^ (prefixWord ++ tailWord_3071770).sum := by decide
  have hdescent : baseEnd_3071770 < baseStart_3071770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071777 : List Nat := [1, 2, 3, 2, 1, 3, 1, 5, 1, 1, 3]
def baseStart_3071777 : Nat := 118140960795 + 3071777 * 2 ^ 59
def prefixEnd_3071777 : Nat := 4983230072969 + 3 ^ 40 * 3071777 * 2
def baseEnd_3071777 : Nat := 1577298064426133392060661

theorem tailTrace_3071777 : CollatzResearch.WordTrace tailWord_3071777 prefixEnd_3071777 1577298064426133392060661 := by
  unfold tailWord_3071777
  simp only [CollatzResearch.WordTrace]
  refine ⟨112036911392484021589757585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74691274261656014393171723 112036911392484021589757585)
  ·
    refine ⟨84027683544363016192318189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112036911392484021589757585 84027683544363016192318189)
    ·
      refine ⟨31510381329136131072119321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84027683544363016192318189 31510381329136131072119321)
      ·
        refine ⟨23632785996852098304089491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31510381329136131072119321 23632785996852098304089491)
        ·
          refine ⟨35449178995278147456134237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23632785996852098304089491 35449178995278147456134237)
          ·
            refine ⟨13293442123229305296050339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35449178995278147456134237 13293442123229305296050339)
            ·
              refine ⟨19940163184843957944075509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13293442123229305296050339 19940163184843957944075509)
              ·
                refine ⟨1869390298579121057257079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19940163184843957944075509 1869390298579121057257079)
                ·
                  refine ⟨2804085447868681585885619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869390298579121057257079 2804085447868681585885619)
                  ·
                    refine ⟨4206128171803022378828429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2804085447868681585885619 4206128171803022378828429)
                    ·
                      refine ⟨1577298064426133392060661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4206128171803022378828429 1577298064426133392060661)
                      ·
                        rfl

theorem cell23_3071777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_3071777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071777 prefixEnd_3071777 := by exact prefixLift 3071777
  have htrace : WordTrace (prefixWord ++ tailWord_3071777) baseStart_3071777 baseEnd_3071777 := by
    simpa [prefixWord, tailWord_3071777, baseEnd_3071777] using wordTrace_append hprefix tailTrace_3071777
  have hstable : (prefixWord ++ tailWord_3071777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071777).length < 2 ^ (prefixWord ++ tailWord_3071777).sum := by decide
  have hdescent : baseEnd_3071777 < baseStart_3071777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071780 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_3071780 : Nat := 118140960795 + 3071780 * 2 ^ 59
def prefixEnd_3071780 : Nat := 4983230072969 + 3 ^ 40 * 3071780 * 2
def baseEnd_3071780 : Nat := 525766534956032293441049

theorem tailTrace_3071780 : CollatzResearch.WordTrace tailWord_3071780 prefixEnd_3071780 525766534956032293441049 := by
  unfold tailWord_3071780
  simp only [CollatzResearch.WordTrace]
  refine ⟨56018510405736576551058397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74691347207648768734744529 56018510405736576551058397)
  ·
    refine ⟨21006941402151216206646899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56018510405736576551058397 21006941402151216206646899)
    ·
      refine ⟨31510412103226824309970349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21006941402151216206646899 31510412103226824309970349)
      ·
        refine ⟨11816404538710059116238881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31510412103226824309970349 11816404538710059116238881)
        ·
          refine ⟨8862303404032544337179161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11816404538710059116238881 8862303404032544337179161)
          ·
            refine ⟨6646727553024408252884371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8862303404032544337179161 6646727553024408252884371)
            ·
              refine ⟨9970091329536612379326557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6646727553024408252884371 9970091329536612379326557)
              ·
                refine ⟨3738784248576229642247459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9970091329536612379326557 3738784248576229642247459)
                ·
                  refine ⟨5608176372864344463371189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738784248576229642247459 5608176372864344463371189)
                  ·
                    refine ⟨525766534956032293441049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5608176372864344463371189 525766534956032293441049)
                    ·
                      rfl

theorem cell23_3071780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_3071780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071780 prefixEnd_3071780 := by exact prefixLift 3071780
  have htrace : WordTrace (prefixWord ++ tailWord_3071780) baseStart_3071780 baseEnd_3071780 := by
    simpa [prefixWord, tailWord_3071780, baseEnd_3071780] using wordTrace_append hprefix tailTrace_3071780
  have hstable : (prefixWord ++ tailWord_3071780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071780).length < 2 ^ (prefixWord ++ tailWord_3071780).sum := by decide
  have hdescent : baseEnd_3071780 < baseStart_3071780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071814 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_3071814 : Nat := 118140960795 + 3071814 * 2 ^ 59
def prefixEnd_3071814 : Nat := 4983230072969 + 3 ^ 40 * 3071814 * 2
def baseEnd_3071814 : Nat := 525772354403449915765997

theorem tailTrace_3071814 : CollatzResearch.WordTrace tailWord_3071814 prefixEnd_3071814 525772354403449915765997 := by
  unfold tailWord_3071814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3501195652917186778401703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74692173928899984605902997 3501195652917186778401703)
  ·
    refine ⟨5251793479375780167602555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3501195652917186778401703 5251793479375780167602555)
    ·
      refine ⟨7877690219063670251403833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251793479375780167602555 7877690219063670251403833)
      ·
        refine ⟨5908267664297752688552875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7877690219063670251403833 5908267664297752688552875)
        ·
          refine ⟨8862401496446629032829313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5908267664297752688552875 8862401496446629032829313)
          ·
            refine ⟨6646801122334971774621985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8862401496446629032829313 6646801122334971774621985)
            ·
              refine ⟨4985100841751228830966489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6646801122334971774621985 4985100841751228830966489)
              ·
                refine ⟨3738825631313421623224867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4985100841751228830966489 3738825631313421623224867)
                ·
                  refine ⟨5608238446970132434837301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738825631313421623224867 5608238446970132434837301)
                  ·
                    refine ⟨525772354403449915765997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5608238446970132434837301 525772354403449915765997)
                    ·
                      rfl

theorem cell23_3071814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_3071814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071814 prefixEnd_3071814 := by exact prefixLift 3071814
  have htrace : WordTrace (prefixWord ++ tailWord_3071814) baseStart_3071814 baseEnd_3071814 := by
    simpa [prefixWord, tailWord_3071814, baseEnd_3071814] using wordTrace_append hprefix tailTrace_3071814
  have hstable : (prefixWord ++ tailWord_3071814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071814).length < 2 ^ (prefixWord ++ tailWord_3071814).sum := by decide
  have hdescent : baseEnd_3071814 < baseStart_3071814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071833 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 3, 3, 3]
def baseStart_3071833 : Nat := 118140960795 + 3071833 * 2 ^ 59
def prefixEnd_3071833 : Nat := 4983230072969 + 3 ^ 40 * 3071833 * 2
def baseEnd_3071833 : Nat := 1577326819342785172960403

theorem tailTrace_3071833 : CollatzResearch.WordTrace tailWord_3071833 prefixEnd_3071833 1577326819342785172960403 := by
  unfold tailWord_3071833
  simp only [CollatzResearch.WordTrace]
  refine ⟨112038953880281143153796153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74692635920187428769197435 112038953880281143153796153)
  ·
    refine ⟨84029215410210857365347115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112038953880281143153796153 84029215410210857365347115)
    ·
      refine ⟨126043823115316286048020673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84029215410210857365347115 126043823115316286048020673)
      ·
        refine ⟨94532867336487214536015505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126043823115316286048020673 94532867336487214536015505)
        ·
          refine ⟨70899650502365410902011629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94532867336487214536015505 70899650502365410902011629)
          ·
            refine ⟨26587368938387029088254361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70899650502365410902011629 26587368938387029088254361)
            ·
              refine ⟨19940526703790271816190771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26587368938387029088254361 19940526703790271816190771)
              ·
                refine ⟨29910790055685407724286157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19940526703790271816190771 29910790055685407724286157)
                ·
                  refine ⟨11216546270882027896607309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29910790055685407724286157 11216546270882027896607309)
                  ·
                    refine ⟨4206204851580760461227741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11216546270882027896607309 4206204851580760461227741)
                    ·
                      refine ⟨1577326819342785172960403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4206204851580760461227741 1577326819342785172960403)
                      ·
                        rfl

theorem cell23_3071833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_3071833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071833 prefixEnd_3071833 := by exact prefixLift 3071833
  have htrace : WordTrace (prefixWord ++ tailWord_3071833) baseStart_3071833 baseEnd_3071833 := by
    simpa [prefixWord, tailWord_3071833, baseEnd_3071833] using wordTrace_append hprefix tailTrace_3071833
  have hstable : (prefixWord ++ tailWord_3071833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071833).length < 2 ^ (prefixWord ++ tailWord_3071833).sum := by decide
  have hdescent : baseEnd_3071833 < baseStart_3071833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071893 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_3071893 : Nat := 118140960795 + 3071893 * 2 ^ 59
def prefixEnd_3071893 : Nat := 4983230072969 + 3 ^ 40 * 3071893 * 2
def baseEnd_3071893 : Nat := 1577357628182054938210127

theorem tailTrace_3071893 : CollatzResearch.WordTrace tailWord_3071893 prefixEnd_3071893 1577357628182054938210127 := by
  unfold tailWord_3071893
  simp only [CollatzResearch.WordTrace]
  refine ⟨112041142260063773400980333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74694094840042515600653555 112041142260063773400980333)
  ·
    refine ⟨42015428347523915025367625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112041142260063773400980333 42015428347523915025367625)
    ·
      refine ⟨31511571260642936269025719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42015428347523915025367625 31511571260642936269025719)
      ·
        refine ⟨47267356890964404403538579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31511571260642936269025719 47267356890964404403538579)
        ·
          refine ⟨70901035336446606605307869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47267356890964404403538579 70901035336446606605307869)
          ·
            refine ⟨26587888251167477476990451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70901035336446606605307869 26587888251167477476990451)
            ·
              refine ⟨39881832376751216215485677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26587888251167477476990451 39881832376751216215485677)
              ·
                refine ⟨14955687141281706080807129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39881832376751216215485677 14955687141281706080807129)
                ·
                  refine ⟨11216765355961279560605347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14955687141281706080807129 11216765355961279560605347)
                  ·
                    refine ⟨16825148033941919340908021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11216765355961279560605347 16825148033941919340908021)
                    ·
                      refine ⟨1577357628182054938210127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16825148033941919340908021 1577357628182054938210127)
                      ·
                        rfl

theorem cell23_3071893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_3071893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071893 prefixEnd_3071893 := by exact prefixLift 3071893
  have htrace : WordTrace (prefixWord ++ tailWord_3071893) baseStart_3071893 baseEnd_3071893 := by
    simpa [prefixWord, tailWord_3071893, baseEnd_3071893] using wordTrace_append hprefix tailTrace_3071893
  have hstable : (prefixWord ++ tailWord_3071893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071893).length < 2 ^ (prefixWord ++ tailWord_3071893).sum := by decide
  have hdescent : baseEnd_3071893 < baseStart_3071893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071902 : List Nat := [4, 3, 1, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_3071902 : Nat := 118140960795 + 3071902 * 2 ^ 59
def prefixEnd_3071902 : Nat := 4983230072969 + 3 ^ 40 * 3071902 * 2
def baseEnd_3071902 : Nat := 1577362249507945402997587

theorem tailTrace_3071902 : CollatzResearch.WordTrace tailWord_3071902 prefixEnd_3071902 1577362249507945402997587 := by
  unfold tailWord_3071902
  simp only [CollatzResearch.WordTrace]
  refine ⟨14005183814628895992257245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74694313678020778625371973 14005183814628895992257245)
  ·
    refine ⟨5251943930485835997096467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14005183814628895992257245 5251943930485835997096467)
    ·
      refine ⟨7877915895728753995644701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251943930485835997096467 7877915895728753995644701)
      ·
        refine ⟨2954218460898282748366763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7877915895728753995644701 2954218460898282748366763)
        ·
          refine ⟨4431327691347424122550145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2954218460898282748366763 4431327691347424122550145)
          ·
            refine ⟨3323495768510568091912609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4431327691347424122550145 3323495768510568091912609)
            ·
              refine ⟨2492621826382926068934457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3323495768510568091912609 2492621826382926068934457)
              ·
                refine ⟨1869466369787194551700843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2492621826382926068934457 1869466369787194551700843)
                ·
                  refine ⟨2804199554680791827551265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869466369787194551700843 2804199554680791827551265)
                  ·
                    refine ⟨2103149666010593870663449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2804199554680791827551265 2103149666010593870663449)
                    ·
                      refine ⟨1577362249507945402997587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103149666010593870663449 1577362249507945402997587)
                      ·
                        rfl

theorem cell23_3071902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_3071902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071902 prefixEnd_3071902 := by exact prefixLift 3071902
  have htrace : WordTrace (prefixWord ++ tailWord_3071902) baseStart_3071902 baseEnd_3071902 := by
    simpa [prefixWord, tailWord_3071902, baseEnd_3071902] using wordTrace_append hprefix tailTrace_3071902
  have hstable : (prefixWord ++ tailWord_3071902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071902).length < 2 ^ (prefixWord ++ tailWord_3071902).sum := by decide
  have hdescent : baseEnd_3071902 < baseStart_3071902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3071953 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_3071953 : Nat := 118140960795 + 3071953 * 2 ^ 59
def prefixEnd_3071953 : Nat := 4983230072969 + 3 ^ 40 * 3071953 * 2
def baseEnd_3071953 : Nat := 1577388437021324703459851

theorem tailTrace_3071953 : CollatzResearch.WordTrace tailWord_3071953 prefixEnd_3071953 1577388437021324703459851 := by
  unfold tailWord_3071953
  simp only [CollatzResearch.WordTrace]
  refine ⟨112043330639846403648164513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74695553759897602432109675 112043330639846403648164513)
  ·
    refine ⟨84032497979884802736123385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112043330639846403648164513 84032497979884802736123385)
    ·
      refine ⟨63024373484913602052092539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84032497979884802736123385 63024373484913602052092539)
      ·
        refine ⟨94536560227370403078138809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63024373484913602052092539 94536560227370403078138809)
        ·
          refine ⟨70902420170527802308604107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94536560227370403078138809 70902420170527802308604107)
          ·
            refine ⟨106353630255791703462906161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70902420170527802308604107 106353630255791703462906161)
            ·
              refine ⟨79765222691843777597179621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106353630255791703462906161 79765222691843777597179621)
              ·
                refine ⟨14955979254720708299471179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79765222691843777597179621 14955979254720708299471179)
                ·
                  refine ⟨22433968882081062449206769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14955979254720708299471179 22433968882081062449206769)
                  ·
                    refine ⟨16825476661560796836905077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22433968882081062449206769 16825476661560796836905077)
                    ·
                      refine ⟨1577388437021324703459851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16825476661560796836905077 1577388437021324703459851)
                      ·
                        rfl

theorem cell23_3071953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_3071953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3071953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3071953 prefixEnd_3071953 := by exact prefixLift 3071953
  have htrace : WordTrace (prefixWord ++ tailWord_3071953) baseStart_3071953 baseEnd_3071953 := by
    simpa [prefixWord, tailWord_3071953, baseEnd_3071953] using wordTrace_append hprefix tailTrace_3071953
  have hstable : (prefixWord ++ tailWord_3071953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3071953).length < 2 ^ (prefixWord ++ tailWord_3071953).sum := by decide
  have hdescent : baseEnd_3071953 < baseStart_3071953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3071953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072037 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 6]
def baseStart_3072037 : Nat := 118140960795 + 3072037 * 2 ^ 59
def prefixEnd_3072037 : Nat := 4983230072969 + 3 ^ 40 * 3072037 * 2
def baseEnd_3072037 : Nat := 175270174377366930534385

theorem tailTrace_3072037 : CollatzResearch.WordTrace tailWord_3072037 prefixEnd_3072037 175270174377366930534385 := by
  unfold tailWord_3072037
  simp only [CollatzResearch.WordTrace]
  refine ⟨112046394371542085994222365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74697596247694723996148243 112046394371542085994222365)
  ·
    refine ⟨42017397889328282247833387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112046394371542085994222365 42017397889328282247833387)
    ·
      refine ⟨63026096833992423371750081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42017397889328282247833387 63026096833992423371750081)
      ·
        refine ⟨47269572625494317528812561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63026096833992423371750081 47269572625494317528812561)
        ·
          refine ⟨35452179469120738146609421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47269572625494317528812561 35452179469120738146609421)
          ·
            refine ⟨13294567300920276804978533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35452179469120738146609421 13294567300920276804978533)
            ·
              refine ⟨2492731368922551900933475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13294567300920276804978533 2492731368922551900933475)
              ·
                refine ⟨3739097053383827851400213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492731368922551900933475 3739097053383827851400213)
                ·
                  refine ⟨175270174377366930534385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3739097053383827851400213 175270174377366930534385)
                  ·
                    rfl

theorem cell23_3072037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_3072037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072037 prefixEnd_3072037 := by exact prefixLift 3072037
  have htrace : WordTrace (prefixWord ++ tailWord_3072037) baseStart_3072037 baseEnd_3072037 := by
    simpa [prefixWord, tailWord_3072037, baseEnd_3072037] using wordTrace_append hprefix tailTrace_3072037
  have hstable : (prefixWord ++ tailWord_3072037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072037).length < 2 ^ (prefixWord ++ tailWord_3072037).sum := by decide
  have hdescent : baseEnd_3072037 < baseStart_3072037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072043 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 7]
def baseStart_3072043 : Nat := 118140960795 + 3072043 * 2 ^ 59
def prefixEnd_3072043 : Nat := 4983230072969 + 3 ^ 40 * 3072043 * 2
def baseEnd_3072043 : Nat := 1577434650280229351334437

theorem tailTrace_3072043 : CollatzResearch.WordTrace tailWord_3072043 prefixEnd_3072043 1577434650280229351334437 := by
  unfold tailWord_3072043
  simp only [CollatzResearch.WordTrace]
  refine ⟨112046613209520349018940783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74697742139680232679293855 112046613209520349018940783)
  ·
    refine ⟨168069919814280523528411175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112046613209520349018940783 168069919814280523528411175)
    ·
      refine ⟨252104879721420785292616763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168069919814280523528411175 252104879721420785292616763)
      ·
        refine ⟨378157319582131177938925145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252104879721420785292616763 378157319582131177938925145)
        ·
          refine ⟨283617989686598383454193859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378157319582131177938925145 283617989686598383454193859)
          ·
            refine ⟨425426984529897575181290789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283617989686598383454193859 425426984529897575181290789)
            ·
              refine ⟨79767559599355795346492023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 425426984529897575181290789 79767559599355795346492023)
              ·
                refine ⟨119651339399033693019738035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79767559599355795346492023 119651339399033693019738035)
                ·
                  refine ⟨179477009098550539529607053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119651339399033693019738035 179477009098550539529607053)
                  ·
                    refine ⟨67303878411956452323602645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179477009098550539529607053 67303878411956452323602645)
                    ·
                      refine ⟨1577434650280229351334437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67303878411956452323602645 1577434650280229351334437)
                      ·
                        rfl

theorem cell23_3072043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_3072043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072043 prefixEnd_3072043 := by exact prefixLift 3072043
  have htrace : WordTrace (prefixWord ++ tailWord_3072043) baseStart_3072043 baseEnd_3072043 := by
    simpa [prefixWord, tailWord_3072043, baseEnd_3072043] using wordTrace_append hprefix tailTrace_3072043
  have hstable : (prefixWord ++ tailWord_3072043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072043).length < 2 ^ (prefixWord ++ tailWord_3072043).sum := by decide
  have hdescent : baseEnd_3072043 < baseStart_3072043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072090 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_3072090 : Nat := 118140960795 + 3072090 * 2 ^ 59
def prefixEnd_3072090 : Nat := 4983230072969 + 3 ^ 40 * 3072090 * 2
def baseEnd_3072090 : Nat := 1577458783870990667446721

theorem tailTrace_3072090 : CollatzResearch.WordTrace tailWord_3072090 prefixEnd_3072090 1577458783870990667446721 := by
  unfold tailWord_3072090
  simp only [CollatzResearch.WordTrace]
  refine ⟨28012081860087519011475431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74698884960233384030601149 28012081860087519011475431)
  ·
    refine ⟨42018122790131278517213147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28012081860087519011475431 42018122790131278517213147)
    ·
      refine ⟨63027184185196917775819721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42018122790131278517213147 63027184185196917775819721)
      ·
        refine ⟨47270388138897688331864791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63027184185196917775819721 47270388138897688331864791)
        ·
          refine ⟨70905582208346532497797187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47270388138897688331864791 70905582208346532497797187)
          ·
            refine ⟨106358373312519798746695781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70905582208346532497797187 106358373312519798746695781)
            ·
              refine ⟨19942194996097462265005459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106358373312519798746695781 19942194996097462265005459)
              ·
                refine ⟨29913292494146193397508189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19942194996097462265005459 29913292494146193397508189)
                ·
                  refine ⟨11217484685304822524065571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29913292494146193397508189 11217484685304822524065571)
                  ·
                    refine ⟨16826227027957233786098357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11217484685304822524065571 16826227027957233786098357)
                    ·
                      refine ⟨1577458783870990667446721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16826227027957233786098357 1577458783870990667446721)
                      ·
                        rfl

theorem cell23_3072090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_3072090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072090 prefixEnd_3072090 := by exact prefixLift 3072090
  have htrace : WordTrace (prefixWord ++ tailWord_3072090) baseStart_3072090 baseEnd_3072090 := by
    simpa [prefixWord, tailWord_3072090, baseEnd_3072090] using wordTrace_append hprefix tailTrace_3072090
  have hstable : (prefixWord ++ tailWord_3072090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072090).length < 2 ^ (prefixWord ++ tailWord_3072090).sum := by decide
  have hdescent : baseEnd_3072090 < baseStart_3072090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072100 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_3072100 : Nat := 118140960795 + 3072100 * 2 ^ 59
def prefixEnd_3072100 : Nat := 4983230072969 + 3 ^ 40 * 3072100 * 2
def baseEnd_3072100 : Nat := 1577463918677535628321675

theorem tailTrace_3072100 : CollatzResearch.WordTrace tailWord_3072100 prefixEnd_3072100 1577463918677535628321675 := by
  unfold tailWord_3072100
  simp only [CollatzResearch.WordTrace]
  refine ⟨56024346085156923876882877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74699128113542565169177169 56024346085156923876882877)
  ·
    refine ⟨21009129781933846453831079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56024346085156923876882877 21009129781933846453831079)
    ·
      refine ⟨31513694672900769680746619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21009129781933846453831079 31513694672900769680746619)
      ·
        refine ⟨47270542009351154521119929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31513694672900769680746619 47270542009351154521119929)
        ·
          refine ⟨35452906507013365890839947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47270542009351154521119929 35452906507013365890839947)
          ·
            refine ⟨53179359760520048836259921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35452906507013365890839947 53179359760520048836259921)
            ·
              refine ⟨39884519820390036627194941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53179359760520048836259921 39884519820390036627194941)
              ·
                refine ⟨14956694932646263735198103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39884519820390036627194941 14956694932646263735198103)
                ·
                  refine ⟨22435042398969395602797155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14956694932646263735198103 22435042398969395602797155)
                  ·
                    refine ⟨33652563598454093404195733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22435042398969395602797155 33652563598454093404195733)
                    ·
                      refine ⟨1577463918677535628321675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33652563598454093404195733 1577463918677535628321675)
                      ·
                        rfl

theorem cell23_3072100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_3072100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072100 prefixEnd_3072100 := by exact prefixLift 3072100
  have htrace : WordTrace (prefixWord ++ tailWord_3072100) baseStart_3072100 baseEnd_3072100 := by
    simpa [prefixWord, tailWord_3072100, baseEnd_3072100] using wordTrace_append hprefix tailTrace_3072100
  have hstable : (prefixWord ++ tailWord_3072100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072100).length < 2 ^ (prefixWord ++ tailWord_3072100).sum := by decide
  have hdescent : baseEnd_3072100 < baseStart_3072100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072121 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 1, 1, 4]
def baseStart_3072121 : Nat := 118140960795 + 3072121 * 2 ^ 59
def prefixEnd_3072121 : Nat := 4983230072969 + 3 ^ 40 * 3072121 * 2
def baseEnd_3072121 : Nat := 1577474701771280046159079

theorem tailTrace_3072121 : CollatzResearch.WordTrace tailWord_3072121 prefixEnd_3072121 1577474701771280046159079 := by
  unfold tailWord_3072121
  simp only [CollatzResearch.WordTrace]
  refine ⟨112049458103237768340280217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74699638735491845560186811 112049458103237768340280217)
  ·
    refine ⟨84037093577428326255210163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112049458103237768340280217 84037093577428326255210163)
    ·
      refine ⟨126055640366142489382815245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84037093577428326255210163 126055640366142489382815245)
      ·
        refine ⟨47270865137303433518555717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126055640366142489382815245 47270865137303433518555717)
        ·
          refine ⟨8863287213244393784729197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47270865137303433518555717 8863287213244393784729197)
          ·
            refine ⟨3323732704966647669273449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8863287213244393784729197 3323732704966647669273449)
            ·
              refine ⟨2492799528724985751955087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3323732704966647669273449 2492799528724985751955087)
              ·
                refine ⟨3739199293087478627932631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492799528724985751955087 3739199293087478627932631)
                ·
                  refine ⟨5608798939631217941898947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739199293087478627932631 5608798939631217941898947)
                  ·
                    refine ⟨8413198409446826912848421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5608798939631217941898947 8413198409446826912848421)
                    ·
                      refine ⟨1577474701771280046159079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8413198409446826912848421 1577474701771280046159079)
                      ·
                        rfl

theorem cell23_3072121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_3072121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072121 prefixEnd_3072121 := by exact prefixLift 3072121
  have htrace : WordTrace (prefixWord ++ tailWord_3072121) baseStart_3072121 baseEnd_3072121 := by
    simpa [prefixWord, tailWord_3072121, baseEnd_3072121] using wordTrace_append hprefix tailTrace_3072121
  have hstable : (prefixWord ++ tailWord_3072121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072121).length < 2 ^ (prefixWord ++ tailWord_3072121).sum := by decide
  have hdescent : baseEnd_3072121 < baseStart_3072121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072124 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_3072124 : Nat := 118140960795 + 3072124 * 2 ^ 59
def prefixEnd_3072124 : Nat := 4983230072969 + 3 ^ 40 * 3072124 * 2
def baseEnd_3072124 : Nat := 1577476242213243534421565

theorem tailTrace_3072124 : CollatzResearch.WordTrace tailWord_3072124 prefixEnd_3072124 1577476242213243534421565 := by
  unfold tailWord_3072124
  simp only [CollatzResearch.WordTrace]
  refine ⟨56024783761113449926319713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74699711681484599901759617 56024783761113449926319713)
  ·
    refine ⟨42018587820835087444739785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56024783761113449926319713 42018587820835087444739785)
    ·
      refine ⟨31513940865626315583554839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42018587820835087444739785 31513940865626315583554839)
      ·
        refine ⟨47270911298439473375332259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31513940865626315583554839 47270911298439473375332259)
        ·
          refine ⟨70906366947659210062998389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47270911298439473375332259 70906366947659210062998389)
          ·
            refine ⟨6647471901343050943406099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70906366947659210062998389 6647471901343050943406099)
            ·
              refine ⟨9971207852014576415109149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6647471901343050943406099 9971207852014576415109149)
              ·
                refine ⟨3739202944505466155665931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9971207852014576415109149 3739202944505466155665931)
                ·
                  refine ⟨5608804416758199233498897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739202944505466155665931 5608804416758199233498897)
                  ·
                    refine ⟨4206603312568649425124173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5608804416758199233498897 4206603312568649425124173)
                    ·
                      refine ⟨1577476242213243534421565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4206603312568649425124173 1577476242213243534421565)
                      ·
                        rfl

theorem cell23_3072124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_3072124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072124 prefixEnd_3072124 := by exact prefixLift 3072124
  have htrace : WordTrace (prefixWord ++ tailWord_3072124) baseStart_3072124 baseEnd_3072124 := by
    simpa [prefixWord, tailWord_3072124, baseEnd_3072124] using wordTrace_append hprefix tailTrace_3072124
  have hstable : (prefixWord ++ tailWord_3072124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072124).length < 2 ^ (prefixWord ++ tailWord_3072124).sum := by decide
  have hdescent : baseEnd_3072124 < baseStart_3072124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072138 : List Nat := [3, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2]
def baseStart_3072138 : Nat := 118140960795 + 3072138 * 2 ^ 59
def prefixEnd_3072138 : Nat := 4983230072969 + 3 ^ 40 * 3072138 * 2
def baseEnd_3072138 : Nat := 1577483430942406479646501

theorem tailTrace_3072138 : CollatzResearch.WordTrace tailWord_3072138 prefixEnd_3072138 1577483430942406479646501 := by
  unfold tailWord_3072138
  simp only [CollatzResearch.WordTrace]
  refine ⟨28012519536044045060912267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74700052096117453495766045 28012519536044045060912267)
  ·
    refine ⟨42018779304066067591368401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28012519536044045060912267 42018779304066067591368401)
    ·
      refine ⟨31514084478049550693526301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42018779304066067591368401 31514084478049550693526301)
      ·
        refine ⟨11817781679268581510072363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31514084478049550693526301 11817781679268581510072363)
        ·
          refine ⟨17726672518902872265108545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11817781679268581510072363 17726672518902872265108545)
          ·
            refine ⟨13295004389177154198831409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17726672518902872265108545 13295004389177154198831409)
            ·
              refine ⟨9971253291882865649123557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13295004389177154198831409 9971253291882865649123557)
              ·
                refine ⟨1869609992228037309210667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9971253291882865649123557 1869609992228037309210667)
                ·
                  refine ⟨2804414988342055963816001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869609992228037309210667 2804414988342055963816001)
                  ·
                    refine ⟨2103311241256541972862001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2804414988342055963816001 2103311241256541972862001)
                    ·
                      refine ⟨1577483430942406479646501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103311241256541972862001 1577483430942406479646501)
                      ·
                        rfl

theorem cell23_3072138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_3072138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072138 prefixEnd_3072138 := by exact prefixLift 3072138
  have htrace : WordTrace (prefixWord ++ tailWord_3072138) baseStart_3072138 baseEnd_3072138 := by
    simpa [prefixWord, tailWord_3072138, baseEnd_3072138] using wordTrace_append hprefix tailTrace_3072138
  have hstable : (prefixWord ++ tailWord_3072138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072138).length < 2 ^ (prefixWord ++ tailWord_3072138).sum := by decide
  have hdescent : baseEnd_3072138 < baseStart_3072138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072148 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_3072148 : Nat := 118140960795 + 3072148 * 2 ^ 59
def prefixEnd_3072148 : Nat := 4983230072969 + 3 ^ 40 * 3072148 * 2
def baseEnd_3072148 : Nat := 525829521916317146840485

theorem tailTrace_3072148 : CollatzResearch.WordTrace tailWord_3072148 prefixEnd_3072148 525829521916317146840485 := by
  unfold tailWord_3072148
  simp only [CollatzResearch.WordTrace]
  refine ⟨56025221437069975975756549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74700295249426634634342065 56025221437069975975756549)
  ·
    refine ⟨10504729019450620495454353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56025221437069975975756549 10504729019450620495454353)
    ·
      refine ⟨7878546764587965371590765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10504729019450620495454353 7878546764587965371590765)
      ·
        refine ⟨2954455036720487014346537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7878546764587965371590765 2954455036720487014346537)
        ·
          refine ⟨2215841277540365260759903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2954455036720487014346537 2215841277540365260759903)
          ·
            refine ⟨3323761916310547891139855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215841277540365260759903 3323761916310547891139855)
            ·
              refine ⟨4985642874465821836709783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3323761916310547891139855 4985642874465821836709783)
              ·
                refine ⟨7478464311698732755064675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4985642874465821836709783 7478464311698732755064675)
                ·
                  refine ⟨11217696467548099132597013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7478464311698732755064675 11217696467548099132597013)
                  ·
                    refine ⟨525829521916317146840485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11217696467548099132597013 525829521916317146840485)
                    ·
                      rfl

theorem cell23_3072148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_3072148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072148 prefixEnd_3072148 := by exact prefixLift 3072148
  have htrace : WordTrace (prefixWord ++ tailWord_3072148) baseStart_3072148 baseEnd_3072148 := by
    simpa [prefixWord, tailWord_3072148, baseEnd_3072148] using wordTrace_append hprefix tailTrace_3072148
  have hstable : (prefixWord ++ tailWord_3072148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072148).length < 2 ^ (prefixWord ++ tailWord_3072148).sum := by decide
  have hdescent : baseEnd_3072148 < baseStart_3072148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072151 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 1, 2, 4]
def baseStart_3072151 : Nat := 118140960795 + 3072151 * 2 ^ 59
def prefixEnd_3072151 : Nat := 4983230072969 + 3 ^ 40 * 3072151 * 2
def baseEnd_3072151 : Nat := 1577490106190914928783941

theorem tailTrace_3072151 : CollatzResearch.WordTrace tailWord_3072151 prefixEnd_3072151 1577490106190914928783941 := by
  unfold tailWord_3072151
  simp only [CollatzResearch.WordTrace]
  refine ⟨112050552293129083463872307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74700368195419388975914871 112050552293129083463872307)
  ·
    refine ⟨168075828439693625195808461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112050552293129083463872307 168075828439693625195808461)
    ·
      refine ⟨63028435664885109448428173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168075828439693625195808461 63028435664885109448428173)
      ·
        refine ⟨23635663374331916043160565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63028435664885109448428173 23635663374331916043160565)
        ·
          refine ⟨2215843441343617129046303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23635663374331916043160565 2215843441343617129046303)
          ·
            refine ⟨3323765162015425693569455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215843441343617129046303 3323765162015425693569455)
            ·
              refine ⟨4985647743023138540354183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3323765162015425693569455 4985647743023138540354183)
              ·
                refine ⟨7478471614534707810531275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4985647743023138540354183 7478471614534707810531275)
                ·
                  refine ⟨11217707421802061715796913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7478471614534707810531275 11217707421802061715796913)
                  ·
                    refine ⟨8413280566351546286847685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11217707421802061715796913 8413280566351546286847685)
                    ·
                      refine ⟨1577490106190914928783941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8413280566351546286847685 1577490106190914928783941)
                      ·
                        rfl

theorem cell23_3072151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_3072151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072151 prefixEnd_3072151 := by exact prefixLift 3072151
  have htrace : WordTrace (prefixWord ++ tailWord_3072151) baseStart_3072151 baseEnd_3072151 := by
    simpa [prefixWord, tailWord_3072151, baseEnd_3072151] using wordTrace_append hprefix tailTrace_3072151
  have hstable : (prefixWord ++ tailWord_3072151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072151).length < 2 ^ (prefixWord ++ tailWord_3072151).sum := by decide
  have hdescent : baseEnd_3072151 < baseStart_3072151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072158 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_3072158 : Nat := 118140960795 + 3072158 * 2 ^ 59
def prefixEnd_3072158 : Nat := 4983230072969 + 3 ^ 40 * 3072158 * 2
def baseEnd_3072158 : Nat := 1577493700555496401396409

theorem tailTrace_3072158 : CollatzResearch.WordTrace tailWord_3072158 prefixEnd_3072158 1577493700555496401396409 := by
  unfold tailWord_3072158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14006350950512965457422141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74700538402735815772918085 14006350950512965457422141)
  ·
    refine ⟨5252381606442362046533303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14006350950512965457422141 5252381606442362046533303)
    ·
      refine ⟨7878572409663543069799955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5252381606442362046533303 7878572409663543069799955)
      ·
        refine ⟨11817858614495314604699933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7878572409663543069799955 11817858614495314604699933)
        ·
          refine ⟨4431696980435742976762475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11817858614495314604699933 4431696980435742976762475)
          ·
            refine ⟨6647545470653614465143713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4431696980435742976762475 6647545470653614465143713)
            ·
              refine ⟨4985659102990210848857785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6647545470653614465143713 4985659102990210848857785)
              ·
                refine ⟨3739244327242658136643339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4985659102990210848857785 3739244327242658136643339)
                ·
                  refine ⟨5608866490863987204965009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739244327242658136643339 5608866490863987204965009)
                  ·
                    refine ⟨4206649868147990403723757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5608866490863987204965009 4206649868147990403723757)
                    ·
                      refine ⟨1577493700555496401396409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4206649868147990403723757 1577493700555496401396409)
                      ·
                        rfl

theorem cell23_3072158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_3072158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072158 prefixEnd_3072158 := by exact prefixLift 3072158
  have htrace : WordTrace (prefixWord ++ tailWord_3072158) baseStart_3072158 baseEnd_3072158 := by
    simpa [prefixWord, tailWord_3072158, baseEnd_3072158] using wordTrace_append hprefix tailTrace_3072158
  have hstable : (prefixWord ++ tailWord_3072158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072158).length < 2 ^ (prefixWord ++ tailWord_3072158).sum := by decide
  have hdescent : baseEnd_3072158 < baseStart_3072158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072234 : List Nat := [3, 1, 3, 1, 1, 2, 2, 5, 5]
def baseStart_3072234 : Nat := 118140960795 + 3072234 * 2 ^ 59
def prefixEnd_3072234 : Nat := 4983230072969 + 3 ^ 40 * 3072234 * 2
def baseEnd_3072234 : Nat := 175281413898359789338451

theorem tailTrace_3072234 : CollatzResearch.WordTrace tailWord_3072234 prefixEnd_3072234 175281413898359789338451 := by
  unfold tailWord_3072234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28013394887957097159785939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74702386367885592426095837 28013394887957097159785939)
  ·
    refine ⟨42020092331935645739678909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28013394887957097159785939 42020092331935645739678909)
    ·
      refine ⟨15757534624475867152379591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42020092331935645739678909 15757534624475867152379591)
      ·
        refine ⟨23636301936713800728569387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15757534624475867152379591 23636301936713800728569387)
        ·
          refine ⟨35454452905070701092854081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23636301936713800728569387 35454452905070701092854081)
          ·
            refine ⟨26590839678803025819640561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35454452905070701092854081 26590839678803025819640561)
            ·
              refine ⟨19943129759102269364730421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26590839678803025819640561 19943129759102269364730421)
              ·
                refine ⟨1869668414915837752943477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19943129759102269364730421 1869668414915837752943477)
                ·
                  refine ⟨175281413898359789338451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1869668414915837752943477 175281413898359789338451)
                  ·
                    rfl

theorem cell23_3072234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_3072234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072234 prefixEnd_3072234 := by exact prefixLift 3072234
  have htrace : WordTrace (prefixWord ++ tailWord_3072234) baseStart_3072234 baseEnd_3072234 := by
    simpa [prefixWord, tailWord_3072234, baseEnd_3072234] using wordTrace_append hprefix tailTrace_3072234
  have hstable : (prefixWord ++ tailWord_3072234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072234).length < 2 ^ (prefixWord ++ tailWord_3072234).sum := by decide
  have hdescent : baseEnd_3072234 < baseStart_3072234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072257 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_3072257 : Nat := 118140960795 + 3072257 * 2 ^ 59
def prefixEnd_3072257 : Nat := 4983230072969 + 3 ^ 40 * 3072257 * 2
def baseEnd_3072257 : Nat := 1577544535140291514058453

theorem tailTrace_3072257 : CollatzResearch.WordTrace tailWord_3072257 prefixEnd_3072257 1577544535140291514058453 := by
  unfold tailWord_3072257
  simp only [CollatzResearch.WordTrace]
  refine ⟨112054418430745063567231025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74702945620496709044820683 112054418430745063567231025)
  ·
    refine ⟨84040813823058797675423269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112054418430745063567231025 84040813823058797675423269)
    ·
      refine ⟨15757652591823524564141863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84040813823058797675423269 15757652591823524564141863)
      ·
        refine ⟨23636478887735286846212795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15757652591823524564141863 23636478887735286846212795)
        ·
          refine ⟨35454718331602930269319193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23636478887735286846212795 35454718331602930269319193)
          ·
            refine ⟨26591038748702197701989395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35454718331602930269319193 26591038748702197701989395)
            ·
              refine ⟨39886558123053296552984093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26591038748702197701989395 39886558123053296552984093)
              ·
                refine ⟨14957459296144986207369035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39886558123053296552984093 14957459296144986207369035)
                ·
                  refine ⟨22436188944217479311053553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14957459296144986207369035 22436188944217479311053553)
                  ·
                    refine ⟨16827141708163109483290165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22436188944217479311053553 16827141708163109483290165)
                    ·
                      refine ⟨1577544535140291514058453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16827141708163109483290165 1577544535140291514058453)
                      ·
                        rfl

theorem cell23_3072257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_3072257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072257 prefixEnd_3072257 := by exact prefixLift 3072257
  have htrace : WordTrace (prefixWord ++ tailWord_3072257) baseStart_3072257 baseEnd_3072257 := by
    simpa [prefixWord, tailWord_3072257, baseEnd_3072257] using wordTrace_append hprefix tailTrace_3072257
  have hstable : (prefixWord ++ tailWord_3072257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072257).length < 2 ^ (prefixWord ++ tailWord_3072257).sum := by decide
  have hdescent : baseEnd_3072257 < baseStart_3072257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072267 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 4]
def baseStart_3072267 : Nat := 118140960795 + 3072267 * 2 ^ 59
def prefixEnd_3072267 : Nat := 4983230072969 + 3 ^ 40 * 3072267 * 2
def baseEnd_3072267 : Nat := 1577549669946836474933407

theorem tailTrace_3072267 : CollatzResearch.WordTrace tailWord_3072267 prefixEnd_3072267 1577549669946836474933407 := by
  unfold tailWord_3072267
  simp only [CollatzResearch.WordTrace]
  refine ⟨112054783160708835275095055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74703188773805890183396703 112054783160708835275095055)
  ·
    refine ⟨168082174741063252912642583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112054783160708835275095055 168082174741063252912642583)
    ·
      refine ⟨252123262111594879368963875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168082174741063252912642583 252123262111594879368963875)
      ·
        refine ⟨378184893167392319053445813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252123262111594879368963875 378184893167392319053445813)
        ·
          refine ⟨35454833734443029911260545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 378184893167392319053445813 35454833734443029911260545)
          ·
            refine ⟨26591125300832272433445409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35454833734443029911260545 26591125300832272433445409)
            ·
              refine ⟨19943343975624204325084057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26591125300832272433445409 19943343975624204325084057)
              ·
                refine ⟨14957507981718153243813043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19943343975624204325084057 14957507981718153243813043)
                ·
                  refine ⟨22436261972577229865719565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14957507981718153243813043 22436261972577229865719565)
                  ·
                    refine ⟨8413598239716461199644837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22436261972577229865719565 8413598239716461199644837)
                    ·
                      refine ⟨1577549669946836474933407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8413598239716461199644837 1577549669946836474933407)
                      ·
                        rfl

theorem cell23_3072267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 4].length) (baseStart_3072267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072267 prefixEnd_3072267 := by exact prefixLift 3072267
  have htrace : WordTrace (prefixWord ++ tailWord_3072267) baseStart_3072267 baseEnd_3072267 := by
    simpa [prefixWord, tailWord_3072267, baseEnd_3072267] using wordTrace_append hprefix tailTrace_3072267
  have hstable : (prefixWord ++ tailWord_3072267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072267).length < 2 ^ (prefixWord ++ tailWord_3072267).sum := by decide
  have hdescent : baseEnd_3072267 < baseStart_3072267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072284 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_3072284 : Nat := 118140960795 + 3072284 * 2 ^ 59
def prefixEnd_3072284 : Nat := 4983230072969 + 3 ^ 40 * 3072284 * 2
def baseEnd_3072284 : Nat := 1577558399117962908420829

theorem tailTrace_3072284 : CollatzResearch.WordTrace tailWord_3072284 prefixEnd_3072284 1577558399117962908420829 := by
  unfold tailWord_3072284
  simp only [CollatzResearch.WordTrace]
  refine ⟨56027701600823623589231953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74703602134431498118975937 56027701600823623589231953)
  ·
    refine ⟨42020776200617717691923965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56027701600823623589231953 42020776200617717691923965)
    ·
      refine ⟨15757791075231644134471487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42020776200617717691923965 15757791075231644134471487)
      ·
        refine ⟨23636686612847466201707231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15757791075231644134471487 23636686612847466201707231)
        ·
          refine ⟨35455029919271199302560847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23636686612847466201707231 35455029919271199302560847)
          ·
            refine ⟨53182544878906798953841271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35455029919271199302560847 53182544878906798953841271)
            ·
              refine ⟨79773817318360198430761907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53182544878906798953841271 79773817318360198430761907)
              ·
                refine ⟨119660725977540297646142861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79773817318360198430761907 119660725977540297646142861)
                ·
                  refine ⟨44872772241577611617303573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119660725977540297646142861 44872772241577611617303573)
                  ·
                    refine ⟨2103411198823950544561105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 44872772241577611617303573 2103411198823950544561105)
                    ·
                      refine ⟨1577558399117962908420829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103411198823950544561105 1577558399117962908420829)
                      ·
                        rfl

theorem cell23_3072284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_3072284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072284 prefixEnd_3072284 := by exact prefixLift 3072284
  have htrace : WordTrace (prefixWord ++ tailWord_3072284) baseStart_3072284 baseEnd_3072284 := by
    simpa [prefixWord, tailWord_3072284, baseEnd_3072284] using wordTrace_append hprefix tailTrace_3072284
  have hstable : (prefixWord ++ tailWord_3072284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072284).length < 2 ^ (prefixWord ++ tailWord_3072284).sum := by decide
  have hdescent : baseEnd_3072284 < baseStart_3072284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072307 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 8]
def baseStart_3072307 : Nat := 118140960795 + 3072307 * 2 ^ 59
def prefixEnd_3072307 : Nat := 4983230072969 + 3 ^ 40 * 3072307 * 2
def baseEnd_3072307 : Nat := 175285578797001813159247

theorem tailTrace_3072307 : CollatzResearch.WordTrace tailWord_3072307 prefixEnd_3072307 175285578797001813159247 := by
  unfold tailWord_3072307
  simp only [CollatzResearch.WordTrace]
  refine ⟨112056242080563922106551175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74704161387042614737700783 112056242080563922106551175)
  ·
    refine ⟨168084363120845883159826763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112056242080563922106551175 168084363120845883159826763)
    ·
      refine ⟨252126544681268824739740145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168084363120845883159826763 252126544681268824739740145)
      ·
        refine ⟨189094908510951618554805109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252126544681268824739740145 189094908510951618554805109)
        ·
          refine ⟨17727647672901714239512979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189094908510951618554805109 17727647672901714239512979)
          ·
            refine ⟨26591471509352571359269469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17727647672901714239512979 26591471509352571359269469)
            ·
              refine ⟨9971801816007214259726051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26591471509352571359269469 9971801816007214259726051)
              ·
                refine ⟨14957702724010821389589077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9971801816007214259726051 14957702724010821389589077)
                ·
                  refine ⟨175285578797001813159247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14957702724010821389589077 175285578797001813159247)
                  ·
                    rfl

theorem cell23_3072307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 8].length) (baseStart_3072307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072307 prefixEnd_3072307 := by exact prefixLift 3072307
  have htrace : WordTrace (prefixWord ++ tailWord_3072307) baseStart_3072307 baseEnd_3072307 := by
    simpa [prefixWord, tailWord_3072307, baseEnd_3072307] using wordTrace_append hprefix tailTrace_3072307
  have hstable : (prefixWord ++ tailWord_3072307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072307).length < 2 ^ (prefixWord ++ tailWord_3072307).sum := by decide
  have hdescent : baseEnd_3072307 < baseStart_3072307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072327 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_3072327 : Nat := 118140960795 + 3072327 * 2 ^ 59
def prefixEnd_3072327 : Nat := 4983230072969 + 3 ^ 40 * 3072327 * 2
def baseEnd_3072327 : Nat := 1577580478786106240183131

theorem tailTrace_3072327 : CollatzResearch.WordTrace tailWord_3072327 prefixEnd_3072327 1577580478786106240183131 := by
  unfold tailWord_3072327
  simp only [CollatzResearch.WordTrace]
  refine ⟨112056971540491465522279235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74704647693660977014852823 112056971540491465522279235)
  ·
    refine ⟨168085457310737198283418853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112056971540491465522279235 168085457310737198283418853)
    ·
      refine ⟨31516023245763224678141035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168085457310737198283418853 31516023245763224678141035)
      ·
        refine ⟨47274034868644837017211553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31516023245763224678141035 47274034868644837017211553)
        ·
          refine ⟨35455526151483627762908665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47274034868644837017211553 35455526151483627762908665)
          ·
            refine ⟨26591644613612720822181499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35455526151483627762908665 26591644613612720822181499)
            ·
              refine ⟨39887466920419081233272249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26591644613612720822181499 39887466920419081233272249)
              ·
                refine ⟨29915600190314310924954187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39887466920419081233272249 29915600190314310924954187)
                ·
                  refine ⟨44873400285471466387431281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29915600190314310924954187 44873400285471466387431281)
                  ·
                    refine ⟨33655050214103599790573461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44873400285471466387431281 33655050214103599790573461)
                    ·
                      refine ⟨1577580478786106240183131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33655050214103599790573461 1577580478786106240183131)
                      ·
                        rfl

theorem cell23_3072327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_3072327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072327 prefixEnd_3072327 := by exact prefixLift 3072327
  have htrace : WordTrace (prefixWord ++ tailWord_3072327) baseStart_3072327 baseEnd_3072327 := by
    simpa [prefixWord, tailWord_3072327, baseEnd_3072327] using wordTrace_append hprefix tailTrace_3072327
  have hstable : (prefixWord ++ tailWord_3072327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072327).length < 2 ^ (prefixWord ++ tailWord_3072327).sum := by decide
  have hdescent : baseEnd_3072327 < baseStart_3072327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072361 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 2, 3, 2]
def baseStart_3072361 : Nat := 118140960795 + 3072361 * 2 ^ 59
def prefixEnd_3072361 : Nat := 4983230072969 + 3 ^ 40 * 3072361 * 2
def baseEnd_3072361 : Nat := 1577597937128359107157975

theorem tailTrace_3072361 : CollatzResearch.WordTrace tailWord_3072361 prefixEnd_3072361 1577597937128359107157975 := by
  unfold tailWord_3072361
  simp only [CollatzResearch.WordTrace]
  refine ⟨112058211622368289329016937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74705474414912192886011291 112058211622368289329016937)
  ·
    refine ⟨84043658716776216996762703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112058211622368289329016937 84043658716776216996762703)
    ·
      refine ⟨126065488075164325495144055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84043658716776216996762703 126065488075164325495144055)
      ·
        refine ⟨189098232112746488242716083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126065488075164325495144055 189098232112746488242716083)
        ·
          refine ⟨283647348169119732364074125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189098232112746488242716083 283647348169119732364074125)
          ·
            refine ⟨106367755563419899636527797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283647348169119732364074125 106367755563419899636527797)
            ·
              refine ⟨9971977084070615590924481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106367755563419899636527797 9971977084070615590924481)
              ·
                refine ⟨7478982813052961693193361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9971977084070615590924481 7478982813052961693193361)
                ·
                  refine ⟨5609237109789721269895021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7478982813052961693193361 5609237109789721269895021)
                  ·
                    refine ⟨2103463916171145476210633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5609237109789721269895021 2103463916171145476210633)
                    ·
                      refine ⟨1577597937128359107157975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103463916171145476210633 1577597937128359107157975)
                      ·
                        rfl

theorem cell23_3072361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 3, 2].length) (baseStart_3072361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072361 prefixEnd_3072361 := by exact prefixLift 3072361
  have htrace : WordTrace (prefixWord ++ tailWord_3072361) baseStart_3072361 baseEnd_3072361 := by
    simpa [prefixWord, tailWord_3072361, baseEnd_3072361] using wordTrace_append hprefix tailTrace_3072361
  have hstable : (prefixWord ++ tailWord_3072361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072361).length < 2 ^ (prefixWord ++ tailWord_3072361).sum := by decide
  have hdescent : baseEnd_3072361 < baseStart_3072361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072367 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 5, 6]
def baseStart_3072367 : Nat := 118140960795 + 3072367 * 2 ^ 59
def prefixEnd_3072367 : Nat := 4983230072969 + 3 ^ 40 * 3072367 * 2
def baseEnd_3072367 : Nat := 525867006004095361227649

theorem tailTrace_3072367 : CollatzResearch.WordTrace tailWord_3072367 prefixEnd_3072367 525867006004095361227649 := by
  unfold tailWord_3072367
  simp only [CollatzResearch.WordTrace]
  refine ⟨112058430460346552353735355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74705620306897701569156903 112058430460346552353735355)
  ·
    refine ⟨168087645690519828530603033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112058430460346552353735355 168087645690519828530603033)
    ·
      refine ⟨126065734267889871397952275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168087645690519828530603033 126065734267889871397952275)
      ·
        refine ⟨189098601401834807096928413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126065734267889871397952275 189098601401834807096928413)
        ·
          refine ⟨70911975525688052661348155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189098601401834807096928413 70911975525688052661348155)
          ·
            refine ⟨106367963288532078992022233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70911975525688052661348155 106367963288532078992022233)
            ·
              refine ⟨79775972466399059244016675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106367963288532078992022233 79775972466399059244016675)
              ·
                refine ⟨119663958699598588866025013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79775972466399059244016675 119663958699598588866025013)
                ·
                  refine ⟨11218496128087367706189845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119663958699598588866025013 11218496128087367706189845)
                  ·
                    refine ⟨525867006004095361227649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11218496128087367706189845 525867006004095361227649)
                    ·
                      rfl

theorem cell23_3072367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_3072367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072367 prefixEnd_3072367 := by exact prefixLift 3072367
  have htrace : WordTrace (prefixWord ++ tailWord_3072367) baseStart_3072367 baseEnd_3072367 := by
    simpa [prefixWord, tailWord_3072367, baseEnd_3072367] using wordTrace_append hprefix tailTrace_3072367
  have hstable : (prefixWord ++ tailWord_3072367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072367).length < 2 ^ (prefixWord ++ tailWord_3072367).sum := by decide
  have hdescent : baseEnd_3072367 < baseStart_3072367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072368 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 3, 1, 3]
def baseStart_3072368 : Nat := 118140960795 + 3072368 * 2 ^ 59
def prefixEnd_3072368 : Nat := 4983230072969 + 3 ^ 40 * 3072368 * 2
def baseEnd_3072368 : Nat := 1577601531492940579770443

theorem tailTrace_3072368 : CollatzResearch.WordTrace tailWord_3072368 prefixEnd_3072368 1577601531492940579770443 := by
  unfold tailWord_3072368
  simp only [CollatzResearch.WordTrace]
  refine ⟨56029233466671464762260879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74705644622228619683014505 56029233466671464762260879)
  ·
    refine ⟨84043850200007197143391319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56029233466671464762260879 84043850200007197143391319)
    ·
      refine ⟨126065775300010795715086979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84043850200007197143391319 126065775300010795715086979)
      ·
        refine ⟨189098662950016193572630469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126065775300010795715086979 189098662950016193572630469)
        ·
          refine ⟨35455999303128036294868213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189098662950016193572630469 35455999303128036294868213)
          ·
            refine ⟨3323999934668253402643895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35455999303128036294868213 3323999934668253402643895)
            ·
              refine ⟨4985999902002380103965843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3323999934668253402643895 4985999902002380103965843)
              ·
                refine ⟨7478999853003570155948765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4985999902002380103965843 7478999853003570155948765)
                ·
                  refine ⟨2804624944876338808480787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7478999853003570155948765 2804624944876338808480787)
                  ·
                    refine ⟨4206937417314508212721181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2804624944876338808480787 4206937417314508212721181)
                    ·
                      refine ⟨1577601531492940579770443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4206937417314508212721181 1577601531492940579770443)
                      ·
                        rfl

theorem cell23_3072368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3, 1, 3].length) (baseStart_3072368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072368 prefixEnd_3072368 := by exact prefixLift 3072368
  have htrace : WordTrace (prefixWord ++ tailWord_3072368) baseStart_3072368 baseEnd_3072368 := by
    simpa [prefixWord, tailWord_3072368, baseEnd_3072368] using wordTrace_append hprefix tailTrace_3072368
  have hstable : (prefixWord ++ tailWord_3072368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072368).length < 2 ^ (prefixWord ++ tailWord_3072368).sum := by decide
  have hdescent : baseEnd_3072368 < baseStart_3072368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072418 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3072418 : Nat := 118140960795 + 3072418 * 2 ^ 59
def prefixEnd_3072418 : Nat := 4983230072969 + 3 ^ 40 * 3072418 * 2
def baseEnd_3072418 : Nat := 525875735175221794715071

theorem tailTrace_3072418 : CollatzResearch.WordTrace tailWord_3072418 prefixEnd_3072418 525875735175221794715071 := by
  unfold tailWord_3072418
  simp only [CollatzResearch.WordTrace]
  refine ⟨28015072645790447015960477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74706860388774525375894605 28015072645790447015960477)
  ·
    refine ⟨10505652242171417630985179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28015072645790447015960477 10505652242171417630985179)
    ·
      refine ⟨15758478363257126446477769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10505652242171417630985179 15758478363257126446477769)
      ·
        refine ⟨11818858772442844834858327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15758478363257126446477769 11818858772442844834858327)
        ·
          refine ⟨17728288158664267252287491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11818858772442844834858327 17728288158664267252287491)
          ·
            refine ⟨26592432237996400878431237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17728288158664267252287491 26592432237996400878431237)
            ·
              refine ⟨4986081044624325164705857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26592432237996400878431237 4986081044624325164705857)
              ·
                refine ⟨3739560783468243873529393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4986081044624325164705857 3739560783468243873529393)
                ·
                  refine ⟨2804670587601182905147045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3739560783468243873529393 2804670587601182905147045)
                  ·
                    refine ⟨525875735175221794715071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2804670587601182905147045 525875735175221794715071)
                    ·
                      rfl

theorem cell23_3072418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3072418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072418 prefixEnd_3072418 := by exact prefixLift 3072418
  have htrace : WordTrace (prefixWord ++ tailWord_3072418) baseStart_3072418 baseEnd_3072418 := by
    simpa [prefixWord, tailWord_3072418, baseEnd_3072418] using wordTrace_append hprefix tailTrace_3072418
  have hstable : (prefixWord ++ tailWord_3072418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072418).length < 2 ^ (prefixWord ++ tailWord_3072418).sum := by decide
  have hdescent : baseEnd_3072418 < baseStart_3072418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072441 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 1, 3, 3]
def baseStart_3072441 : Nat := 118140960795 + 3072441 * 2 ^ 59
def prefixEnd_3072441 : Nat := 4983230072969 + 3 ^ 40 * 3072441 * 2
def baseEnd_3072441 : Nat := 1577639015580718794157607

theorem tailTrace_3072441 : CollatzResearch.WordTrace tailWord_3072441 prefixEnd_3072441 1577639015580718794157607 := by
  unfold tailWord_3072441
  simp only [CollatzResearch.WordTrace]
  refine ⟨112061129462078462991929177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74707419641385641994619451 112061129462078462991929177)
  ·
    refine ⟨84045847096558847243946883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112061129462078462991929177 84045847096558847243946883)
    ·
      refine ⟨126068770644838270865920325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84045847096558847243946883 126068770644838270865920325)
      ·
        refine ⟨23637894495907175787360061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126068770644838270865920325 23637894495907175787360061)
        ·
          refine ⟨8864210435965190920260023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23637894495907175787360061 8864210435965190920260023)
          ·
            refine ⟨13296315653947786380390035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8864210435965190920260023 13296315653947786380390035)
            ·
              refine ⟨19944473480921679570585053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13296315653947786380390035 19944473480921679570585053)
              ·
                refine ⟨7479177555345629838969395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19944473480921679570585053 7479177555345629838969395)
                ·
                  refine ⟨11218766333018444758454093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7479177555345629838969395 11218766333018444758454093)
                  ·
                    refine ⟨4207037374881916784420285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11218766333018444758454093 4207037374881916784420285)
                    ·
                      refine ⟨1577639015580718794157607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4207037374881916784420285 1577639015580718794157607)
                      ·
                        rfl

theorem cell23_3072441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_3072441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072441 prefixEnd_3072441 := by exact prefixLift 3072441
  have htrace : WordTrace (prefixWord ++ tailWord_3072441) baseStart_3072441 baseEnd_3072441 := by
    simpa [prefixWord, tailWord_3072441, baseEnd_3072441] using wordTrace_append hprefix tailTrace_3072441
  have hstable : (prefixWord ++ tailWord_3072441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072441).length < 2 ^ (prefixWord ++ tailWord_3072441).sum := by decide
  have hdescent : baseEnd_3072441 < baseStart_3072441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072474 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_3072474 : Nat := 118140960795 + 3072474 * 2 ^ 59
def prefixEnd_3072474 : Nat := 4983230072969 + 3 ^ 40 * 3072474 * 2
def baseEnd_3072474 : Nat := 525885320147439055014985

theorem tailTrace_3072474 : CollatzResearch.WordTrace tailWord_3072474 prefixEnd_3072474 525885320147439055014985 := by
  unfold tailWord_3072474
  simp only [CollatzResearch.WordTrace]
  refine ⟨28015583267739727406970119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74708222047305939751920317 28015583267739727406970119)
  ·
    refine ⟨42023374901609591110455179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28015583267739727406970119 42023374901609591110455179)
    ·
      refine ⟨63035062352414386665682769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42023374901609591110455179 63035062352414386665682769)
      ·
        refine ⟨47276296764310789999262077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63035062352414386665682769 47276296764310789999262077)
        ·
          refine ⟨17728611286616546249723279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47276296764310789999262077 17728611286616546249723279)
          ·
            refine ⟨26592916929924819374584919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17728611286616546249723279 26592916929924819374584919)
            ·
              refine ⟨39889375394887229061877379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26592916929924819374584919 39889375394887229061877379)
              ·
                refine ⟨59834063092330843592816069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39889375394887229061877379 59834063092330843592816069)
                ·
                  refine ⟨11218886829812033173653013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59834063092330843592816069 11218886829812033173653013)
                  ·
                    refine ⟨525885320147439055014985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11218886829812033173653013 525885320147439055014985)
                    ·
                      rfl

theorem cell23_3072474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_3072474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072474 prefixEnd_3072474 := by exact prefixLift 3072474
  have htrace : WordTrace (prefixWord ++ tailWord_3072474) baseStart_3072474 baseEnd_3072474 := by
    simpa [prefixWord, tailWord_3072474, baseEnd_3072474] using wordTrace_append hprefix tailTrace_3072474
  have hstable : (prefixWord ++ tailWord_3072474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072474).length < 2 ^ (prefixWord ++ tailWord_3072474).sum := by decide
  have hdescent : baseEnd_3072474 < baseStart_3072474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072484 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_3072484 : Nat := 118140960795 + 3072484 * 2 ^ 59
def prefixEnd_3072484 : Nat := 4983230072969 + 3 ^ 40 * 3072484 * 2
def baseEnd_3072484 : Nat := 1577661095248862125919909

theorem tailTrace_3072484 : CollatzResearch.WordTrace tailWord_3072484 prefixEnd_3072484 1577661095248862125919909 := by
  unfold tailWord_3072484
  simp only [CollatzResearch.WordTrace]
  refine ⟨56031348900461340667872253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74708465200615120890496337 56031348900461340667872253)
  ·
    refine ⟨21011755837673002750452095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56031348900461340667872253 21011755837673002750452095)
    ·
      refine ⟨31517633756509504125678143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21011755837673002750452095 31517633756509504125678143)
      ·
        refine ⟨47276450634764256188517215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31517633756509504125678143 47276450634764256188517215)
        ·
          refine ⟨70914675952146384282775823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47276450634764256188517215 70914675952146384282775823)
          ·
            refine ⟨106372013928219576424163735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70914675952146384282775823 106372013928219576424163735)
            ·
              refine ⟨159558020892329364636245603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106372013928219576424163735 159558020892329364636245603)
              ·
                refine ⟨239337031338494046954368405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159558020892329364636245603 239337031338494046954368405)
                ·
                  refine ⟨11218923343991908450986019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 239337031338494046954368405 11218923343991908450986019)
                  ·
                    refine ⟨16828385015987862676479029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11218923343991908450986019 16828385015987862676479029)
                    ·
                      refine ⟨1577661095248862125919909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16828385015987862676479029 1577661095248862125919909)
                      ·
                        rfl

theorem cell23_3072484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_3072484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072484 prefixEnd_3072484 := by exact prefixLift 3072484
  have htrace : WordTrace (prefixWord ++ tailWord_3072484) baseStart_3072484 baseEnd_3072484 := by
    simpa [prefixWord, tailWord_3072484, baseEnd_3072484] using wordTrace_append hprefix tailTrace_3072484
  have hstable : (prefixWord ++ tailWord_3072484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072484).length < 2 ^ (prefixWord ++ tailWord_3072484).sum := by decide
  have hdescent : baseEnd_3072484 < baseStart_3072484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072504 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 7]
def baseStart_3072504 : Nat := 118140960795 + 3072504 * 2 ^ 59
def prefixEnd_3072504 : Nat := 4983230072969 + 3 ^ 40 * 3072504 * 2
def baseEnd_3072504 : Nat := 175296818317994671963313

theorem tailTrace_3072504 : CollatzResearch.WordTrace tailWord_3072504 prefixEnd_3072504 175296818317994671963313 := by
  unfold tailWord_3072504
  simp only [CollatzResearch.WordTrace]
  refine ⟨56031713630425112375736283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74708951507233483167648377 56031713630425112375736283)
  ·
    refine ⟨84047570445637668563604425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56031713630425112375736283 84047570445637668563604425)
    ·
      refine ⟨63035677834228251422703319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84047570445637668563604425 63035677834228251422703319)
      ·
        refine ⟨94553516751342377134054979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63035677834228251422703319 94553516751342377134054979)
        ·
          refine ⟨141830275127013565701082469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94553516751342377134054979 141830275127013565701082469)
          ·
            refine ⟨26593176586315043568952963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141830275127013565701082469 26593176586315043568952963)
            ·
              refine ⟨39889764879472565353429445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26593176586315043568952963 39889764879472565353429445)
              ·
                refine ⟨7479330914901106003768021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39889764879472565353429445 7479330914901106003768021)
                ·
                  refine ⟨175296818317994671963313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7479330914901106003768021 175296818317994671963313)
                  ·
                    rfl

theorem cell23_3072504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 7].length) (baseStart_3072504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072504 prefixEnd_3072504 := by exact prefixLift 3072504
  have htrace : WordTrace (prefixWord ++ tailWord_3072504) baseStart_3072504 baseEnd_3072504 := by
    simpa [prefixWord, tailWord_3072504, baseEnd_3072504] using wordTrace_append hprefix tailTrace_3072504
  have hstable : (prefixWord ++ tailWord_3072504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072504).length < 2 ^ (prefixWord ++ tailWord_3072504).sum := by decide
  have hdescent : baseEnd_3072504 < baseStart_3072504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072521 : List Nat := [1, 2, 1, 1, 3, 1, 2, 7, 5]
def baseStart_3072521 : Nat := 118140960795 + 3072521 * 2 ^ 59
def prefixEnd_3072521 : Nat := 4983230072969 + 3 ^ 40 * 3072521 * 2
def baseEnd_3072521 : Nat := 175297788225897609017471

theorem tailTrace_3072521 : CollatzResearch.WordTrace tailWord_3072521 prefixEnd_3072521 175297788225897609017471 := by
  unfold tailWord_3072521
  simp only [CollatzResearch.WordTrace]
  refine ⟨112064047301788636654841417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74709364867859091103227611 112064047301788636654841417)
  ·
    refine ⟨84048035476341477491131063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112064047301788636654841417 84048035476341477491131063)
    ·
      refine ⟨126072053214512216236696595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84048035476341477491131063 126072053214512216236696595)
      ·
        refine ⟨189108079821768324355044893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126072053214512216236696595 189108079821768324355044893)
        ·
          refine ⟨70915529933163121633141835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189108079821768324355044893 70915529933163121633141835)
          ·
            refine ⟨106373294899744682449712753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70915529933163121633141835 106373294899744682449712753)
            ·
              refine ⟨79779971174808511837284565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106373294899744682449712753 79779971174808511837284565)
              ·
                refine ⟨1869843074409574496186357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79779971174808511837284565 1869843074409574496186357)
                ·
                  refine ⟨175297788225897609017471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1869843074409574496186357 175297788225897609017471)
                  ·
                    rfl

theorem cell23_3072521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 5].length) (baseStart_3072521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072521 prefixEnd_3072521 := by exact prefixLift 3072521
  have htrace : WordTrace (prefixWord ++ tailWord_3072521) baseStart_3072521 baseEnd_3072521 := by
    simpa [prefixWord, tailWord_3072521, baseEnd_3072521] using wordTrace_append hprefix tailTrace_3072521
  have hstable : (prefixWord ++ tailWord_3072521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072521).length < 2 ^ (prefixWord ++ tailWord_3072521).sum := by decide
  have hdescent : baseEnd_3072521 < baseStart_3072521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072532 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_3072532 : Nat := 118140960795 + 3072532 * 2 ^ 59
def prefixEnd_3072532 : Nat := 4983230072969 + 3 ^ 40 * 3072532 * 2
def baseEnd_3072532 : Nat := 1577685742320277938119689

theorem tailTrace_3072532 : CollatzResearch.WordTrace tailWord_3072532 prefixEnd_3072532 1577685742320277938119689 := by
  unfold tailWord_3072532
  simp only [CollatzResearch.WordTrace]
  refine ⟨56032224252374392766745925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74709632336499190355661233 56032224252374392766745925)
  ·
    refine ⟨10506042047320198643764861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56032224252374392766745925 10506042047320198643764861)
    ·
      refine ⟨3939765767745074491411823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10506042047320198643764861 3939765767745074491411823)
      ·
        refine ⟨5909648651617611737117735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939765767745074491411823 5909648651617611737117735)
        ·
          refine ⟨8864472977426417605676603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909648651617611737117735 8864472977426417605676603)
          ·
            refine ⟨13296709466139626408514905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8864472977426417605676603 13296709466139626408514905)
            ·
              refine ⟨9972532099604719806386179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13296709466139626408514905 9972532099604719806386179)
              ·
                refine ⟨14958798149407079709579269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9972532099604719806386179 14958798149407079709579269)
                ·
                  refine ⟨2804774653013827445546113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14958798149407079709579269 2804774653013827445546113)
                  ·
                    refine ⟨2103580989760370584159585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2804774653013827445546113 2103580989760370584159585)
                    ·
                      refine ⟨1577685742320277938119689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103580989760370584159585 1577685742320277938119689)
                      ·
                        rfl

theorem cell23_3072532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_3072532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072532 prefixEnd_3072532 := by exact prefixLift 3072532
  have htrace : WordTrace (prefixWord ++ tailWord_3072532) baseStart_3072532 baseEnd_3072532 := by
    simpa [prefixWord, tailWord_3072532, baseEnd_3072532] using wordTrace_append hprefix tailTrace_3072532
  have hstable : (prefixWord ++ tailWord_3072532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072532).length < 2 ^ (prefixWord ++ tailWord_3072532).sum := by decide
  have hdescent : baseEnd_3072532 < baseStart_3072532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072588 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 2, 4, 2]
def baseStart_3072588 : Nat := 118140960795 + 3072588 * 2 ^ 59
def prefixEnd_3072588 : Nat := 4983230072969 + 3 ^ 40 * 3072588 * 2
def baseEnd_3072588 : Nat := 1577714497236929719019431

theorem tailTrace_3072588 : CollatzResearch.WordTrace tailWord_3072588 prefixEnd_3072588 1577714497236929719019431 := by
  unfold tailWord_3072588
  simp only [CollatzResearch.WordTrace]
  refine ⟨56033245496272953548765209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74710993995030604731686945 56033245496272953548765209)
  ·
    refine ⟨42024934122204715161573907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56033245496272953548765209 42024934122204715161573907)
    ·
      refine ⟨63037401183307072742360861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42024934122204715161573907 63037401183307072742360861)
      ·
        refine ⟨23639025443740152278385323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63037401183307072742360861 23639025443740152278385323)
        ·
          refine ⟨35458538165610228417577985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23639025443740152278385323 35458538165610228417577985)
          ·
            refine ⟨26593903624207671313183489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35458538165610228417577985 26593903624207671313183489)
            ·
              refine ⟨19945427718155753484887617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26593903624207671313183489 19945427718155753484887617)
              ·
                refine ⟨14959070788616815113665713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19945427718155753484887617 14959070788616815113665713)
                ·
                  refine ⟨11219303091462611335249285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14959070788616815113665713 11219303091462611335249285)
                  ·
                    refine ⟨2103619329649239625359241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11219303091462611335249285 2103619329649239625359241)
                    ·
                      refine ⟨1577714497236929719019431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103619329649239625359241 1577714497236929719019431)
                      ·
                        rfl

theorem cell23_3072588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_3072588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072588 prefixEnd_3072588 := by exact prefixLift 3072588
  have htrace : WordTrace (prefixWord ++ tailWord_3072588) baseStart_3072588 baseEnd_3072588 := by
    simpa [prefixWord, tailWord_3072588, baseEnd_3072588] using wordTrace_append hprefix tailTrace_3072588
  have hstable : (prefixWord ++ tailWord_3072588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072588).length < 2 ^ (prefixWord ++ tailWord_3072588).sum := by decide
  have hdescent : baseEnd_3072588 < baseStart_3072588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072611 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 6]
def baseStart_3072611 : Nat := 118140960795 + 3072611 * 2 ^ 59
def prefixEnd_3072611 : Nat := 4983230072969 + 3 ^ 40 * 3072611 * 2
def baseEnd_3072611 : Nat := 175302923032442569892425

theorem tailTrace_3072611 : CollatzResearch.WordTrace tailWord_3072611 prefixEnd_3072611 175302923032442569892425 := by
  unfold tailWord_3072611
  simp only [CollatzResearch.WordTrace]
  refine ⟨112067329871462582025617687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74711553247641721350411791 112067329871462582025617687)
  ·
    refine ⟨168100994807193873038426531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112067329871462582025617687 168100994807193873038426531)
    ·
      refine ⟨252151492210790809557639797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168100994807193873038426531 252151492210790809557639797)
      ·
        refine ⟨23639202394761638396028731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 252151492210790809557639797 23639202394761638396028731)
        ·
          refine ⟨35458803592142457594043097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23639202394761638396028731 35458803592142457594043097)
          ·
            refine ⟨26594102694106843195532323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35458803592142457594043097 26594102694106843195532323)
            ·
              refine ⟨39891154041160264793298485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26594102694106843195532323 39891154041160264793298485)
              ·
                refine ⟨3739795691358774824371733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39891154041160264793298485 3739795691358774824371733)
                ·
                  refine ⟨175302923032442569892425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3739795691358774824371733 175302923032442569892425)
                  ·
                    rfl

theorem cell23_3072611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 6].length) (baseStart_3072611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072611 prefixEnd_3072611 := by exact prefixLift 3072611
  have htrace : WordTrace (prefixWord ++ tailWord_3072611) baseStart_3072611 baseEnd_3072611 := by
    simpa [prefixWord, tailWord_3072611, baseEnd_3072611] using wordTrace_append hprefix tailTrace_3072611
  have hstable : (prefixWord ++ tailWord_3072611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072611).length < 2 ^ (prefixWord ++ tailWord_3072611).sum := by decide
  have hdescent : baseEnd_3072611 < baseStart_3072611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072698 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5]
def baseStart_3072698 : Nat := 118140960795 + 3072698 * 2 ^ 59
def prefixEnd_3072698 : Nat := 4983230072969 + 3 ^ 40 * 3072698 * 2
def baseEnd_3072698 : Nat := 1577770980108924288643925

theorem tailTrace_3072698 : CollatzResearch.WordTrace tailWord_3072698 prefixEnd_3072698 1577770980108924288643925 := by
  unfold tailWord_3072698
  simp only [CollatzResearch.WordTrace]
  refine ⟨28017625755536848971008687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74713668681431597256023165 28017625755536848971008687)
  ·
    refine ⟨42026438633305273456513031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28017625755536848971008687 42026438633305273456513031)
    ·
      refine ⟨63039657949957910184769547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42026438633305273456513031 63039657949957910184769547)
      ·
        refine ⟨94559486924936865277154321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63039657949957910184769547 94559486924936865277154321)
        ·
          refine ⟨70919615193702648957865741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94559486924936865277154321 70919615193702648957865741)
          ·
            refine ⟨26594855697638493359199653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70919615193702648957865741 26594855697638493359199653)
            ·
              refine ⟨4986535443307217504849935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26594855697638493359199653 4986535443307217504849935)
              ·
                refine ⟨7479803164960826257274903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4986535443307217504849935 7479803164960826257274903)
                ·
                  refine ⟨11219704747441239385912355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7479803164960826257274903 11219704747441239385912355)
                  ·
                    refine ⟨16829557121161859078868533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11219704747441239385912355 16829557121161859078868533)
                    ·
                      refine ⟨1577770980108924288643925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16829557121161859078868533 1577770980108924288643925)
                      ·
                        rfl

theorem cell23_3072698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_3072698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072698 prefixEnd_3072698 := by exact prefixLift 3072698
  have htrace : WordTrace (prefixWord ++ tailWord_3072698) baseStart_3072698 baseEnd_3072698 := by
    simpa [prefixWord, tailWord_3072698, baseEnd_3072698] using wordTrace_append hprefix tailTrace_3072698
  have hstable : (prefixWord ++ tailWord_3072698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072698).length < 2 ^ (prefixWord ++ tailWord_3072698).sum := by decide
  have hdescent : baseEnd_3072698 < baseStart_3072698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072701 : List Nat := [1, 4, 1, 2, 1, 3, 11]
def baseStart_3072701 : Nat := 118140960795 + 3072701 * 2 ^ 59
def prefixEnd_3072701 : Nat := 4983230072969 + 3 ^ 40 * 3072701 * 2
def baseEnd_3072701 : Nat := 19478673093220836751931

theorem tailTrace_3072701 : CollatzResearch.WordTrace tailWord_3072701 prefixEnd_3072701 19478673093220836751931 := by
  unfold tailWord_3072701
  simp only [CollatzResearch.WordTrace]
  refine ⟨112070612441136527396393957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74713741627424351597595971 112070612441136527396393957)
  ·
    refine ⟨21013239832713098886823867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112070612441136527396393957 21013239832713098886823867)
    ·
      refine ⟨31519859749069648330235801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21013239832713098886823867 31519859749069648330235801)
      ·
        refine ⟨23639894811802236247676851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31519859749069648330235801 23639894811802236247676851)
        ·
          refine ⟨35459842217703354371515277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23639894811802236247676851 35459842217703354371515277)
          ·
            refine ⟨13297440831638757889318229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35459842217703354371515277 13297440831638757889318229)
            ·
              refine ⟨19478673093220836751931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13297440831638757889318229 19478673093220836751931)
              ·
                rfl

theorem cell23_3072701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 11].length) (baseStart_3072701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072701 prefixEnd_3072701 := by exact prefixLift 3072701
  have htrace : WordTrace (prefixWord ++ tailWord_3072701) baseStart_3072701 baseEnd_3072701 := by
    simpa [prefixWord, tailWord_3072701, baseEnd_3072701] using wordTrace_append hprefix tailTrace_3072701
  have hstable : (prefixWord ++ tailWord_3072701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072701).length < 2 ^ (prefixWord ++ tailWord_3072701).sum := by decide
  have hdescent : baseEnd_3072701 < baseStart_3072701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072708 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3072708 : Nat := 118140960795 + 3072708 * 2 ^ 59
def prefixEnd_3072708 : Nat := 4983230072969 + 3 ^ 40 * 3072708 * 2
def baseEnd_3072708 : Nat := 1577776114915469249518879

theorem tailTrace_3072708 : CollatzResearch.WordTrace tailWord_3072708 prefixEnd_3072708 1577776114915469249518879 := by
  unfold tailWord_3072708
  simp only [CollatzResearch.WordTrace]
  refine ⟨56035433876055583795949389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74713911834740778394599185 56035433876055583795949389)
  ·
    refine ⟨21013287703520843923481021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56035433876055583795949389 21013287703520843923481021)
    ·
      refine ⟨7879982888820316471305383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21013287703520843923481021 7879982888820316471305383)
      ·
        refine ⟨11819974333230474706958075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7879982888820316471305383 11819974333230474706958075)
        ·
          refine ⟨17729961499845712060437113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11819974333230474706958075 17729961499845712060437113)
          ·
            refine ⟨13297471124884284045327835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17729961499845712060437113 13297471124884284045327835)
            ·
              refine ⟨19946206687326426067991753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13297471124884284045327835 19946206687326426067991753)
              ·
                refine ⟨14959655015494819550993815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19946206687326426067991753 14959655015494819550993815)
                ·
                  refine ⟨22439482523242229326490723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14959655015494819550993815 22439482523242229326490723)
                  ·
                    refine ⟨33659223784863343989736085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22439482523242229326490723 33659223784863343989736085)
                    ·
                      refine ⟨1577776114915469249518879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33659223784863343989736085 1577776114915469249518879)
                      ·
                        rfl

theorem cell23_3072708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3072708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072708 prefixEnd_3072708 := by exact prefixLift 3072708
  have htrace : WordTrace (prefixWord ++ tailWord_3072708) baseStart_3072708 baseEnd_3072708 := by
    simpa [prefixWord, tailWord_3072708, baseEnd_3072708] using wordTrace_append hprefix tailTrace_3072708
  have hstable : (prefixWord ++ tailWord_3072708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072708).length < 2 ^ (prefixWord ++ tailWord_3072708).sum := by decide
  have hdescent : baseEnd_3072708 < baseStart_3072708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072712 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 3, 2, 2]
def baseStart_3072712 : Nat := 118140960795 + 3072712 * 2 ^ 59
def prefixEnd_3072712 : Nat := 4983230072969 + 3 ^ 40 * 3072712 * 2
def baseEnd_3072712 : Nat := 1577778168838087233868861

theorem tailTrace_3072712 : CollatzResearch.WordTrace tailWord_3072712 prefixEnd_3072712 1577778168838087233868861 := by
  unfold tailWord_3072712
  simp only [CollatzResearch.WordTrace]
  refine ⟨56035506822048338137522195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74714009096064450850029593 56035506822048338137522195)
  ·
    refine ⟨84053260233072507206283293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56035506822048338137522195 84053260233072507206283293)
    ·
      refine ⟨31519972587402190202356235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84053260233072507206283293 31519972587402190202356235)
      ·
        refine ⟨47279958881103285303534353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31519972587402190202356235 47279958881103285303534353)
        ·
          refine ⟨35459969160827463977650765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47279958881103285303534353 35459969160827463977650765)
          ·
            refine ⟨13297488435310298991619037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35459969160827463977650765 13297488435310298991619037)
            ·
              refine ⟨4986558163241362121857139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13297488435310298991619037 4986558163241362121857139)
              ·
                refine ⟨7479837244862043182785709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4986558163241362121857139 7479837244862043182785709)
                ·
                  refine ⟨2804938966823266193544641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7479837244862043182785709 2804938966823266193544641)
                  ·
                    refine ⟨2103704225117449645158481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2804938966823266193544641 2103704225117449645158481)
                    ·
                      refine ⟨1577778168838087233868861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103704225117449645158481 1577778168838087233868861)
                      ·
                        rfl

theorem cell23_3072712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_3072712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072712 prefixEnd_3072712 := by exact prefixLift 3072712
  have htrace : WordTrace (prefixWord ++ tailWord_3072712) baseStart_3072712 baseEnd_3072712 := by
    simpa [prefixWord, tailWord_3072712, baseEnd_3072712] using wordTrace_append hprefix tailTrace_3072712
  have hstable : (prefixWord ++ tailWord_3072712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072712).length < 2 ^ (prefixWord ++ tailWord_3072712).sum := by decide
  have hdescent : baseEnd_3072712 < baseStart_3072712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072718 : List Nat := [4, 1, 1, 1, 3, 3, 2, 8]
def baseStart_3072718 : Nat := 118140960795 + 3072718 * 2 ^ 59
def prefixEnd_3072718 : Nat := 4983230072969 + 3 ^ 40 * 3072718 * 2
def baseEnd_3072718 : Nat := 58436342582296822607179

theorem tailTrace_3072718 : CollatzResearch.WordTrace tailWord_3072718 prefixEnd_3072718 58436342582296822607179 := by
  unfold tailWord_3072718
  simp only [CollatzResearch.WordTrace]
  refine ⟨14008904060259367412470351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74714154988049959533175205 14008904060259367412470351)
  ·
    refine ⟨21013356090389051118705527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14008904060259367412470351 21013356090389051118705527)
    ·
      refine ⟨31520034135583576678058291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21013356090389051118705527 31520034135583576678058291)
      ·
        refine ⟨47280051203375365017087437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31520034135583576678058291 47280051203375365017087437)
        ·
          refine ⟨17730019201265761881407789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47280051203375365017087437 17730019201265761881407789)
          ·
            refine ⟨6648757200474660705527921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17730019201265761881407789 6648757200474660705527921)
            ·
              refine ⟨4986567900355995529145941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6648757200474660705527921 4986567900355995529145941)
              ·
                refine ⟨58436342582296822607179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4986567900355995529145941 58436342582296822607179)
                ·
                  rfl

theorem cell23_3072718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_3072718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072718 prefixEnd_3072718 := by exact prefixLift 3072718
  have htrace : WordTrace (prefixWord ++ tailWord_3072718) baseStart_3072718 baseEnd_3072718 := by
    simpa [prefixWord, tailWord_3072718, baseEnd_3072718] using wordTrace_append hprefix tailTrace_3072718
  have hstable : (prefixWord ++ tailWord_3072718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072718).length < 2 ^ (prefixWord ++ tailWord_3072718).sum := by decide
  have hdescent : baseEnd_3072718 < baseStart_3072718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072721 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_3072721 : Nat := 118140960795 + 3072721 * 2 ^ 59
def prefixEnd_3072721 : Nat := 4983230072969 + 3 ^ 40 * 3072721 * 2
def baseEnd_3072721 : Nat := 1577782790163977698656319

theorem tailTrace_3072721 : CollatzResearch.WordTrace tailWord_3072721 prefixEnd_3072721 1577782790163977698656319 := by
  unfold tailWord_3072721
  simp only [CollatzResearch.WordTrace]
  refine ⟨112071341901064070812122017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74714227934042713874748011 112071341901064070812122017)
  ·
    refine ⟨84053506425798053109091513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112071341901064070812122017 84053506425798053109091513)
    ·
      refine ⟨63040129819348539831818635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84053506425798053109091513 63040129819348539831818635)
      ·
        refine ⟨94560194729022809747727953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63040129819348539831818635 94560194729022809747727953)
        ·
          refine ⟨70920146046767107310795965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94560194729022809747727953 70920146046767107310795965)
          ·
            refine ⟨26595054767537665241548487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70920146046767107310795965 26595054767537665241548487)
            ·
              refine ⟨39892582151306497862322731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26595054767537665241548487 39892582151306497862322731)
              ·
                refine ⟨59838873226959746793484097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39892582151306497862322731 59838873226959746793484097)
                ·
                  refine ⟨44879154920219810095113073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59838873226959746793484097 44879154920219810095113073)
                  ·
                    refine ⟨33659366190164857571334805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44879154920219810095113073 33659366190164857571334805)
                    ·
                      refine ⟨1577782790163977698656319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33659366190164857571334805 1577782790163977698656319)
                      ·
                        rfl

theorem cell23_3072721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_3072721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072721 prefixEnd_3072721 := by exact prefixLift 3072721
  have htrace : WordTrace (prefixWord ++ tailWord_3072721) baseStart_3072721 baseEnd_3072721 := by
    simpa [prefixWord, tailWord_3072721, baseEnd_3072721] using wordTrace_append hprefix tailTrace_3072721
  have hstable : (prefixWord ++ tailWord_3072721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072721).length < 2 ^ (prefixWord ++ tailWord_3072721).sum := by decide
  have hdescent : baseEnd_3072721 < baseStart_3072721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072722 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_3072722 : Nat := 118140960795 + 3072722 * 2 ^ 59
def prefixEnd_3072722 : Nat := 4983230072969 + 3 ^ 40 * 3072722 * 2
def baseEnd_3072722 : Nat := 525927767881544064914605

theorem tailTrace_3072722 : CollatzResearch.WordTrace tailWord_3072722 prefixEnd_3072722 525927767881544064914605 := by
  unfold tailWord_3072722
  simp only [CollatzResearch.WordTrace]
  refine ⟨28017844593515111995727105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74714252249373631988605613 28017844593515111995727105)
  ·
    refine ⟨21013383445136333996795329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28017844593515111995727105 21013383445136333996795329)
    ·
      refine ⟨15760037583852250497596497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21013383445136333996795329 15760037583852250497596497)
      ·
        refine ⟨11820028187889187873197373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15760037583852250497596497 11820028187889187873197373)
        ·
          refine ⟨4432510570458445452449015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11820028187889187873197373 4432510570458445452449015)
          ·
            refine ⟨6648765855687668178673523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4432510570458445452449015 6648765855687668178673523)
            ·
              refine ⟨9973148783531502268010285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648765855687668178673523 9973148783531502268010285)
              ·
                refine ⟨3739930793824313350503857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9973148783531502268010285 3739930793824313350503857)
                ·
                  refine ⟨2804948095368235012877893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3739930793824313350503857 2804948095368235012877893)
                  ·
                    refine ⟨525927767881544064914605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2804948095368235012877893 525927767881544064914605)
                    ·
                      rfl

theorem cell23_3072722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_3072722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072722 prefixEnd_3072722 := by exact prefixLift 3072722
  have htrace : WordTrace (prefixWord ++ tailWord_3072722) baseStart_3072722 baseEnd_3072722 := by
    simpa [prefixWord, tailWord_3072722, baseEnd_3072722] using wordTrace_append hprefix tailTrace_3072722
  have hstable : (prefixWord ++ tailWord_3072722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072722).length < 2 ^ (prefixWord ++ tailWord_3072722).sum := by decide
  have hdescent : baseEnd_3072722 < baseStart_3072722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072732 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3072732 : Nat := 118140960795 + 3072732 * 2 ^ 59
def prefixEnd_3072732 : Nat := 4983230072969 + 3 ^ 40 * 3072732 * 2
def baseEnd_3072732 : Nat := 1577788438451177155618769

theorem tailTrace_3072732 : CollatzResearch.WordTrace tailWord_3072732 prefixEnd_3072732 1577788438451177155618769 := by
  unfold tailWord_3072732
  simp only [CollatzResearch.WordTrace]
  refine ⟨56035871552012109845386225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74714495402682813127181633 56035871552012109845386225)
  ·
    refine ⟨42026903664009082384039669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56035871552012109845386225 42026903664009082384039669)
    ·
      refine ⟨3940022218500851473503719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42026903664009082384039669 3940022218500851473503719)
      ·
        refine ⟨5910033327751277210255579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3940022218500851473503719 5910033327751277210255579)
        ·
          refine ⟨8865049991626915815383369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5910033327751277210255579 8865049991626915815383369)
          ·
            refine ⟨6648787493720186861537527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8865049991626915815383369 6648787493720186861537527)
            ·
              refine ⟨9973181240580280292306291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648787493720186861537527 9973181240580280292306291)
              ·
                refine ⟨14959771860870420438459437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9973181240580280292306291 14959771860870420438459437)
                ·
                  refine ⟨5609914447826407664422289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14959771860870420438459437 5609914447826407664422289)
                  ·
                    refine ⟨4207435835869805748316717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5609914447826407664422289 4207435835869805748316717)
                    ·
                      refine ⟨1577788438451177155618769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4207435835869805748316717 1577788438451177155618769)
                      ·
                        rfl

theorem cell23_3072732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3072732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072732 prefixEnd_3072732 := by exact prefixLift 3072732
  have htrace : WordTrace (prefixWord ++ tailWord_3072732) baseStart_3072732 baseEnd_3072732 := by
    simpa [prefixWord, tailWord_3072732, baseEnd_3072732] using wordTrace_append hprefix tailTrace_3072732
  have hstable : (prefixWord ++ tailWord_3072732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072732).length < 2 ^ (prefixWord ++ tailWord_3072732).sum := by decide
  have hdescent : baseEnd_3072732 < baseStart_3072732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072756 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3072756 : Nat := 118140960795 + 3072756 * 2 ^ 59
def prefixEnd_3072756 : Nat := 4983230072969 + 3 ^ 40 * 3072756 * 2
def baseEnd_3072756 : Nat := 525933587328961687239553

theorem tailTrace_3072756 : CollatzResearch.WordTrace tailWord_3072756 prefixEnd_3072756 525933587328961687239553 := by
  unfold tailWord_3072756
  simp only [CollatzResearch.WordTrace]
  refine ⟨56036309227968635894823061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74715078970624847859764081 56036309227968635894823061)
  ·
    refine ⟨2626701995061029807569831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56036309227968635894823061 2626701995061029807569831)
    ·
      refine ⟨3940052992591544711354747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2626701995061029807569831 3940052992591544711354747)
      ·
        refine ⟨5910079488887317067032121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3940052992591544711354747 5910079488887317067032121)
        ·
          refine ⟨4432559616665487800274091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5910079488887317067032121 4432559616665487800274091)
          ·
            refine ⟨6648839424998231700411137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4432559616665487800274091 6648839424998231700411137)
            ·
              refine ⟨4986629568748673775308353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6648839424998231700411137 4986629568748673775308353)
              ·
                refine ⟨3739972176561505331481265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4986629568748673775308353 3739972176561505331481265)
                ·
                  refine ⟨2804979132421128998610949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3739972176561505331481265 2804979132421128998610949)
                  ·
                    refine ⟨525933587328961687239553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2804979132421128998610949 525933587328961687239553)
                    ·
                      rfl

theorem cell23_3072756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3072756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072756 prefixEnd_3072756 := by exact prefixLift 3072756
  have htrace : WordTrace (prefixWord ++ tailWord_3072756) baseStart_3072756 baseEnd_3072756 := by
    simpa [prefixWord, tailWord_3072756, baseEnd_3072756] using wordTrace_append hprefix tailTrace_3072756
  have hstable : (prefixWord ++ tailWord_3072756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072756).length < 2 ^ (prefixWord ++ tailWord_3072756).sum := by decide
  have hdescent : baseEnd_3072756 < baseStart_3072756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072757 : List Nat := [1, 3, 6, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3072757 : Nat := 118140960795 + 3072757 * 2 ^ 59
def prefixEnd_3072757 : Nat := 4983230072969 + 3 ^ 40 * 3072757 * 2
def baseEnd_3072757 : Nat := 1577801275467539557806155

theorem tailTrace_3072757 : CollatzResearch.WordTrace tailWord_3072757 prefixEnd_3072757 1577801275467539557806155 := by
  unfold tailWord_3072757
  simp only [CollatzResearch.WordTrace]
  refine ⟨112072654928933648960432525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74715103285955765973621683 112072654928933648960432525)
  ·
    refine ⟨42027245598350118360162197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112072654928933648960432525 42027245598350118360162197)
    ·
      refine ⟨1970027137422661798132603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42027245598350118360162197 1970027137422661798132603)
      ·
        refine ⟨2955040706133992697198905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1970027137422661798132603 2955040706133992697198905)
        ·
          refine ⟨2216280529600494522899179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2955040706133992697198905 2216280529600494522899179)
          ·
            refine ⟨3324420794400741784348769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216280529600494522899179 3324420794400741784348769)
            ·
              refine ⟨2493315595800556338261577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3324420794400741784348769 2493315595800556338261577)
              ·
                refine ⟨1869986696850417253696183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2493315595800556338261577 1869986696850417253696183)
                ·
                  refine ⟨2804980045275625880544275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869986696850417253696183 2804980045275625880544275)
                  ·
                    refine ⟨4207470067913438820816413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2804980045275625880544275 4207470067913438820816413)
                    ·
                      refine ⟨1577801275467539557806155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4207470067913438820816413 1577801275467539557806155)
                      ·
                        rfl

theorem cell23_3072757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3072757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072757 prefixEnd_3072757 := by exact prefixLift 3072757
  have htrace : WordTrace (prefixWord ++ tailWord_3072757) baseStart_3072757 baseEnd_3072757 := by
    simpa [prefixWord, tailWord_3072757, baseEnd_3072757] using wordTrace_append hprefix tailTrace_3072757
  have hstable : (prefixWord ++ tailWord_3072757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072757).length < 2 ^ (prefixWord ++ tailWord_3072757).sum := by decide
  have hdescent : baseEnd_3072757 < baseStart_3072757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072761 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 3, 8]
def baseStart_3072761 : Nat := 118140960795 + 3072761 * 2 ^ 59
def prefixEnd_3072761 : Nat := 4983230072969 + 3 ^ 40 * 3072761 * 2
def baseEnd_3072761 : Nat := 525934443130052514052045

theorem tailTrace_3072761 : CollatzResearch.WordTrace tailWord_3072761 prefixEnd_3072761 525934443130052514052045 := by
  unfold tailWord_3072761
  simp only [CollatzResearch.WordTrace]
  refine ⟨112072800820919157643578137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74715200547279438429052091 112072800820919157643578137)
  ·
    refine ⟨84054600615689368232683603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112072800820919157643578137 84054600615689368232683603)
    ·
      refine ⟨126081900923534052349025405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84054600615689368232683603 126081900923534052349025405)
      ·
        refine ⟨47280712846325269630884527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126081900923534052349025405 47280712846325269630884527)
        ·
          refine ⟨70921069269487904446326791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47280712846325269630884527 70921069269487904446326791)
          ·
            refine ⟨106381603904231856669490187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70921069269487904446326791 106381603904231856669490187)
            ·
              refine ⟨159572405856347785004235281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106381603904231856669490187 159572405856347785004235281)
              ·
                refine ⟨119679304392260838753176461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159572405856347785004235281 119679304392260838753176461)
                ·
                  refine ⟨44879739147097814532441173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119679304392260838753176461 44879739147097814532441173)
                  ·
                    refine ⟨525934443130052514052045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44879739147097814532441173 525934443130052514052045)
                    ·
                      rfl

theorem cell23_3072761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_3072761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072761 prefixEnd_3072761 := by exact prefixLift 3072761
  have htrace : WordTrace (prefixWord ++ tailWord_3072761) baseStart_3072761 baseEnd_3072761 := by
    simpa [prefixWord, tailWord_3072761, baseEnd_3072761] using wordTrace_append hprefix tailTrace_3072761
  have hstable : (prefixWord ++ tailWord_3072761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072761).length < 2 ^ (prefixWord ++ tailWord_3072761).sum := by decide
  have hdescent : baseEnd_3072761 < baseStart_3072761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072778 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_3072778 : Nat := 118140960795 + 3072778 * 2 ^ 59
def prefixEnd_3072778 : Nat := 4983230072969 + 3 ^ 40 * 3072778 * 2
def baseEnd_3072778 : Nat := 525937352853761325214519

theorem tailTrace_3072778 : CollatzResearch.WordTrace tailWord_3072778 prefixEnd_3072778 525937352853761325214519 := by
  unfold tailWord_3072778
  simp only [CollatzResearch.WordTrace]
  refine ⟨28018355215464392386736747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74715613907905046364631325 28018355215464392386736747)
  ·
    refine ⟨42027532823196588580105121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28018355215464392386736747 42027532823196588580105121)
    ·
      refine ⟨31520649617397441435078841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42027532823196588580105121 31520649617397441435078841)
      ·
        refine ⟨23640487213048081076309131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31520649617397441435078841 23640487213048081076309131)
        ·
          refine ⟨35460730819572121614463697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23640487213048081076309131 35460730819572121614463697)
          ·
            refine ⟨26595548114679091210847773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35460730819572121614463697 26595548114679091210847773)
            ·
              refine ⟨9973330543004659204067915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26595548114679091210847773 9973330543004659204067915)
              ·
                refine ⟨14959995814506988806101873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9973330543004659204067915 14959995814506988806101873)
                ·
                  refine ⟨11219996860880241604576405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14959995814506988806101873 11219996860880241604576405)
                  ·
                    refine ⟨525937352853761325214519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11219996860880241604576405 525937352853761325214519)
                    ·
                      rfl

theorem cell23_3072778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_3072778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072778 prefixEnd_3072778 := by exact prefixLift 3072778
  have htrace : WordTrace (prefixWord ++ tailWord_3072778) baseStart_3072778 baseEnd_3072778 := by
    simpa [prefixWord, tailWord_3072778, baseEnd_3072778] using wordTrace_append hprefix tailTrace_3072778
  have hstable : (prefixWord ++ tailWord_3072778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072778).length < 2 ^ (prefixWord ++ tailWord_3072778).sum := by decide
  have hdescent : baseEnd_3072778 < baseStart_3072778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072785 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 1, 4, 2]
def baseStart_3072785 : Nat := 118140960795 + 3072785 * 2 ^ 59
def prefixEnd_3072785 : Nat := 4983230072969 + 3 ^ 40 * 3072785 * 2
def baseEnd_3072785 : Nat := 1577815652925865448256025

theorem tailTrace_3072785 : CollatzResearch.WordTrace tailWord_3072785 prefixEnd_3072785 1577815652925865448256025 := by
  unfold tailWord_3072785
  simp only [CollatzResearch.WordTrace]
  refine ⟨112073676172832209742451809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74715784115221473161634539 112073676172832209742451809)
  ·
    refine ⟨84055257129624157306838857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112073676172832209742451809 84055257129624157306838857)
    ·
      refine ⟨63041442847218117980129143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84055257129624157306838857 63041442847218117980129143)
      ·
        refine ⟨94562164270827176970193715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63041442847218117980129143 94562164270827176970193715)
        ·
          refine ⟨141843246406240765455290573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94562164270827176970193715 141843246406240765455290573)
          ·
            refine ⟨53191217402340287045733965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141843246406240765455290573 53191217402340287045733965)
            ·
              refine ⟨19946706525877607642150237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53191217402340287045733965 19946706525877607642150237)
              ·
                refine ⟨7480014947204102865806339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19946706525877607642150237 7480014947204102865806339)
                ·
                  refine ⟨11220022420806154298709509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480014947204102865806339 11220022420806154298709509)
                  ·
                    refine ⟨2103754203901153931008033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11220022420806154298709509 2103754203901153931008033)
                    ·
                      refine ⟨1577815652925865448256025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103754203901153931008033 1577815652925865448256025)
                      ·
                        rfl

theorem cell23_3072785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 4, 2].length) (baseStart_3072785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072785 prefixEnd_3072785 := by exact prefixLift 3072785
  have htrace : WordTrace (prefixWord ++ tailWord_3072785) baseStart_3072785 baseEnd_3072785 := by
    simpa [prefixWord, tailWord_3072785, baseEnd_3072785] using wordTrace_append hprefix tailTrace_3072785
  have hstable : (prefixWord ++ tailWord_3072785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072785).length < 2 ^ (prefixWord ++ tailWord_3072785).sum := by decide
  have hdescent : baseEnd_3072785 < baseStart_3072785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072802 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_3072802 : Nat := 118140960795 + 3072802 * 2 ^ 59
def prefixEnd_3072802 : Nat := 4983230072969 + 3 ^ 40 * 3072802 * 2
def baseEnd_3072802 : Nat := 1577824382096991881743447

theorem tailTrace_3072802 : CollatzResearch.WordTrace tailWord_3072802 prefixEnd_3072802 1577824382096991881743447 := by
  unfold tailWord_3072802
  simp only [CollatzResearch.WordTrace]
  refine ⟨28018574053442655411455165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74716197475847081097213773 28018574053442655411455165)
  ·
    refine ⟨10506965270040995779295687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28018574053442655411455165 10506965270040995779295687)
    ·
      refine ⟨15760447905061493668943531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10506965270040995779295687 15760447905061493668943531)
      ·
        refine ⟨23640671857592240503415297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15760447905061493668943531 23640671857592240503415297)
        ·
          refine ⟨17730503893194180377561473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23640671857592240503415297 17730503893194180377561473)
          ·
            refine ⟨13297877919895635283171105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17730503893194180377561473 13297877919895635283171105)
            ·
              refine ⟨9973408439921726462378329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13297877919895635283171105 9973408439921726462378329)
              ·
                refine ⟨7480056329941294846783747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9973408439921726462378329 7480056329941294846783747)
                ·
                  refine ⟨11220084494911942270175621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480056329941294846783747 11220084494911942270175621)
                  ·
                    refine ⟨2103765842795989175657929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11220084494911942270175621 2103765842795989175657929)
                    ·
                      refine ⟨1577824382096991881743447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103765842795989175657929 1577824382096991881743447)
                      ·
                        rfl

theorem cell23_3072802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_3072802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072802 prefixEnd_3072802 := by exact prefixLift 3072802
  have htrace : WordTrace (prefixWord ++ tailWord_3072802) baseStart_3072802 baseEnd_3072802 := by
    simpa [prefixWord, tailWord_3072802, baseEnd_3072802] using wordTrace_append hprefix tailTrace_3072802
  have hstable : (prefixWord ++ tailWord_3072802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072802).length < 2 ^ (prefixWord ++ tailWord_3072802).sum := by decide
  have hdescent : baseEnd_3072802 < baseStart_3072802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072808 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 9]
def baseStart_3072808 : Nat := 118140960795 + 3072808 * 2 ^ 59
def prefixEnd_3072808 : Nat := 4983230072969 + 3 ^ 40 * 3072808 * 2
def baseEnd_3072808 : Nat := 175314162553435428696491

theorem tailTrace_3072808 : CollatzResearch.WordTrace tailWord_3072808 prefixEnd_3072808 175314162553435428696491 := by
  unfold tailWord_3072808
  simp only [CollatzResearch.WordTrace]
  refine ⟨56037257525874442335269539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74716343367832589780359385 56037257525874442335269539)
  ·
    refine ⟨84055886288811663502904309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56037257525874442335269539 84055886288811663502904309)
    ·
      refine ⟨7880239339576093453397279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84055886288811663502904309 7880239339576093453397279)
      ·
        refine ⟨11820359009364140180095919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7880239339576093453397279 11820359009364140180095919)
        ·
          refine ⟨17730538514046210270143879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11820359009364140180095919 17730538514046210270143879)
          ·
            refine ⟨26595807771069315405215819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17730538514046210270143879 26595807771069315405215819)
            ·
              refine ⟨39893711656603973107823729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26595807771069315405215819 39893711656603973107823729)
              ·
                refine ⟨29920283742452979830867797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39893711656603973107823729 29920283742452979830867797)
                ·
                  refine ⟨175314162553435428696491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29920283742452979830867797 175314162553435428696491)
                  ·
                    rfl

theorem cell23_3072808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 9].length) (baseStart_3072808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072808 prefixEnd_3072808 := by exact prefixLift 3072808
  have htrace : WordTrace (prefixWord ++ tailWord_3072808) baseStart_3072808 baseEnd_3072808 := by
    simpa [prefixWord, tailWord_3072808, baseEnd_3072808] using wordTrace_append hprefix tailTrace_3072808
  have hstable : (prefixWord ++ tailWord_3072808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072808).length < 2 ^ (prefixWord ++ tailWord_3072808).sum := by decide
  have hdescent : baseEnd_3072808 < baseStart_3072808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072813 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3072813 : Nat := 118140960795 + 3072813 * 2 ^ 59
def prefixEnd_3072813 : Nat := 4983230072969 + 3 ^ 40 * 3072813 * 2
def baseEnd_3072813 : Nat := 1577830030384191338705897

theorem tailTrace_3072813 : CollatzResearch.WordTrace tailWord_3072813 prefixEnd_3072813 1577830030384191338705897 := by
  unfold tailWord_3072813
  simp only [CollatzResearch.WordTrace]
  refine ⟨112074697416730770524471093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74716464944487180349647395 112074697416730770524471093)
  ·
    refine ⟨10507002882818509736669165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112074697416730770524471093 10507002882818509736669165)
    ·
      refine ⟨3940126081056941151250937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10507002882818509736669165 3940126081056941151250937)
      ·
        refine ⟨2955094560792705863438203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3940126081056941151250937 2955094560792705863438203)
        ·
          refine ⟨4432641841189058795157305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2955094560792705863438203 4432641841189058795157305)
          ·
            refine ⟨3324481380891794096367979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4432641841189058795157305 3324481380891794096367979)
            ·
              refine ⟨4986722071337691144551969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3324481380891794096367979 4986722071337691144551969)
              ·
                refine ⟨3740041553503268358413977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4986722071337691144551969 3740041553503268358413977)
                ·
                  refine ⟨2805031165127451268810483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3740041553503268358413977 2805031165127451268810483)
                  ·
                    refine ⟨4207546747691176903215725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2805031165127451268810483 4207546747691176903215725)
                    ·
                      refine ⟨1577830030384191338705897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4207546747691176903215725 1577830030384191338705897)
                      ·
                        rfl

theorem cell23_3072813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3072813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072813 prefixEnd_3072813 := by exact prefixLift 3072813
  have htrace : WordTrace (prefixWord ++ tailWord_3072813) baseStart_3072813 baseEnd_3072813 := by
    simpa [prefixWord, tailWord_3072813, baseEnd_3072813] using wordTrace_append hprefix tailTrace_3072813
  have hstable : (prefixWord ++ tailWord_3072813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072813).length < 2 ^ (prefixWord ++ tailWord_3072813).sum := by decide
  have hdescent : baseEnd_3072813 < baseStart_3072813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072819 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 2, 2, 2]
def baseStart_3072819 : Nat := 118140960795 + 3072819 * 2 ^ 59
def prefixEnd_3072819 : Nat := 4983230072969 + 3 ^ 40 * 3072819 * 2
def baseEnd_3072819 : Nat := 1577833111268118315230869

theorem tailTrace_3072819 : CollatzResearch.WordTrace tailWord_3072819 prefixEnd_3072819 1577833111268118315230869 := by
  unfold tailWord_3072819
  simp only [CollatzResearch.WordTrace]
  refine ⟨112074916254709033549189511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74716610836472689032793007 112074916254709033549189511)
  ·
    refine ⟨168112374382063550323784267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112074916254709033549189511 168112374382063550323784267)
    ·
      refine ⟨252168561573095325485676401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168112374382063550323784267 252168561573095325485676401)
      ·
        refine ⟨189126421179821494114257301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252168561573095325485676401 189126421179821494114257301)
        ·
          refine ⟨8865300992804132536605811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 189126421179821494114257301 8865300992804132536605811)
          ·
            refine ⟨13297951489206198804908717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8865300992804132536605811 13297951489206198804908717)
            ·
              refine ⟨4986731808452324551840769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13297951489206198804908717 4986731808452324551840769)
              ·
                refine ⟨3740048856339243413880577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4986731808452324551840769 3740048856339243413880577)
                ·
                  refine ⟨2805036642254432560410433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3740048856339243413880577 2805036642254432560410433)
                  ·
                    refine ⟨2103777481690824420307825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2805036642254432560410433 2103777481690824420307825)
                    ·
                      refine ⟨1577833111268118315230869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103777481690824420307825 1577833111268118315230869)
                      ·
                        rfl

theorem cell23_3072819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 2, 2].length) (baseStart_3072819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072819 prefixEnd_3072819 := by exact prefixLift 3072819
  have htrace : WordTrace (prefixWord ++ tailWord_3072819) baseStart_3072819 baseEnd_3072819 := by
    simpa [prefixWord, tailWord_3072819, baseEnd_3072819] using wordTrace_append hprefix tailTrace_3072819
  have hstable : (prefixWord ++ tailWord_3072819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072819).length < 2 ^ (prefixWord ++ tailWord_3072819).sum := by decide
  have hdescent : baseEnd_3072819 < baseStart_3072819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072875 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 4, 4, 2]
def baseStart_3072875 : Nat := 118140960795 + 3072875 * 2 ^ 59
def prefixEnd_3072875 : Nat := 4983230072969 + 3 ^ 40 * 3072875 * 2
def baseEnd_3072875 : Nat := 1577861866184770096130611

theorem tailTrace_3072875 : CollatzResearch.WordTrace tailWord_3072875 prefixEnd_3072875 1577861866184770096130611 := by
  unfold tailWord_3072875
  simp only [CollatzResearch.WordTrace]
  refine ⟨112076958742506155113228079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74717972495004103408818719 112076958742506155113228079)
  ·
    refine ⟨168115438113759232669842119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112076958742506155113228079 168115438113759232669842119)
    ·
      refine ⟨252173157170638849004763179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168115438113759232669842119 252173157170638849004763179)
      ·
        refine ⟨378259735755958273507144769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252173157170638849004763179 378259735755958273507144769)
        ·
          refine ⟨283694801816968705130358577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378259735755958273507144769 283694801816968705130358577)
          ·
            refine ⟨212771101362726528847768933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283694801816968705130358577 212771101362726528847768933)
            ·
              refine ⟨39894581505511224158956675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212771101362726528847768933 39894581505511224158956675)
              ·
                refine ⟨59841872258266836238435013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39894581505511224158956675 59841872258266836238435013)
                ·
                  refine ⟨11220351048425031794706565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59841872258266836238435013 11220351048425031794706565)
                  ·
                    refine ⟨2103815821579693461507481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11220351048425031794706565 2103815821579693461507481)
                    ·
                      refine ⟨1577861866184770096130611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2103815821579693461507481 1577861866184770096130611)
                      ·
                        rfl

theorem cell23_3072875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 4, 2].length) (baseStart_3072875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072875 prefixEnd_3072875 := by exact prefixLift 3072875
  have htrace : WordTrace (prefixWord ++ tailWord_3072875) baseStart_3072875 baseEnd_3072875 := by
    simpa [prefixWord, tailWord_3072875, baseEnd_3072875] using wordTrace_append hprefix tailTrace_3072875
  have hstable : (prefixWord ++ tailWord_3072875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072875).length < 2 ^ (prefixWord ++ tailWord_3072875).sum := by decide
  have hdescent : baseEnd_3072875 < baseStart_3072875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072888 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_3072888 : Nat := 118140960795 + 3072888 * 2 ^ 59
def prefixEnd_3072888 : Nat := 4983230072969 + 3 ^ 40 * 3072888 * 2
def baseEnd_3072888 : Nat := 1577868541433278545268051

theorem tailTrace_3072888 : CollatzResearch.WordTrace tailWord_3072888 prefixEnd_3072888 1577868541433278545268051 := by
  unfold tailWord_3072888
  simp only [CollatzResearch.WordTrace]
  refine ⟨56038716445729529166725659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74718288594306038888967545 56038716445729529166725659)
  ·
    refine ⟨84058074668594293750088489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56038716445729529166725659 84058074668594293750088489)
    ·
      refine ⟨63043556001445720312566367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84058074668594293750088489 63043556001445720312566367)
      ·
        refine ⟨94565334002168580468849551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63043556001445720312566367 94565334002168580468849551)
        ·
          refine ⟨141848001003252870703274327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94565334002168580468849551 141848001003252870703274327)
          ·
            refine ⟨212772001504879306054911491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141848001003252870703274327 212772001504879306054911491)
            ·
              refine ⟨319158002257318959082367237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212772001504879306054911491 319158002257318959082367237)
              ·
                refine ⟨59842125423247304827943857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319158002257318959082367237 59842125423247304827943857)
                ·
                  refine ⟨44881594067435478620957893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59842125423247304827943857 44881594067435478620957893)
                  ·
                    refine ⟨8415298887644152241429605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44881594067435478620957893 8415298887644152241429605)
                    ·
                      refine ⟨1577868541433278545268051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8415298887644152241429605 1577868541433278545268051)
                      ·
                        rfl

theorem cell23_3072888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_3072888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072888 prefixEnd_3072888 := by exact prefixLift 3072888
  have htrace : WordTrace (prefixWord ++ tailWord_3072888) baseStart_3072888 baseEnd_3072888 := by
    simpa [prefixWord, tailWord_3072888, baseEnd_3072888] using wordTrace_append hprefix tailTrace_3072888
  have hstable : (prefixWord ++ tailWord_3072888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072888).length < 2 ^ (prefixWord ++ tailWord_3072888).sum := by decide
  have hdescent : baseEnd_3072888 < baseStart_3072888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072975 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 1, 6]
def baseStart_3072975 : Nat := 118140960795 + 3072975 * 2 ^ 59
def prefixEnd_3072975 : Nat := 4983230072969 + 3 ^ 40 * 3072975 * 2
def baseEnd_3072975 : Nat := 525971071416739901626717

theorem tailTrace_3072975 : CollatzResearch.WordTrace tailWord_3072975 prefixEnd_3072975 525971071416739901626717 := by
  unfold tailWord_3072975
  simp only [CollatzResearch.WordTrace]
  refine ⟨112080606042143872191868379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74720404028095914794578919 112080606042143872191868379)
  ·
    refine ⟨168120909063215808287802569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112080606042143872191868379 168120909063215808287802569)
    ·
      refine ⟨126090681797411856215851927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168120909063215808287802569 126090681797411856215851927)
      ·
        refine ⟨189136022696117784323777891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126090681797411856215851927 189136022696117784323777891)
        ·
          refine ⟨283704034044176676485666837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189136022696117784323777891 283704034044176676485666837)
          ·
            refine ⟨13298626595820781710265633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 283704034044176676485666837 13298626595820781710265633)
            ·
              refine ⟨9973969946865586282699225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13298626595820781710265633 9973969946865586282699225)
              ·
                refine ⟨7480477460149189712024419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9973969946865586282699225 7480477460149189712024419)
                ·
                  refine ⟨11220716190223784568036629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480477460149189712024419 11220716190223784568036629)
                  ·
                    refine ⟨525971071416739901626717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11220716190223784568036629 525971071416739901626717)
                    ·
                      rfl

theorem cell23_3072975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_3072975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072975 prefixEnd_3072975 := by exact prefixLift 3072975
  have htrace : WordTrace (prefixWord ++ tailWord_3072975) baseStart_3072975 baseEnd_3072975 := by
    simpa [prefixWord, tailWord_3072975, baseEnd_3072975] using wordTrace_append hprefix tailTrace_3072975
  have hstable : (prefixWord ++ tailWord_3072975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072975).length < 2 ^ (prefixWord ++ tailWord_3072975).sum := by decide
  have hdescent : baseEnd_3072975 < baseStart_3072975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3072995 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3072995 : Nat := 118140960795 + 3072995 * 2 ^ 59
def prefixEnd_3072995 : Nat := 4983230072969 + 3 ^ 40 * 3072995 * 2
def baseEnd_3072995 : Nat := 1577923483863309626630059

theorem tailTrace_3072995 : CollatzResearch.WordTrace tailWord_3072995 prefixEnd_3072995 1577923483863309626630059 := by
  unfold tailWord_3072995
  simp only [CollatzResearch.WordTrace]
  refine ⟨112081335502071415607596439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74720890334714277071730959 112081335502071415607596439)
  ·
    refine ⟨168122003253107123411394659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112081335502071415607596439 168122003253107123411394659)
    ·
      refine ⟨252183004879660685117091989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168122003253107123411394659 252183004879660685117091989)
      ·
        refine ⟨11821078353734094614863687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 252183004879660685117091989 11821078353734094614863687)
        ·
          refine ⟨17731617530601141922295531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11821078353734094614863687 17731617530601141922295531)
          ·
            refine ⟨26597426295901712883443297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17731617530601141922295531 26597426295901712883443297)
            ·
              refine ⟨19948069721926284662582473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26597426295901712883443297 19948069721926284662582473)
              ·
                refine ⟨14961052291444713496936855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19948069721926284662582473 14961052291444713496936855)
                ·
                  refine ⟨22441578437167070245405283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14961052291444713496936855 22441578437167070245405283)
                  ·
                    refine ⟨33662367655750605368107925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22441578437167070245405283 33662367655750605368107925)
                    ·
                      refine ⟨1577923483863309626630059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33662367655750605368107925 1577923483863309626630059)
                      ·
                        rfl

theorem cell23_3072995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3072995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3072995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3072995 prefixEnd_3072995 := by exact prefixLift 3072995
  have htrace : WordTrace (prefixWord ++ tailWord_3072995) baseStart_3072995 baseEnd_3072995 := by
    simpa [prefixWord, tailWord_3072995, baseEnd_3072995] using wordTrace_append hprefix tailTrace_3072995
  have hstable : (prefixWord ++ tailWord_3072995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3072995).length < 2 ^ (prefixWord ++ tailWord_3072995).sum := by decide
  have hdescent : baseEnd_3072995 < baseStart_3072995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3072995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073002 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_3073002 : Nat := 118140960795 + 3073002 * 2 ^ 59
def prefixEnd_3073002 : Nat := 4983230072969 + 3 ^ 40 * 3073002 * 2
def baseEnd_3073002 : Nat := 1577927078227891099242527

theorem tailTrace_3073002 : CollatzResearch.WordTrace tailWord_3073002 prefixEnd_3073002 1577927078227891099242527 := by
  unfold tailWord_3073002
  simp only [CollatzResearch.WordTrace]
  refine ⟨28020397703261513950775315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74721060542030703868734173 28020397703261513950775315)
  ·
    refine ⟨42030596554892270926162973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28020397703261513950775315 42030596554892270926162973)
    ·
      refine ⟨15761473708084601597311115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42030596554892270926162973 15761473708084601597311115)
      ·
        refine ⟨23642210562126902395966673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15761473708084601597311115 23642210562126902395966673)
        ·
          refine ⟨17731657921595176796975005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23642210562126902395966673 17731657921595176796975005)
          ·
            refine ⟨6649371720598191298865627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17731657921595176796975005 6649371720598191298865627)
            ·
              refine ⟨9974057580897286948298441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6649371720598191298865627 9974057580897286948298441)
              ·
                refine ⟨7480543185672965211223831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9974057580897286948298441 7480543185672965211223831)
                ·
                  refine ⟨11220814778509447816835747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480543185672965211223831 11220814778509447816835747)
                  ·
                    refine ⟨16831222167764171725253621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11220814778509447816835747 16831222167764171725253621)
                    ·
                      refine ⟨1577927078227891099242527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16831222167764171725253621 1577927078227891099242527)
                      ·
                        rfl

theorem cell23_3073002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_3073002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073002 prefixEnd_3073002 := by exact prefixLift 3073002
  have htrace : WordTrace (prefixWord ++ tailWord_3073002) baseStart_3073002 baseEnd_3073002 := by
    simpa [prefixWord, tailWord_3073002, baseEnd_3073002] using wordTrace_append hprefix tailTrace_3073002
  have hstable : (prefixWord ++ tailWord_3073002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073002).length < 2 ^ (prefixWord ++ tailWord_3073002).sum := by decide
  have hdescent : baseEnd_3073002 < baseStart_3073002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073102 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_3073102 : Nat := 118140960795 + 3073102 * 2 ^ 59
def prefixEnd_3073102 : Nat := 4983230072969 + 3 ^ 40 * 3073102 * 2
def baseEnd_3073102 : Nat := 1577978426293340707992067

theorem tailTrace_3073102 : CollatzResearch.WordTrace tailWord_3073102 prefixEnd_3073102 1577978426293340707992067 := by
  unfold tailWord_3073102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14010654764085471610217695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74723492075122515254494373 14010654764085471610217695)
  ·
    refine ⟨21015982146128207415326543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14010654764085471610217695 21015982146128207415326543)
    ·
      refine ⟨31523973219192311122989815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21015982146128207415326543 31523973219192311122989815)
      ·
        refine ⟨47285959828788466684484723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31523973219192311122989815 47285959828788466684484723)
        ·
          refine ⟨70928939743182700026727085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47285959828788466684484723 70928939743182700026727085)
          ·
            refine ⟨26598352403693512510022657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70928939743182700026727085 26598352403693512510022657)
            ·
              refine ⟨19948764302770134382516993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26598352403693512510022657 19948764302770134382516993)
              ·
                refine ⟨14961573227077600786887745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19948764302770134382516993 14961573227077600786887745)
                ·
                  refine ⟨11221179920308200590165809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14961573227077600786887745 11221179920308200590165809)
                  ·
                    refine ⟨8415884940231150442624357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11221179920308200590165809 8415884940231150442624357)
                    ·
                      refine ⟨1577978426293340707992067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8415884940231150442624357 1577978426293340707992067)
                      ·
                        rfl

theorem cell23_3073102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_3073102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073102 prefixEnd_3073102 := by exact prefixLift 3073102
  have htrace : WordTrace (prefixWord ++ tailWord_3073102) baseStart_3073102 baseEnd_3073102 := by
    simpa [prefixWord, tailWord_3073102, baseEnd_3073102] using wordTrace_append hprefix tailTrace_3073102
  have hstable : (prefixWord ++ tailWord_3073102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073102).length < 2 ^ (prefixWord ++ tailWord_3073102).sum := by decide
  have hdescent : baseEnd_3073102 < baseStart_3073102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073105 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_3073105 : Nat := 118140960795 + 3073105 * 2 ^ 59
def prefixEnd_3073105 : Nat := 4983230072969 + 3 ^ 40 * 3073105 * 2
def baseEnd_3073105 : Nat := 1577979966735304196254553

theorem tailTrace_3073105 : CollatzResearch.WordTrace tailWord_3073105 prefixEnd_3073105 1577979966735304196254553 := by
  unfold tailWord_3073105
  simp only [CollatzResearch.WordTrace]
  refine ⟨112085347531672904394100769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74723565021115269596067179 112085347531672904394100769)
  ·
    refine ⟨84064010648754678295575577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112085347531672904394100769 84064010648754678295575577)
    ·
      refine ⟨63048007986566008721681683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84064010648754678295575577 63048007986566008721681683)
      ·
        refine ⟨94572011979849013082522525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63048007986566008721681683 94572011979849013082522525)
        ·
          refine ⟨35464504492443379905945947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94572011979849013082522525 35464504492443379905945947)
          ·
            refine ⟨53196756738665069858918921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35464504492443379905945947 53196756738665069858918921)
            ·
              refine ⟨39897567553998802394189191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53196756738665069858918921 39897567553998802394189191)
              ·
                refine ⟨59846351330998203591283787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39897567553998802394189191 59846351330998203591283787)
                ·
                  refine ⟨89769526996497305386925681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59846351330998203591283787 89769526996497305386925681)
                  ·
                    refine ⟨67327145247372979040194261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89769526996497305386925681 67327145247372979040194261)
                    ·
                      refine ⟨1577979966735304196254553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 67327145247372979040194261 1577979966735304196254553)
                      ·
                        rfl

theorem cell23_3073105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_3073105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073105 prefixEnd_3073105 := by exact prefixLift 3073105
  have htrace : WordTrace (prefixWord ++ tailWord_3073105) baseStart_3073105 baseEnd_3073105 := by
    simpa [prefixWord, tailWord_3073105, baseEnd_3073105] using wordTrace_append hprefix tailTrace_3073105
  have hstable : (prefixWord ++ tailWord_3073105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073105).length < 2 ^ (prefixWord ++ tailWord_3073105).sum := by decide
  have hdescent : baseEnd_3073105 < baseStart_3073105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073189 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 3, 4]
def baseStart_3073189 : Nat := 118140960795 + 3073189 * 2 ^ 59
def prefixEnd_3073189 : Nat := 4983230072969 + 3 ^ 40 * 3073189 * 2
def baseEnd_3073189 : Nat := 526007699703427289201389

theorem tailTrace_3073189 : CollatzResearch.WordTrace tailWord_3073189 prefixEnd_3073189 526007699703427289201389 := by
  unfold tailWord_3073189
  simp only [CollatzResearch.WordTrace]
  refine ⟨112088411263368586740158621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74725607508912391160105747 112088411263368586740158621)
  ·
    refine ⟨42033154223763220027559483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112088411263368586740158621 42033154223763220027559483)
    ·
      refine ⟨63049731335644830041339225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42033154223763220027559483 63049731335644830041339225)
      ·
        refine ⟨47287298501733622531004419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63049731335644830041339225 47287298501733622531004419)
        ·
          refine ⟨70930947752600433796506629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47287298501733622531004419 70930947752600433796506629)
          ·
            refine ⟨13299552703612581336844993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70930947752600433796506629 13299552703612581336844993)
            ·
              refine ⟨9974664527709436002633745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13299552703612581336844993 9974664527709436002633745)
              ·
                refine ⟨7480998395782077001975309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9974664527709436002633745 7480998395782077001975309)
                ·
                  refine ⟨2805374398418278875740741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7480998395782077001975309 2805374398418278875740741)
                  ·
                    refine ⟨526007699703427289201389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2805374398418278875740741 526007699703427289201389)
                    ·
                      rfl

theorem cell23_3073189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_3073189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073189 prefixEnd_3073189 := by exact prefixLift 3073189
  have htrace : WordTrace (prefixWord ++ tailWord_3073189) baseStart_3073189 baseEnd_3073189 := by
    simpa [prefixWord, tailWord_3073189, baseEnd_3073189] using wordTrace_append hprefix tailTrace_3073189
  have hstable : (prefixWord ++ tailWord_3073189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073189).length < 2 ^ (prefixWord ++ tailWord_3073189).sum := by decide
  have hdescent : baseEnd_3073189 < baseStart_3073189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073202 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 8]
def baseStart_3073202 : Nat := 118140960795 + 3073202 * 2 ^ 59
def prefixEnd_3073202 : Nat := 4983230072969 + 3 ^ 40 * 3073202 * 2
def baseEnd_3073202 : Nat := 175336641595421146304623

theorem tailTrace_3073202 : CollatzResearch.WordTrace tailWord_3073202 prefixEnd_3073202 175336641595421146304623 := by
  unfold tailWord_3073202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28022221353080372490095465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74725923608214326640254573 28022221353080372490095465)
  ·
    refine ⟨21016666014810279367571599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28022221353080372490095465 21016666014810279367571599)
    ·
      refine ⟨31524999022215419051357399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21016666014810279367571599 31524999022215419051357399)
      ·
        refine ⟨47287498533323128577036099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31524999022215419051357399 47287498533323128577036099)
        ·
          refine ⟨70931247799984692865554149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47287498533323128577036099 70931247799984692865554149)
          ·
            refine ⟨13299608962497129912291403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70931247799984692865554149 13299608962497129912291403)
            ·
              refine ⟨19949413443745694868437105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13299608962497129912291403 19949413443745694868437105)
              ·
                refine ⟨14962060082809271151327829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19949413443745694868437105 14962060082809271151327829)
                ·
                  refine ⟨175336641595421146304623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14962060082809271151327829 175336641595421146304623)
                  ·
                    rfl

theorem cell23_3073202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_3073202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073202 prefixEnd_3073202 := by exact prefixLift 3073202
  have htrace : WordTrace (prefixWord ++ tailWord_3073202) baseStart_3073202 baseEnd_3073202 := by
    simpa [prefixWord, tailWord_3073202, baseEnd_3073202] using wordTrace_append hprefix tailTrace_3073202
  have hstable : (prefixWord ++ tailWord_3073202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073202).length < 2 ^ (prefixWord ++ tailWord_3073202).sum := by decide
  have hdescent : baseEnd_3073202 < baseStart_3073202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073216 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 3]
def baseStart_3073216 : Nat := 118140960795 + 3073216 * 2 ^ 59
def prefixEnd_3073216 : Nat := 4983230072969 + 3 ^ 40 * 3073216 * 2
def baseEnd_3073216 : Nat := 1578036963087953261966543

theorem tailTrace_3073216 : CollatzResearch.WordTrace tailWord_3073216 prefixEnd_3073216 1578036963087953261966543 := by
  unfold tailWord_3073216
  simp only [CollatzResearch.WordTrace]
  refine ⟨56044698017135385175695751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74726264022847180234261001 56044698017135385175695751)
  ·
    refine ⟨84067047025703077763543627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56044698017135385175695751 84067047025703077763543627)
    ·
      refine ⟨126100570538554616645315441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84067047025703077763543627 126100570538554616645315441)
      ·
        refine ⟨94575427903915962483986581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126100570538554616645315441 94575427903915962483986581)
        ·
          refine ⟨4433223182996060741436871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94575427903915962483986581 4433223182996060741436871)
          ·
            refine ⟨6649834774494091112155307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4433223182996060741436871 6649834774494091112155307)
            ·
              refine ⟨9974752161741136668232961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6649834774494091112155307 9974752161741136668232961)
              ·
                refine ⟨7481064121305852501174721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9974752161741136668232961 7481064121305852501174721)
                ·
                  refine ⟨5610798090979389375881041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7481064121305852501174721 5610798090979389375881041)
                  ·
                    refine ⟨4208098568234542031910781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5610798090979389375881041 4208098568234542031910781)
                    ·
                      refine ⟨1578036963087953261966543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4208098568234542031910781 1578036963087953261966543)
                      ·
                        rfl

theorem cell23_3073216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_3073216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073216 prefixEnd_3073216 := by exact prefixLift 3073216
  have htrace : WordTrace (prefixWord ++ tailWord_3073216) baseStart_3073216 baseEnd_3073216 := by
    simpa [prefixWord, tailWord_3073216, baseEnd_3073216] using wordTrace_append hprefix tailTrace_3073216
  have hstable : (prefixWord ++ tailWord_3073216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073216).length < 2 ^ (prefixWord ++ tailWord_3073216).sum := by decide
  have hdescent : baseEnd_3073216 < baseStart_3073216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073239 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 3, 5, 2]
def baseStart_3073239 : Nat := 118140960795 + 3073239 * 2 ^ 59
def prefixEnd_3073239 : Nat := 4983230072969 + 3 ^ 40 * 3073239 * 2
def baseEnd_3073239 : Nat := 1578048773143006671978937

theorem tailTrace_3073239 : CollatzResearch.WordTrace tailWord_3073239 prefixEnd_3073239 1578048773143006671978937 := by
  unfold tailWord_3073239
  simp only [CollatzResearch.WordTrace]
  refine ⟨112090234913187445279478771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74726823275458296852985847 112090234913187445279478771)
  ·
    refine ⟨168135352369781167919218157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112090234913187445279478771 168135352369781167919218157)
    ·
      refine ⟨63050757138667937969706809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168135352369781167919218157 63050757138667937969706809)
      ·
        refine ⟨47288067854000953477280107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63050757138667937969706809 47288067854000953477280107)
        ·
          refine ⟨70932101781001430215920161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47288067854000953477280107 70932101781001430215920161)
          ·
            refine ⟨53199076335751072661940121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70932101781001430215920161 53199076335751072661940121)
            ·
              refine ⟨39899307251813304496455091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53199076335751072661940121 39899307251813304496455091)
              ·
                refine ⟨59848960877719956744682637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39899307251813304496455091 59848960877719956744682637)
                ·
                  refine ⟨22443360329144983779255989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59848960877719956744682637 22443360329144983779255989)
                  ·
                    refine ⟨2104065030857342229305249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22443360329144983779255989 2104065030857342229305249)
                    ·
                      refine ⟨1578048773143006671978937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104065030857342229305249 1578048773143006671978937)
                      ·
                        rfl

theorem cell23_3073239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_3073239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073239 prefixEnd_3073239 := by exact prefixLift 3073239
  have htrace : WordTrace (prefixWord ++ tailWord_3073239) baseStart_3073239 baseEnd_3073239 := by
    simpa [prefixWord, tailWord_3073239, baseEnd_3073239] using wordTrace_append hprefix tailTrace_3073239
  have hstable : (prefixWord ++ tailWord_3073239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073239).length < 2 ^ (prefixWord ++ tailWord_3073239).sum := by decide
  have hdescent : baseEnd_3073239 < baseStart_3073239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073249 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 3, 5]
def baseStart_3073249 : Nat := 118140960795 + 3073249 * 2 ^ 59
def prefixEnd_3073249 : Nat := 4983230072969 + 3 ^ 40 * 3073249 * 2
def baseEnd_3073249 : Nat := 526017969316517210951297

theorem tailTrace_3073249 : CollatzResearch.WordTrace tailWord_3073249 prefixEnd_3073249 526017969316517210951297 := by
  unfold tailWord_3073249
  simp only [CollatzResearch.WordTrace]
  refine ⟨112090599643151216987342801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74727066428767477991561867 112090599643151216987342801)
  ·
    refine ⟨84067949732363412740507101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112090599643151216987342801 84067949732363412740507101)
    ·
      refine ⟨31525481149636279777690163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84067949732363412740507101 31525481149636279777690163)
      ·
        refine ⟨47288221724454419666535245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31525481149636279777690163 47288221724454419666535245)
        ·
          refine ⟨17733083146670407374950717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47288221724454419666535245 17733083146670407374950717)
          ·
            refine ⟨6649906180001402765606519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17733083146670407374950717 6649906180001402765606519)
            ·
              refine ⟨9974859270002104148409779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6649906180001402765606519 9974859270002104148409779)
              ·
                refine ⟨14962288905003156222614669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9974859270002104148409779 14962288905003156222614669)
                ·
                  refine ⟨5610858339376183583480501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14962288905003156222614669 5610858339376183583480501)
                  ·
                    refine ⟨526017969316517210951297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5610858339376183583480501 526017969316517210951297)
                    ·
                      rfl

theorem cell23_3073249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_3073249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073249 prefixEnd_3073249 := by exact prefixLift 3073249
  have htrace : WordTrace (prefixWord ++ tailWord_3073249) baseStart_3073249 baseEnd_3073249 := by
    simpa [prefixWord, tailWord_3073249, baseEnd_3073249] using wordTrace_append hprefix tailTrace_3073249
  have hstable : (prefixWord ++ tailWord_3073249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073249).length < 2 ^ (prefixWord ++ tailWord_3073249).sum := by decide
  have hdescent : baseEnd_3073249 < baseStart_3073249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073289 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 5, 2, 3]
def baseStart_3073289 : Nat := 118140960795 + 3073289 * 2 ^ 59
def prefixEnd_3073289 : Nat := 4983230072969 + 3 ^ 40 * 3073289 * 2
def baseEnd_3073289 : Nat := 1578074447175731476353707

theorem tailTrace_3073289 : CollatzResearch.WordTrace tailWord_3073289 prefixEnd_3073289 1578074447175731476353707 := by
  unfold tailWord_3073289
  simp only [CollatzResearch.WordTrace]
  refine ⟨112092058563006303818798921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74728039042004202545865947 112092058563006303818798921)
  ·
    refine ⟨84069043922254727864099191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112092058563006303818798921 84069043922254727864099191)
    ·
      refine ⟨126103565883382091796148787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84069043922254727864099191 126103565883382091796148787)
      ·
        refine ⟨189155348825073137694223181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126103565883382091796148787 189155348825073137694223181)
        ·
          refine ⟨70933255809402426635333693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189155348825073137694223181 70933255809402426635333693)
          ·
            refine ⟨26599970928525909988250135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70933255809402426635333693 26599970928525909988250135)
            ·
              refine ⟨39899956392788864982375203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26599970928525909988250135 39899956392788864982375203)
              ·
                refine ⟨59849934589183297473562805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39899956392788864982375203 59849934589183297473562805)
                ·
                  refine ⟨5610931367735934138146513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59849934589183297473562805 5610931367735934138146513)
                  ·
                    refine ⟨4208198525801950603609885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5610931367735934138146513 4208198525801950603609885)
                    ·
                      refine ⟨1578074447175731476353707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4208198525801950603609885 1578074447175731476353707)
                      ·
                        rfl

theorem cell23_3073289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 2, 3].length) (baseStart_3073289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073289 prefixEnd_3073289 := by exact prefixLift 3073289
  have htrace : WordTrace (prefixWord ++ tailWord_3073289) baseStart_3073289 baseEnd_3073289 := by
    simpa [prefixWord, tailWord_3073289, baseEnd_3073289] using wordTrace_append hprefix tailTrace_3073289
  have hstable : (prefixWord ++ tailWord_3073289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073289).length < 2 ^ (prefixWord ++ tailWord_3073289).sum := by decide
  have hdescent : baseEnd_3073289 < baseStart_3073289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073303 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 3, 2, 2]
def baseStart_3073303 : Nat := 118140960795 + 3073303 * 2 ^ 59
def prefixEnd_3073303 : Nat := 4983230072969 + 3 ^ 40 * 3073303 * 2
def baseEnd_3073303 : Nat := 1578081635904894421578643

theorem tailTrace_3073303 : CollatzResearch.WordTrace tailWord_3073303 prefixEnd_3073303 1578081635904894421578643 := by
  unfold tailWord_3073303
  simp only [CollatzResearch.WordTrace]
  refine ⟨112092569184955584209808563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74728379456637056139872375 112092569184955584209808563)
  ·
    refine ⟨168138853777433376314712845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112092569184955584209808563 168138853777433376314712845)
    ·
      refine ⟨63052070166537516118017317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168138853777433376314712845 63052070166537516118017317)
      ·
        refine ⟨11822263156225784272128247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63052070166537516118017317 11822263156225784272128247)
        ·
          refine ⟨17733394734338676408192371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11822263156225784272128247 17733394734338676408192371)
          ·
            refine ⟨26600092101508014612288557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17733394734338676408192371 26600092101508014612288557)
            ·
              refine ⟨9975034538065505479608209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26600092101508014612288557 9975034538065505479608209)
              ·
                refine ⟨7481275903549129109706157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9975034538065505479608209 7481275903549129109706157)
                ·
                  refine ⟨2805478463830923416139809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7481275903549129109706157 2805478463830923416139809)
                  ·
                    refine ⟨2104108847873192562104857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2805478463830923416139809 2104108847873192562104857)
                    ·
                      refine ⟨1578081635904894421578643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104108847873192562104857 1578081635904894421578643)
                      ·
                        rfl

theorem cell23_3073303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_3073303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073303 prefixEnd_3073303 := by exact prefixLift 3073303
  have htrace : WordTrace (prefixWord ++ tailWord_3073303) baseStart_3073303 baseEnd_3073303 := by
    simpa [prefixWord, tailWord_3073303, baseEnd_3073303] using wordTrace_append hprefix tailTrace_3073303
  have hstable : (prefixWord ++ tailWord_3073303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073303).length < 2 ^ (prefixWord ++ tailWord_3073303).sum := by decide
  have hdescent : baseEnd_3073303 < baseStart_3073303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073306 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3]
def baseStart_3073306 : Nat := 118140960795 + 3073306 * 2 ^ 59
def prefixEnd_3073306 : Nat := 4983230072969 + 3 ^ 40 * 3073306 * 2
def baseEnd_3073306 : Nat := 1578083176346857909841129

theorem tailTrace_3073306 : CollatzResearch.WordTrace tailWord_3073306 prefixEnd_3073306 1578083176346857909841129 := by
  unfold tailWord_3073306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28023169650986178930541943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74728452402629810481445181 28023169650986178930541943)
  ·
    refine ⟨42034754476479268395812915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28023169650986178930541943 42034754476479268395812915)
    ·
      refine ⟨63052131714718902593719373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42034754476479268395812915 63052131714718902593719373)
      ·
        refine ⟨23644549393019588472644765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63052131714718902593719373 23644549393019588472644765)
        ·
          refine ⟨8866706022382345677241787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23644549393019588472644765 8866706022382345677241787)
          ·
            refine ⟨13300059033573518515862681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8866706022382345677241787 13300059033573518515862681)
            ·
              refine ⟨9975044275180138886897011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13300059033573518515862681 9975044275180138886897011)
              ·
                refine ⟨14962566412770208330345517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9975044275180138886897011 14962566412770208330345517)
                ·
                  refine ⟨5610962404788828123879569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14962566412770208330345517 5610962404788828123879569)
                  ·
                    refine ⟨4208221803591621092909677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5610962404788828123879569 4208221803591621092909677)
                    ·
                      refine ⟨1578083176346857909841129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4208221803591621092909677 1578083176346857909841129)
                      ·
                        rfl

theorem cell23_3073306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_3073306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073306 prefixEnd_3073306 := by exact prefixLift 3073306
  have htrace : WordTrace (prefixWord ++ tailWord_3073306) baseStart_3073306 baseEnd_3073306 := by
    simpa [prefixWord, tailWord_3073306, baseEnd_3073306] using wordTrace_append hprefix tailTrace_3073306
  have hstable : (prefixWord ++ tailWord_3073306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073306).length < 2 ^ (prefixWord ++ tailWord_3073306).sum := by decide
  have hdescent : baseEnd_3073306 < baseStart_3073306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073320 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_3073320 : Nat := 118140960795 + 3073320 * 2 ^ 59
def prefixEnd_3073320 : Nat := 4983230072969 + 3 ^ 40 * 3073320 * 2
def baseEnd_3073320 : Nat := 1578090365076020855066065

theorem tailTrace_3073320 : CollatzResearch.WordTrace tailWord_3073320 prefixEnd_3073320 1578090365076020855066065 := by
  unfold tailWord_3073320
  simp only [CollatzResearch.WordTrace]
  refine ⟨56046594612946998056588707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74728792817262664075451609 56046594612946998056588707)
  ·
    refine ⟨84069891919420497084883061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56046594612946998056588707 84069891919420497084883061)
    ·
      refine ⟨7881552367445671601707787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84069891919420497084883061 7881552367445671601707787)
      ·
        refine ⟨11822328551168507402561681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7881552367445671601707787 11822328551168507402561681)
        ·
          refine ⟨8866746413376380551921261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11822328551168507402561681 8866746413376380551921261)
          ·
            refine ⟨3325029905016142706970473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8866746413376380551921261 3325029905016142706970473)
            ·
              refine ⟨2493772428762107030227855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3325029905016142706970473 2493772428762107030227855)
              ·
                refine ⟨3740658643143160545341783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2493772428762107030227855 3740658643143160545341783)
                ·
                  refine ⟨5610987964714740818012675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740658643143160545341783 5610987964714740818012675)
                  ·
                    refine ⟨8416481947072111227019013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5610987964714740818012675 8416481947072111227019013)
                    ·
                      refine ⟨1578090365076020855066065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8416481947072111227019013 1578090365076020855066065)
                      ·
                        rfl

theorem cell23_3073320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_3073320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073320 prefixEnd_3073320 := by exact prefixLift 3073320
  have htrace : WordTrace (prefixWord ++ tailWord_3073320) baseStart_3073320 baseEnd_3073320 := by
    simpa [prefixWord, tailWord_3073320, baseEnd_3073320] using wordTrace_append hprefix tailTrace_3073320
  have hstable : (prefixWord ++ tailWord_3073320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073320).length < 2 ^ (prefixWord ++ tailWord_3073320).sum := by decide
  have hdescent : baseEnd_3073320 < baseStart_3073320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073350 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3073350 : Nat := 118140960795 + 3073350 * 2 ^ 59
def prefixEnd_3073350 : Nat := 4983230072969 + 3 ^ 40 * 3073350 * 2
def baseEnd_3073350 : Nat := 1578105769495655737690927

theorem tailTrace_3073350 : CollatzResearch.WordTrace tailWord_3073350 prefixEnd_3073350 1578105769495655737690927 := by
  unfold tailWord_3073350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3502946356743290976149047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 74729522277190207491179669 3502946356743290976149047)
  ·
    refine ⟨5254419535114936464223571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3502946356743290976149047 5254419535114936464223571)
    ·
      refine ⟨7881629302672404696335357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5254419535114936464223571 7881629302672404696335357)
      ·
        refine ⟨2955610988502151761125759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7881629302672404696335357 2955610988502151761125759)
        ·
          refine ⟨4433416482753227641688639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2955610988502151761125759 4433416482753227641688639)
          ·
            refine ⟨6650124724129841462532959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4433416482753227641688639 6650124724129841462532959)
            ·
              refine ⟨9975187086194762193799439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6650124724129841462532959 9975187086194762193799439)
              ·
                refine ⟨14962780629292143290699159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9975187086194762193799439 14962780629292143290699159)
                ·
                  refine ⟨22444170943938214936048739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14962780629292143290699159 22444170943938214936048739)
                  ·
                    refine ⟨33666256415907322404073109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22444170943938214936048739 33666256415907322404073109)
                    ·
                      refine ⟨1578105769495655737690927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33666256415907322404073109 1578105769495655737690927)
                      ·
                        rfl

theorem cell23_3073350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3073350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073350 prefixEnd_3073350 := by exact prefixLift 3073350
  have htrace : WordTrace (prefixWord ++ tailWord_3073350) baseStart_3073350 baseEnd_3073350 := by
    simpa [prefixWord, tailWord_3073350, baseEnd_3073350] using wordTrace_append hprefix tailTrace_3073350
  have hstable : (prefixWord ++ tailWord_3073350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073350).length < 2 ^ (prefixWord ++ tailWord_3073350).sum := by decide
  have hdescent : baseEnd_3073350 < baseStart_3073350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073357 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3073357 : Nat := 118140960795 + 3073357 * 2 ^ 59
def prefixEnd_3073357 : Nat := 4983230072969 + 3 ^ 40 * 3073357 * 2
def baseEnd_3073357 : Nat := 1578109363860237210303395

theorem tailTrace_3073357 : CollatzResearch.WordTrace tailWord_3073357 prefixEnd_3073357 1578109363860237210303395 := by
  unfold tailWord_3073357
  simp only [CollatzResearch.WordTrace]
  refine ⟨112094538726759951432274325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74729692484506634288182883 112094538726759951432274325)
  ·
    refine ⟨5254431502816872723387859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112094538726759951432274325 5254431502816872723387859)
    ·
      refine ⟨7881647254225309085081789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5254431502816872723387859 7881647254225309085081789)
      ·
        refine ⟨2955617720334490906905671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7881647254225309085081789 2955617720334490906905671)
        ·
          refine ⟨4433426580501736360358507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2955617720334490906905671 4433426580501736360358507)
          ·
            refine ⟨6650139870752604540537761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4433426580501736360358507 6650139870752604540537761)
            ·
              refine ⟨4987604903064453405403321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6650139870752604540537761 4987604903064453405403321)
              ·
                refine ⟨3740703677298340054052491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4987604903064453405403321 3740703677298340054052491)
                ·
                  refine ⟨5611055515947510081078737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740703677298340054052491 5611055515947510081078737)
                  ·
                    refine ⟨4208291636960632560809053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5611055515947510081078737 4208291636960632560809053)
                    ·
                      refine ⟨1578109363860237210303395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4208291636960632560809053 1578109363860237210303395)
                      ·
                        rfl

theorem cell23_3073357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3073357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073357 prefixEnd_3073357 := by exact prefixLift 3073357
  have htrace : WordTrace (prefixWord ++ tailWord_3073357) baseStart_3073357 baseEnd_3073357 := by
    simpa [prefixWord, tailWord_3073357, baseEnd_3073357] using wordTrace_append hprefix tailTrace_3073357
  have hstable : (prefixWord ++ tailWord_3073357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073357).length < 2 ^ (prefixWord ++ tailWord_3073357).sum := by decide
  have hdescent : baseEnd_3073357 < baseStart_3073357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073363 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 1, 3, 2]
def baseStart_3073363 : Nat := 118140960795 + 3073363 * 2 ^ 59
def prefixEnd_3073363 : Nat := 4983230072969 + 3 ^ 40 * 3073363 * 2
def baseEnd_3073363 : Nat := 1578112444744164186828367

theorem tailTrace_3073363 : CollatzResearch.WordTrace tailWord_3073363 prefixEnd_3073363 1578112444744164186828367 := by
  unfold tailWord_3073363
  simp only [CollatzResearch.WordTrace]
  refine ⟨112094757564738214456992743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74729838376492142971328495 112094757564738214456992743)
  ·
    refine ⟨168142136347107321685489115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112094757564738214456992743 168142136347107321685489115)
    ·
      refine ⟨252213204520660982528233673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168142136347107321685489115 252213204520660982528233673)
      ·
        refine ⟨189159903390495736896175255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252213204520660982528233673 189159903390495736896175255)
        ·
          refine ⟨283739855085743605344262883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189159903390495736896175255 283739855085743605344262883)
          ·
            refine ⟨425609782628615408016394325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283739855085743605344262883 425609782628615408016394325)
            ·
              refine ⟨4987614640179086812692121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 425609782628615408016394325 4987614640179086812692121)
              ·
                refine ⟨3740710980134315109519091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4987614640179086812692121 3740710980134315109519091)
                ·
                  refine ⟨5611066470201472664278637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740710980134315109519091 5611066470201472664278637)
                  ·
                    refine ⟨2104149926325552249104489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5611066470201472664278637 2104149926325552249104489)
                    ·
                      refine ⟨1578112444744164186828367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104149926325552249104489 1578112444744164186828367)
                      ·
                        rfl

theorem cell23_3073363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 3, 2].length) (baseStart_3073363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073363 prefixEnd_3073363 := by exact prefixLift 3073363
  have htrace : WordTrace (prefixWord ++ tailWord_3073363) baseStart_3073363 baseEnd_3073363 := by
    simpa [prefixWord, tailWord_3073363, baseEnd_3073363] using wordTrace_append hprefix tailTrace_3073363
  have hstable : (prefixWord ++ tailWord_3073363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073363).length < 2 ^ (prefixWord ++ tailWord_3073363).sum := by decide
  have hdescent : baseEnd_3073363 < baseStart_3073363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073379 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 5]
def baseStart_3073379 : Nat := 118140960795 + 3073379 * 2 ^ 59
def prefixEnd_3073379 : Nat := 4983230072969 + 3 ^ 40 * 3073379 * 2
def baseEnd_3073379 : Nat := 1578120660434636124228293

theorem tailTrace_3073379 : CollatzResearch.WordTrace tailWord_3073379 prefixEnd_3073379 1578120660434636124228293 := by
  unfold tailWord_3073379
  simp only [CollatzResearch.WordTrace]
  refine ⟨112095341132680249189575191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74730227421786832793050127 112095341132680249189575191)
  ·
    refine ⟨168143011699020373784362787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112095341132680249189575191 168143011699020373784362787)
    ·
      refine ⟨252214517548530560676544181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168143011699020373784362787 252214517548530560676544181)
      ·
        refine ⟨23645111020174740063426017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 252214517548530560676544181 23645111020174740063426017)
        ·
          refine ⟨17733833265131055047569513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23645111020174740063426017 17733833265131055047569513)
          ·
            refine ⟨13300374948848291285677135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17733833265131055047569513 13300374948848291285677135)
            ·
              refine ⟨19950562423272436928515703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13300374948848291285677135 19950562423272436928515703)
              ·
                refine ⟨29925843634908655392773555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19950562423272436928515703 29925843634908655392773555)
                ·
                  refine ⟨44888765452362983089160333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29925843634908655392773555 44888765452362983089160333)
                  ·
                    refine ⟨16833287044636118658435125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44888765452362983089160333 16833287044636118658435125)
                    ·
                      refine ⟨1578120660434636124228293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16833287044636118658435125 1578120660434636124228293)
                      ·
                        rfl

theorem cell23_3073379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_3073379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073379 prefixEnd_3073379 := by exact prefixLift 3073379
  have htrace : WordTrace (prefixWord ++ tailWord_3073379) baseStart_3073379 baseEnd_3073379 := by
    simpa [prefixWord, tailWord_3073379, baseEnd_3073379] using wordTrace_append hprefix tailTrace_3073379
  have hstable : (prefixWord ++ tailWord_3073379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073379).length < 2 ^ (prefixWord ++ tailWord_3073379).sum := by decide
  have hdescent : baseEnd_3073379 < baseStart_3073379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073393 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 4, 2, 2]
def baseStart_3073393 : Nat := 118140960795 + 3073393 * 2 ^ 59
def prefixEnd_3073393 : Nat := 4983230072969 + 3 ^ 40 * 3073393 * 2
def baseEnd_3073393 : Nat := 1578127849163799069453229

theorem tailTrace_3073393 : CollatzResearch.WordTrace tailWord_3073393 prefixEnd_3073393 1578127849163799069453229 := by
  unfold tailWord_3073393
  simp only [CollatzResearch.WordTrace]
  refine ⟨112095851754629529580584833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74730567836419686387056555 112095851754629529580584833)
  ·
    refine ⟨84071888815972147185438625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112095851754629529580584833 84071888815972147185438625)
    ·
      refine ⟨63053916611979110389078969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84071888815972147185438625 63053916611979110389078969)
      ·
        refine ⟨47290437458984332791809227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63053916611979110389078969 47290437458984332791809227)
        ·
          refine ⟨70935656188476499187713841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47290437458984332791809227 70935656188476499187713841)
          ·
            refine ⟨53201742141357374390785381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70935656188476499187713841 53201742141357374390785381)
            ·
              refine ⟨9975326651504507698272259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53201742141357374390785381 9975326651504507698272259)
              ·
                refine ⟨14962989977256761547408389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9975326651504507698272259 14962989977256761547408389)
                ·
                  refine ⟨2805560620735642790139073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14962989977256761547408389 2805560620735642790139073)
                  ·
                    refine ⟨2104170465551732092604305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2805560620735642790139073 2104170465551732092604305)
                    ·
                      refine ⟨1578127849163799069453229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104170465551732092604305 1578127849163799069453229)
                      ·
                        rfl

theorem cell23_3073393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_3073393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073393 prefixEnd_3073393 := by exact prefixLift 3073393
  have htrace : WordTrace (prefixWord ++ tailWord_3073393) baseStart_3073393 baseEnd_3073393 := by
    simpa [prefixWord, tailWord_3073393, baseEnd_3073393] using wordTrace_append hprefix tailTrace_3073393
  have hstable : (prefixWord ++ tailWord_3073393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073393).length < 2 ^ (prefixWord ++ tailWord_3073393).sum := by decide
  have hdescent : baseEnd_3073393 < baseStart_3073393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073429 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_3073429 : Nat := 118140960795 + 3073429 * 2 ^ 59
def prefixEnd_3073429 : Nat := 4983230072969 + 3 ^ 40 * 3073429 * 2
def baseEnd_3073429 : Nat := 526048778155786976201021

theorem tailTrace_3073429 : CollatzResearch.WordTrace tailWord_3073429 prefixEnd_3073429 526048778155786976201021 := by
  unfold tailWord_3073429
  simp only [CollatzResearch.WordTrace]
  refine ⟨112097164782499107728895341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74731443188332738485930227 112097164782499107728895341)
  ·
    refine ⟨42036436793437165398335753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112097164782499107728895341 42036436793437165398335753)
    ·
      refine ⟨31527327595077874048751815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42036436793437165398335753 31527327595077874048751815)
      ·
        refine ⟨47290991392616811073127723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31527327595077874048751815 47290991392616811073127723)
        ·
          refine ⟨70936487088925216609691585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47290991392616811073127723 70936487088925216609691585)
          ·
            refine ⟨53202365316693912457268689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70936487088925216609691585 53202365316693912457268689)
            ·
              refine ⟨39901773987520434342951517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53202365316693912457268689 39901773987520434342951517)
              ·
                refine ⟨14963165245320162878606819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39901773987520434342951517 14963165245320162878606819)
                ·
                  refine ⟨22444747867980244317910229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14963165245320162878606819 22444747867980244317910229)
                  ·
                    refine ⟨526048778155786976201021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22444747867980244317910229 526048778155786976201021)
                    ·
                      rfl

theorem cell23_3073429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_3073429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073429 prefixEnd_3073429 := by exact prefixLift 3073429
  have htrace : WordTrace (prefixWord ++ tailWord_3073429) baseStart_3073429 baseEnd_3073429 := by
    simpa [prefixWord, tailWord_3073429, baseEnd_3073429] using wordTrace_append hprefix tailTrace_3073429
  have hstable : (prefixWord ++ tailWord_3073429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073429).length < 2 ^ (prefixWord ++ tailWord_3073429).sum := by decide
  have hdescent : baseEnd_3073429 < baseStart_3073429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073449 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 4]
def baseStart_3073449 : Nat := 118140960795 + 3073449 * 2 ^ 59
def prefixEnd_3073449 : Nat := 4983230072969 + 3 ^ 40 * 3073449 * 2
def baseEnd_3073449 : Nat := 1578156604080450850352971

theorem tailTrace_3073449 : CollatzResearch.WordTrace tailWord_3073449 prefixEnd_3073449 1578156604080450850352971 := by
  unfold tailWord_3073449
  simp only [CollatzResearch.WordTrace]
  refine ⟨112097894242426651144623401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74731929494951100763082267 112097894242426651144623401)
  ·
    refine ⟨84073420681819988358467551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112097894242426651144623401 84073420681819988358467551)
    ·
      refine ⟨126110131022729982537701327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84073420681819988358467551 126110131022729982537701327)
      ·
        refine ⟨189165196534094973806551991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126110131022729982537701327 189165196534094973806551991)
        ·
          refine ⟨283747794801142460709827987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189165196534094973806551991 283747794801142460709827987)
          ·
            refine ⟨425621692201713691064741981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283747794801142460709827987 425621692201713691064741981)
            ·
              refine ⟨159608134575642634149278243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 425621692201713691064741981 159608134575642634149278243)
              ·
                refine ⟨239412201863463951223917365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159608134575642634149278243 239412201863463951223917365)
                ·
                  refine ⟨22444893924699745427242253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239412201863463951223917365 22444893924699745427242253)
                  ·
                    refine ⟨8416835221762404535215845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22444893924699745427242253 8416835221762404535215845)
                    ·
                      refine ⟨1578156604080450850352971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8416835221762404535215845 1578156604080450850352971)
                      ·
                        rfl

theorem cell23_3073449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_3073449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073449 prefixEnd_3073449 := by exact prefixLift 3073449
  have htrace : WordTrace (prefixWord ++ tailWord_3073449) baseStart_3073449 baseEnd_3073449 := by
    simpa [prefixWord, tailWord_3073449, baseEnd_3073449] using wordTrace_append hprefix tailTrace_3073449
  have hstable : (prefixWord ++ tailWord_3073449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073449).length < 2 ^ (prefixWord ++ tailWord_3073449).sum := by decide
  have hdescent : baseEnd_3073449 < baseStart_3073449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073607 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 1, 1, 4]
def baseStart_3073607 : Nat := 118140960795 + 3073607 * 2 ^ 59
def prefixEnd_3073607 : Nat := 4983230072969 + 3 ^ 40 * 3073607 * 2
def baseEnd_3073607 : Nat := 1578237734023861232177245

theorem tailTrace_3073607 : CollatzResearch.WordTrace tailWord_3073607 prefixEnd_3073607 1578237734023861232177245 := by
  unfold tailWord_3073607
  simp only [CollatzResearch.WordTrace]
  refine ⟨112103656975854244128875075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74735771317236162752583383 112103656975854244128875075)
  ·
    refine ⟨168155485463781366193312613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112103656975854244128875075 168155485463781366193312613)
    ·
      refine ⟨31529153524459006161246115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168155485463781366193312613 31529153524459006161246115)
      ·
        refine ⟨47293730286688509241869173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31529153524459006161246115 47293730286688509241869173)
        ·
          refine ⟨4433787214377047741425235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47293730286688509241869173 4433787214377047741425235)
          ·
            refine ⟨6650680821565571612137853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4433787214377047741425235 6650680821565571612137853)
            ·
              refine ⟨2494005308087089354551695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6650680821565571612137853 2494005308087089354551695)
              ·
                refine ⟨3741007962130634031827543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494005308087089354551695 3741007962130634031827543)
                ·
                  refine ⟨5611511943195951047741315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3741007962130634031827543 5611511943195951047741315)
                  ·
                    refine ⟨8417267914793926571611973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5611511943195951047741315 8417267914793926571611973)
                    ·
                      refine ⟨1578237734023861232177245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8417267914793926571611973 1578237734023861232177245)
                      ·
                        rfl

theorem cell23_3073607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_3073607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073607 prefixEnd_3073607 := by exact prefixLift 3073607
  have htrace : WordTrace (prefixWord ++ tailWord_3073607) baseStart_3073607 baseEnd_3073607 := by
    simpa [prefixWord, tailWord_3073607, baseEnd_3073607] using wordTrace_append hprefix tailTrace_3073607
  have hstable : (prefixWord ++ tailWord_3073607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073607).length < 2 ^ (prefixWord ++ tailWord_3073607).sum := by decide
  have hdescent : baseEnd_3073607 < baseStart_3073607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073613 : List Nat := [1, 6, 1, 1, 3, 11]
def baseStart_3073613 : Nat := 118140960795 + 3073613 * 2 ^ 59
def prefixEnd_3073613 : Nat := 4983230072969 + 3 ^ 40 * 3073613 * 2
def baseEnd_3073613 : Nat := 6494818168344807443219

theorem tailTrace_3073613 : CollatzResearch.WordTrace tailWord_3073613 prefixEnd_3073613 6494818168344807443219 := by
  unfold tailWord_3073613
  simp only [CollatzResearch.WordTrace]
  refine ⟨112103875813832507153593493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74735917209221671435728995 112103875813832507153593493)
  ·
    refine ⟨5254869178773398772824695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112103875813832507153593493 5254869178773398772824695)
    ·
      refine ⟨7882303768160098159237043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5254869178773398772824695 7882303768160098159237043)
      ·
        refine ⟨11823455652240147238855565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7882303768160098159237043 11823455652240147238855565)
        ·
          refine ⟨4433795869590055214570837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11823455652240147238855565 4433795869590055214570837)
          ·
            refine ⟨6494818168344807443219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4433795869590055214570837 6494818168344807443219)
            ·
              rfl

theorem cell23_3073613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 11].length) (baseStart_3073613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073613 prefixEnd_3073613 := by exact prefixLift 3073613
  have htrace : WordTrace (prefixWord ++ tailWord_3073613) baseStart_3073613 baseEnd_3073613 := by
    simpa [prefixWord, tailWord_3073613, baseEnd_3073613] using wordTrace_append hprefix tailTrace_3073613
  have hstable : (prefixWord ++ tailWord_3073613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073613).length < 2 ^ (prefixWord ++ tailWord_3073613).sum := by decide
  have hdescent : baseEnd_3073613 < baseStart_3073613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073640 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3073640 : Nat := 118140960795 + 3073640 * 2 ^ 59
def prefixEnd_3073640 : Nat := 4983230072969 + 3 ^ 40 * 3073640 * 2
def baseEnd_3073640 : Nat := 1578254678885459603064593

theorem tailTrace_3073640 : CollatzResearch.WordTrace tailWord_3073640 prefixEnd_3073640 1578254678885459603064593 := by
  unfold tailWord_3073640
  simp only [CollatzResearch.WordTrace]
  refine ⟨56052430292367345382413187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74736573723156460509884249 56052430292367345382413187)
  ·
    refine ⟨84078645438551018073619781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56052430292367345382413187 84078645438551018073619781)
    ·
      refine ⟨15764746019728315888803709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84078645438551018073619781 15764746019728315888803709)
      ·
        refine ⟨5911779757398118458301391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15764746019728315888803709 5911779757398118458301391)
        ·
          refine ⟨8867669636097177687452087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911779757398118458301391 8867669636097177687452087)
          ·
            refine ⟨13301504454145766531178131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8867669636097177687452087 13301504454145766531178131)
            ·
              refine ⟨19952256681218649796767197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13301504454145766531178131 19952256681218649796767197)
              ·
                refine ⟨7482096255456993673787699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19952256681218649796767197 7482096255456993673787699)
                ·
                  refine ⟨11223144383185490510681549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7482096255456993673787699 11223144383185490510681549)
                  ·
                    refine ⟨4208679143694558941505581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11223144383185490510681549 4208679143694558941505581)
                    ·
                      refine ⟨1578254678885459603064593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4208679143694558941505581 1578254678885459603064593)
                      ·
                        rfl

theorem cell23_3073640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3073640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073640 prefixEnd_3073640 := by exact prefixLift 3073640
  have htrace : WordTrace (prefixWord ++ tailWord_3073640) baseStart_3073640 baseEnd_3073640 := by
    simpa [prefixWord, tailWord_3073640, baseEnd_3073640] using wordTrace_append hprefix tailTrace_3073640
  have hstable : (prefixWord ++ tailWord_3073640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073640).length < 2 ^ (prefixWord ++ tailWord_3073640).sum := by decide
  have hdescent : baseEnd_3073640 < baseStart_3073640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073656 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 6, 6]
def baseStart_3073656 : Nat := 118140960795 + 3073656 * 2 ^ 59
def prefixEnd_3073656 : Nat := 4983230072969 + 3 ^ 40 * 3073656 * 2
def baseEnd_3073656 : Nat := 526087631525310513488173

theorem tailTrace_3073656 : CollatzResearch.WordTrace tailWord_3073656 prefixEnd_3073656 526087631525310513488173 := by
  unfold tailWord_3073656
  simp only [CollatzResearch.WordTrace]
  refine ⟨56052722076338362748704411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74736962768451150331605881 56052722076338362748704411)
  ·
    refine ⟨84079083114507544123056617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56052722076338362748704411 84079083114507544123056617)
    ·
      refine ⟨63059312335880658092292463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84079083114507544123056617 63059312335880658092292463)
      ·
        refine ⟨94588968503820987138438695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63059312335880658092292463 94588968503820987138438695)
        ·
          refine ⟨141883452755731480707658043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94588968503820987138438695 141883452755731480707658043)
          ·
            refine ⟨212825179133597221061487065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141883452755731480707658043 212825179133597221061487065)
            ·
              refine ⟨159618884350197915796115299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212825179133597221061487065 159618884350197915796115299)
              ·
                refine ⟨239428326525296873694172949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159618884350197915796115299 239428326525296873694172949)
                ·
                  refine ⟨11223202805873290954414357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 239428326525296873694172949 11223202805873290954414357)
                  ·
                    refine ⟨526087631525310513488173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11223202805873290954414357 526087631525310513488173)
                    ·
                      rfl

theorem cell23_3073656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_3073656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073656 prefixEnd_3073656 := by exact prefixLift 3073656
  have htrace : WordTrace (prefixWord ++ tailWord_3073656) baseStart_3073656 baseEnd_3073656 := by
    simpa [prefixWord, tailWord_3073656, baseEnd_3073656] using wordTrace_append hprefix tailTrace_3073656
  have hstable : (prefixWord ++ tailWord_3073656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073656).length < 2 ^ (prefixWord ++ tailWord_3073656).sum := by decide
  have hdescent : baseEnd_3073656 < baseStart_3073656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073663 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 2, 8, 2]
def baseStart_3073663 : Nat := 118140960795 + 3073663 * 2 ^ 59
def prefixEnd_3073663 : Nat := 4983230072969 + 3 ^ 40 * 3073663 * 2
def baseEnd_3073663 : Nat := 1578266488940513013076987

theorem tailTrace_3073663 : CollatzResearch.WordTrace tailWord_3073663 prefixEnd_3073663 1578266488940513013076987 := by
  unfold tailWord_3073663
  simp only [CollatzResearch.WordTrace]
  refine ⟨112105699463651365692913643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74737132975767577128609095 112105699463651365692913643)
  ·
    refine ⟨168158549195477048539370465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112105699463651365692913643 168158549195477048539370465)
    ·
      refine ⟨126118911896607786404527849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168158549195477048539370465 126118911896607786404527849)
      ·
        refine ⟨94589183922455839803395887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126118911896607786404527849 94589183922455839803395887)
        ·
          refine ⟨141883775883683759705093831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94589183922455839803395887 141883775883683759705093831)
          ·
            refine ⟨212825663825525639557640747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141883775883683759705093831 212825663825525639557640747)
            ·
              refine ⟨319238495738288459336461121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212825663825525639557640747 319238495738288459336461121)
              ·
                refine ⟨239428871803716344502345841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319238495738288459336461121 239428871803716344502345841)
                ·
                  refine ⟨179571653852787258376759381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239428871803716344502345841 179571653852787258376759381)
                  ·
                    refine ⟨2104355318587350684102649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 179571653852787258376759381 2104355318587350684102649)
                    ·
                      refine ⟨1578266488940513013076987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104355318587350684102649 1578266488940513013076987)
                      ·
                        rfl

theorem cell23_3073663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 8, 2].length) (baseStart_3073663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073663 prefixEnd_3073663 := by exact prefixLift 3073663
  have htrace : WordTrace (prefixWord ++ tailWord_3073663) baseStart_3073663 baseEnd_3073663 := by
    simpa [prefixWord, tailWord_3073663, baseEnd_3073663] using wordTrace_append hprefix tailTrace_3073663
  have hstable : (prefixWord ++ tailWord_3073663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073663).length < 2 ^ (prefixWord ++ tailWord_3073663).sum := by decide
  have hdescent : baseEnd_3073663 < baseStart_3073663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073674 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_3073674 : Nat := 118140960795 + 3073674 * 2 ^ 59
def prefixEnd_3073674 : Nat := 4983230072969 + 3 ^ 40 * 3073674 * 2
def baseEnd_3073674 : Nat := 1578272137227712470039437

theorem tailTrace_3073674 : CollatzResearch.WordTrace tailWord_3073674 prefixEnd_3073674 1578272137227712470039437 := by
  unfold tailWord_3073674
  simp only [CollatzResearch.WordTrace]
  refine ⟨28026525166652878642891019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74737400444407676381042717 28026525166652878642891019)
  ·
    refine ⟨42039787749979317964336529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28026525166652878642891019 42039787749979317964336529)
    ·
      refine ⟨31529840812484488473252397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42039787749979317964336529 31529840812484488473252397)
      ·
        refine ⟨11823690304681683177469649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31529840812484488473252397 11823690304681683177469649)
        ·
          refine ⟨8867767728511262383102237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11823690304681683177469649 8867767728511262383102237)
          ·
            refine ⟨3325412898191723393663339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8867767728511262383102237 3325412898191723393663339)
            ·
              refine ⟨4988119347287585090495009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3325412898191723393663339 4988119347287585090495009)
              ·
                refine ⟨3741089510465688817871257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4988119347287585090495009 3741089510465688817871257)
                ·
                  refine ⟨2805817132849266613403443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3741089510465688817871257 2805817132849266613403443)
                  ·
                    refine ⟨4208725699273899920105165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2805817132849266613403443 4208725699273899920105165)
                    ·
                      refine ⟨1578272137227712470039437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4208725699273899920105165 1578272137227712470039437)
                      ·
                        rfl

theorem cell23_3073674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_3073674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073674 prefixEnd_3073674 := by exact prefixLift 3073674
  have htrace : WordTrace (prefixWord ++ tailWord_3073674) baseStart_3073674 baseEnd_3073674 := by
    simpa [prefixWord, tailWord_3073674, baseEnd_3073674] using wordTrace_append hprefix tailTrace_3073674
  have hstable : (prefixWord ++ tailWord_3073674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073674).length < 2 ^ (prefixWord ++ tailWord_3073674).sum := by decide
  have hdescent : baseEnd_3073674 < baseStart_3073674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073697 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 1, 4, 2]
def baseStart_3073697 : Nat := 118140960795 + 3073697 * 2 ^ 59
def prefixEnd_3073697 : Nat := 4983230072969 + 3 ^ 40 * 3073697 * 2
def baseEnd_3073697 : Nat := 1578283947282765880051831

theorem tailTrace_3073697 : CollatzResearch.WordTrace tailWord_3073697 prefixEnd_3073697 1578283947282765880051831 := by
  unfold tailWord_3073697
  simp only [CollatzResearch.WordTrace]
  refine ⟨112106939545528189499651345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74737959697018792999767563 112106939545528189499651345)
  ·
    refine ⟨84080204659146142124738509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112106939545528189499651345 84080204659146142124738509)
    ·
      refine ⟨31530076747179803296776941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84080204659146142124738509 31530076747179803296776941)
      ·
        refine ⟨11823778780192426236291353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31530076747179803296776941 11823778780192426236291353)
        ·
          refine ⟨8867834085144319677218515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11823778780192426236291353 8867834085144319677218515)
          ·
            refine ⟨13301751127716479515827773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8867834085144319677218515 13301751127716479515827773)
            ·
              refine ⟨4988156672893679818435415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13301751127716479515827773 4988156672893679818435415)
              ·
                refine ⟨7482235009340519727653123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4988156672893679818435415 7482235009340519727653123)
                ·
                  refine ⟨11223352514010779591479685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7482235009340519727653123 11223352514010779591479685)
                  ·
                    refine ⟨2104378596377021173402441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11223352514010779591479685 2104378596377021173402441)
                    ·
                      refine ⟨1578283947282765880051831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104378596377021173402441 1578283947282765880051831)
                      ·
                        rfl

theorem cell23_3073697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_3073697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073697 prefixEnd_3073697 := by exact prefixLift 3073697
  have htrace : WordTrace (prefixWord ++ tailWord_3073697) baseStart_3073697 baseEnd_3073697 := by
    simpa [prefixWord, tailWord_3073697, baseEnd_3073697] using wordTrace_append hprefix tailTrace_3073697
  have hstable : (prefixWord ++ tailWord_3073697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073697).length < 2 ^ (prefixWord ++ tailWord_3073697).sum := by decide
  have hdescent : baseEnd_3073697 < baseStart_3073697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073733 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_3073733 : Nat := 118140960795 + 3073733 * 2 ^ 59
def prefixEnd_3073733 : Nat := 4983230072969 + 3 ^ 40 * 3073733 * 2
def baseEnd_3073733 : Nat := 526100810862109246400555

theorem tailTrace_3073733 : CollatzResearch.WordTrace tailWord_3073733 prefixEnd_3073733 526100810862109246400555 := by
  unfold tailWord_3073733
  simp only [CollatzResearch.WordTrace]
  refine ⟨112108252573397767647961853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74738835048931845098641235 112108252573397767647961853)
  ·
    refine ⟨42040594715024162867985695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112108252573397767647961853 42040594715024162867985695)
    ·
      refine ⟨63060892072536244301978543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42040594715024162867985695 63060892072536244301978543)
      ·
        refine ⟨94591338108804366452967815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63060892072536244301978543 94591338108804366452967815)
        ·
          refine ⟨141887007163206549679451723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94591338108804366452967815 141887007163206549679451723)
          ·
            refine ⟨212830510744809824519177585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141887007163206549679451723 212830510744809824519177585)
            ·
              refine ⟨159622883058607368389383189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212830510744809824519177585 159622883058607368389383189)
              ·
                refine ⟨7482322643372220393252337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159622883058607368389383189 7482322643372220393252337)
                ·
                  refine ⟨5611741982529165294939253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7482322643372220393252337 5611741982529165294939253)
                  ·
                    refine ⟨526100810862109246400555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5611741982529165294939253 526100810862109246400555)
                    ·
                      rfl

theorem cell23_3073733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_3073733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073733 prefixEnd_3073733 := by exact prefixLift 3073733
  have htrace : WordTrace (prefixWord ++ tailWord_3073733) baseStart_3073733 baseEnd_3073733 := by
    simpa [prefixWord, tailWord_3073733, baseEnd_3073733] using wordTrace_append hprefix tailTrace_3073733
  have hstable : (prefixWord ++ tailWord_3073733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073733).length < 2 ^ (prefixWord ++ tailWord_3073733).sum := by decide
  have hdescent : baseEnd_3073733 < baseStart_3073733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073748 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3073748 : Nat := 118140960795 + 3073748 * 2 ^ 59
def prefixEnd_3073748 : Nat := 4983230072969 + 3 ^ 40 * 3073748 * 2
def baseEnd_3073748 : Nat := 1578310134796145180514097

theorem tailTrace_3073748 : CollatzResearch.WordTrace tailWord_3073748 prefixEnd_3073748 1578310134796145180514097 := by
  unfold tailWord_3073748
  simp only [CollatzResearch.WordTrace]
  refine ⟨56054399834171712604878949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74739199778895616806505265 56054399834171712604878949)
  ·
    refine ⟨10510199968907196113414803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56054399834171712604878949 10510199968907196113414803)
    ·
      refine ⟨15765299953360794170122205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10510199968907196113414803 15765299953360794170122205)
      ·
        refine ⟨5911987482510297813795827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15765299953360794170122205 5911987482510297813795827)
        ·
          refine ⟨8867981223765446720693741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911987482510297813795827 8867981223765446720693741)
          ·
            refine ⟨3325492958912042520260153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8867981223765446720693741 3325492958912042520260153)
            ·
              refine ⟨2494119719184031890195115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3325492958912042520260153 2494119719184031890195115)
              ·
                refine ⟨3741179578776047835292673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494119719184031890195115 3741179578776047835292673)
                ·
                  refine ⟨2805884684082035876469505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3741179578776047835292673 2805884684082035876469505)
                  ·
                    refine ⟨2104413513061526907352129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2805884684082035876469505 2104413513061526907352129)
                    ·
                      refine ⟨1578310134796145180514097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104413513061526907352129 1578310134796145180514097)
                      ·
                        rfl

theorem cell23_3073748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3073748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073748 prefixEnd_3073748 := by exact prefixLift 3073748
  have htrace : WordTrace (prefixWord ++ tailWord_3073748) baseStart_3073748 baseEnd_3073748 := by
    simpa [prefixWord, tailWord_3073748, baseEnd_3073748] using wordTrace_append hprefix tailTrace_3073748
  have hstable : (prefixWord ++ tailWord_3073748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073748).length < 2 ^ (prefixWord ++ tailWord_3073748).sum := by decide
  have hdescent : baseEnd_3073748 < baseStart_3073748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073770 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_3073770 : Nat := 118140960795 + 3073770 * 2 ^ 59
def prefixEnd_3073770 : Nat := 4983230072969 + 3 ^ 40 * 3073770 * 2
def baseEnd_3073770 : Nat := 1578321431370544094438995

theorem tailTrace_3073770 : CollatzResearch.WordTrace tailWord_3073770 prefixEnd_3073770 1578321431370544094438995 := by
  unfold tailWord_3073770
  simp only [CollatzResearch.WordTrace]
  refine ⟨28027400518565930741764691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74739734716175815311372509 28027400518565930741764691)
  ·
    refine ⟨42041100777848896112647037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28027400518565930741764691 42041100777848896112647037)
    ·
      refine ⟨15765412791693336042242639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42041100777848896112647037 15765412791693336042242639)
      ·
        refine ⟨23648119187540004063363959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15765412791693336042242639 23648119187540004063363959)
        ·
          refine ⟨35472178781310006095045939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23648119187540004063363959 35472178781310006095045939)
          ·
            refine ⟨53208268171965009142568909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35472178781310006095045939 53208268171965009142568909)
            ·
              refine ⟨19953100564486878428463341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53208268171965009142568909 19953100564486878428463341)
              ·
                refine ⟨7482412711682579410673753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19953100564486878428463341 7482412711682579410673753)
                ·
                  refine ⟨5611809533761934558005315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7482412711682579410673753 5611809533761934558005315)
                  ·
                    refine ⟨8417714300642901837007973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5611809533761934558005315 8417714300642901837007973)
                    ·
                      refine ⟨1578321431370544094438995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8417714300642901837007973 1578321431370544094438995)
                      ·
                        rfl

theorem cell23_3073770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_3073770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073770 prefixEnd_3073770 := by exact prefixLift 3073770
  have htrace : WordTrace (prefixWord ++ tailWord_3073770) baseStart_3073770 baseEnd_3073770 := by
    simpa [prefixWord, tailWord_3073770, baseEnd_3073770] using wordTrace_append hprefix tailTrace_3073770
  have hstable : (prefixWord ++ tailWord_3073770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073770).length < 2 ^ (prefixWord ++ tailWord_3073770).sum := by decide
  have hdescent : baseEnd_3073770 < baseStart_3073770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073793 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 8]
def baseStart_3073793 : Nat := 118140960795 + 3073793 * 2 ^ 59
def prefixEnd_3073793 : Nat := 4983230072969 + 3 ^ 40 * 3073793 * 2
def baseEnd_3073793 : Nat := 175370360158399722716821

theorem tailTrace_3073793 : CollatzResearch.WordTrace tailWord_3073793 prefixEnd_3073793 175370360158399722716821 := by
  unfold tailWord_3073793
  simp only [CollatzResearch.WordTrace]
  refine ⟨112110440953180397895146033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74740293968786931930097355 112110440953180397895146033)
  ·
    refine ⟨84082830714885298421359525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112110440953180397895146033 84082830714885298421359525)
    ·
      refine ⟨15765530759040993454004911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84082830714885298421359525 15765530759040993454004911)
      ·
        refine ⟨23648296138561490181007367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15765530759040993454004911 23648296138561490181007367)
        ·
          refine ⟨35472444207842235271511051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23648296138561490181007367 35472444207842235271511051)
          ·
            refine ⟨53208666311763352907266577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35472444207842235271511051 53208666311763352907266577)
            ·
              refine ⟨39906499733822514680449933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53208666311763352907266577 39906499733822514680449933)
              ·
                refine ⟨14964937400183443005168725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39906499733822514680449933 14964937400183443005168725)
                ·
                  refine ⟨175370360158399722716821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14964937400183443005168725 175370360158399722716821)
                  ·
                    rfl

theorem cell23_3073793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 8].length) (baseStart_3073793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073793 prefixEnd_3073793 := by exact prefixLift 3073793
  have htrace : WordTrace (prefixWord ++ tailWord_3073793) baseStart_3073793 baseEnd_3073793 := by
    simpa [prefixWord, tailWord_3073793, baseEnd_3073793] using wordTrace_append hprefix tailTrace_3073793
  have hstable : (prefixWord ++ tailWord_3073793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073793).length < 2 ^ (prefixWord ++ tailWord_3073793).sum := by decide
  have hdescent : baseEnd_3073793 < baseStart_3073793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073844 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 6]
def baseStart_3073844 : Nat := 118140960795 + 3073844 * 2 ^ 59
def prefixEnd_3073844 : Nat := 4983230072969 + 3 ^ 40 * 3073844 * 2
def baseEnd_3073844 : Nat := 175373269882108533879295

theorem tailTrace_3073844 : CollatzResearch.WordTrace tailWord_3073844 prefixEnd_3073844 175373269882108533879295 := by
  unfold tailWord_3073844
  simp only [CollatzResearch.WordTrace]
  refine ⟨56056150537997816802626293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74741534050663755736835057 56056150537997816802626293)
  ·
    refine ⟨5255264112937295325246215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56056150537997816802626293 5255264112937295325246215)
    ·
      refine ⟨7882896169405942987869323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5255264112937295325246215 7882896169405942987869323)
      ·
        refine ⟨11824344254108914481803985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7882896169405942987869323 11824344254108914481803985)
        ·
          refine ⟨8868258190581685861352989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11824344254108914481803985 8868258190581685861352989)
          ·
            refine ⟨3325596821468132198007371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8868258190581685861352989 3325596821468132198007371)
            ·
              refine ⟨4988395232202198297011057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3325596821468132198007371 4988395232202198297011057)
              ·
                refine ⟨3741296424151648722758293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4988395232202198297011057 3741296424151648722758293)
                ·
                  refine ⟨175373269882108533879295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3741296424151648722758293 175373269882108533879295)
                  ·
                    rfl

theorem cell23_3073844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_3073844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073844 prefixEnd_3073844 := by exact prefixLift 3073844
  have htrace : WordTrace (prefixWord ++ tailWord_3073844) baseStart_3073844 baseEnd_3073844 := by
    simpa [prefixWord, tailWord_3073844, baseEnd_3073844] using wordTrace_append hprefix tailTrace_3073844
  have hstable : (prefixWord ++ tailWord_3073844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073844).length < 2 ^ (prefixWord ++ tailWord_3073844).sum := by decide
  have hdescent : baseEnd_3073844 < baseStart_3073844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073854 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_3073854 : Nat := 118140960795 + 3073854 * 2 ^ 59
def prefixEnd_3073854 : Nat := 4983230072969 + 3 ^ 40 * 3073854 * 2
def baseEnd_3073854 : Nat := 1578364563745521765788609

theorem tailTrace_3073854 : CollatzResearch.WordTrace tailWord_3073854 prefixEnd_3073854 1578364563745521765788609 := by
  unfold tailWord_3073854
  simp only [CollatzResearch.WordTrace]
  refine ⟨14014083225744925664139577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 74741777203972936875411077 14014083225744925664139577)
  ·
    refine ⟨10510562419308694248104683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14014083225744925664139577 10510562419308694248104683)
    ·
      refine ⟨15765843628963041372157025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10510562419308694248104683 15765843628963041372157025)
      ·
        refine ⟨11824382721722281029117769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15765843628963041372157025 11824382721722281029117769)
        ·
          refine ⟨8868287041291710771838327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11824382721722281029117769 8868287041291710771838327)
          ·
            refine ⟨13302430561937566157757491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8868287041291710771838327 13302430561937566157757491)
            ·
              refine ⟨19953645842906349236636237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13302430561937566157757491 19953645842906349236636237)
              ·
                refine ⟨7482617191089880963738589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19953645842906349236636237 7482617191089880963738589)
                ·
                  refine ⟨2805981446658705361401971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7482617191089880963738589 2805981446658705361401971)
                  ·
                    refine ⟨4208972169988058042102957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2805981446658705361401971 4208972169988058042102957)
                    ·
                      refine ⟨1578364563745521765788609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4208972169988058042102957 1578364563745521765788609)
                      ·
                        rfl

theorem cell23_3073854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_3073854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073854 prefixEnd_3073854 := by exact prefixLift 3073854
  have htrace : WordTrace (prefixWord ++ tailWord_3073854) baseStart_3073854 baseEnd_3073854 := by
    simpa [prefixWord, tailWord_3073854, baseEnd_3073854] using wordTrace_append hprefix tailTrace_3073854
  have hstable : (prefixWord ++ tailWord_3073854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073854).length < 2 ^ (prefixWord ++ tailWord_3073854).sum := by decide
  have hdescent : baseEnd_3073854 < baseStart_3073854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073877 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_3073877 : Nat := 118140960795 + 3073877 * 2 ^ 59
def prefixEnd_3073877 : Nat := 4983230072969 + 3 ^ 40 * 3073877 * 2
def baseEnd_3073877 : Nat := 1578376373800575175801003

theorem tailTrace_3073877 : CollatzResearch.WordTrace tailWord_3073877 prefixEnd_3073877 1578376373800575175801003 := by
  unfold tailWord_3073877
  simp only [CollatzResearch.WordTrace]
  refine ⟨112113504684876080241203885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74742336456584053494135923 112113504684876080241203885)
  ·
    refine ⟨42042564256828530090451457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112113504684876080241203885 42042564256828530090451457)
    ·
      refine ⟨31531923192621397567838593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42042564256828530090451457 31531923192621397567838593)
      ·
        refine ⟨23648942394466048175878945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31531923192621397567838593 23648942394466048175878945)
        ·
          refine ⟨17736706795849536131909209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23648942394466048175878945 17736706795849536131909209)
          ·
            refine ⟨13302530096887152098931907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17736706795849536131909209 13302530096887152098931907)
            ·
              refine ⟨19953795145330728148397861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13302530096887152098931907 19953795145330728148397861)
              ·
                refine ⟨3741336589749511527824599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19953795145330728148397861 3741336589749511527824599)
                ·
                  refine ⟨5612004884624267291736899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3741336589749511527824599 5612004884624267291736899)
                  ·
                    refine ⟨8418007326936400937605349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5612004884624267291736899 8418007326936400937605349)
                    ·
                      refine ⟨1578376373800575175801003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8418007326936400937605349 1578376373800575175801003)
                      ·
                        rfl

theorem cell23_3073877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_3073877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073877 prefixEnd_3073877 := by exact prefixLift 3073877
  have htrace : WordTrace (prefixWord ++ tailWord_3073877) baseStart_3073877 baseEnd_3073877 := by
    simpa [prefixWord, tailWord_3073877, baseEnd_3073877] using wordTrace_append hprefix tailTrace_3073877
  have hstable : (prefixWord ++ tailWord_3073877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073877).length < 2 ^ (prefixWord ++ tailWord_3073877).sum := by decide
  have hdescent : baseEnd_3073877 < baseStart_3073877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073900 : List Nat := [2, 2, 1, 1, 4, 4, 9]
def baseStart_3073900 : Nat := 118140960795 + 3073900 * 2 ^ 59
def prefixEnd_3073900 : Nat := 4983230072969 + 3 ^ 40 * 3073900 * 2
def baseEnd_3073900 : Nat := 19486273874760846738437

theorem tailTrace_3073900 : CollatzResearch.WordTrace tailWord_3073900 prefixEnd_3073900 19486273874760846738437 := by
  unfold tailWord_3073900
  simp only [CollatzResearch.WordTrace]
  refine ⟨56057171781896377584645577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74742895709195170112860769 56057171781896377584645577)
  ·
    refine ⟨42042878836422283188484183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56057171781896377584645577 42042878836422283188484183)
    ·
      refine ⟨63064318254633424782726275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42042878836422283188484183 63064318254633424782726275)
      ·
        refine ⟨94596477381950137174089413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63064318254633424782726275 94596477381950137174089413)
        ·
          refine ⟨17736839509115650720141765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94596477381950137174089413 17736839509115650720141765)
          ·
            refine ⟨3325657407959184510026581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17736839509115650720141765 3325657407959184510026581)
            ·
              refine ⟨19486273874760846738437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3325657407959184510026581 19486273874760846738437)
              ·
                rfl

theorem cell23_3073900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 9].length) (baseStart_3073900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073900 prefixEnd_3073900 := by exact prefixLift 3073900
  have htrace : WordTrace (prefixWord ++ tailWord_3073900) baseStart_3073900 baseEnd_3073900 := by
    simpa [prefixWord, tailWord_3073900, baseEnd_3073900] using wordTrace_append hprefix tailTrace_3073900
  have hstable : (prefixWord ++ tailWord_3073900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073900).length < 2 ^ (prefixWord ++ tailWord_3073900).sum := by decide
  have hdescent : baseEnd_3073900 < baseStart_3073900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073921 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 2, 4]
def baseStart_3073921 : Nat := 118140960795 + 3073921 * 2 ^ 59
def prefixEnd_3073921 : Nat := 4983230072969 + 3 ^ 40 * 3073921 * 2
def baseEnd_3073921 : Nat := 526132988983124334550267

theorem tailTrace_3073921 : CollatzResearch.WordTrace tailWord_3073921 prefixEnd_3073921 526132988983124334550267 := by
  unfold tailWord_3073921
  simp only [CollatzResearch.WordTrace]
  refine ⟨112115109496716675755805617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74743406331144450503870411 112115109496716675755805617)
  ·
    refine ⟨84086332122537506816854213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112115109496716675755805617 84086332122537506816854213)
    ·
      refine ⟨15766187272975782528160165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84086332122537506816854213 15766187272975782528160165)
      ·
        refine ⟨2956160113682959224030031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15766187272975782528160165 2956160113682959224030031)
        ·
          refine ⟨4434240170524438836045047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956160113682959224030031 4434240170524438836045047)
          ·
            refine ⟨6651360255786658254067571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434240170524438836045047 6651360255786658254067571)
            ·
              refine ⟨9977040383679987381101357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6651360255786658254067571 9977040383679987381101357)
              ·
                refine ⟨3741390143879995267913009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9977040383679987381101357 3741390143879995267913009)
                ·
                  refine ⟨2806042607909996450934757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3741390143879995267913009 2806042607909996450934757)
                  ·
                    refine ⟨526132988983124334550267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2806042607909996450934757 526132988983124334550267)
                    ·
                      rfl

theorem cell23_3073921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_3073921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073921 prefixEnd_3073921 := by exact prefixLift 3073921
  have htrace : WordTrace (prefixWord ++ tailWord_3073921) baseStart_3073921 baseEnd_3073921 := by
    simpa [prefixWord, tailWord_3073921, baseEnd_3073921] using wordTrace_append hprefix tailTrace_3073921
  have hstable : (prefixWord ++ tailWord_3073921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073921).length < 2 ^ (prefixWord ++ tailWord_3073921).sum := by decide
  have hdescent : baseEnd_3073921 < baseStart_3073921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073967 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 3, 4, 2]
def baseStart_3073967 : Nat := 118140960795 + 3073967 * 2 ^ 59
def prefixEnd_3073967 : Nat := 4983230072969 + 3 ^ 40 * 3073967 * 2
def baseEnd_3073967 : Nat := 1578422587059479823675589

theorem tailTrace_3073967 : CollatzResearch.WordTrace tailWord_3073967 prefixEnd_3073967 1578422587059479823675589 := by
  unfold tailWord_3073967
  simp only [CollatzResearch.WordTrace]
  refine ⟨112116787254550025611980155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74744524836366683741320103 112116787254550025611980155)
  ·
    refine ⟨168175180881825038417970233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112116787254550025611980155 168175180881825038417970233)
    ·
      refine ⟨126131385661368778813477675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168175180881825038417970233 126131385661368778813477675)
      ·
        refine ⟨189197078492053168220216513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126131385661368778813477675 189197078492053168220216513)
        ·
          refine ⟨141897808869039876165162385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189197078492053168220216513 141897808869039876165162385)
          ·
            refine ⟨106423356651779907123871789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141897808869039876165162385 106423356651779907123871789)
            ·
              refine ⟨39908758744417465171451921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106423356651779907123871789 39908758744417465171451921)
              ·
                refine ⟨29931569058313098878588941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39908758744417465171451921 29931569058313098878588941)
                ·
                  refine ⟨11224338396867412079470853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29931569058313098878588941 11224338396867412079470853)
                  ·
                    refine ⟨2104563449412639764900785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11224338396867412079470853 2104563449412639764900785)
                    ·
                      refine ⟨1578422587059479823675589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104563449412639764900785 1578422587059479823675589)
                      ·
                        rfl

theorem cell23_3073967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 4, 2].length) (baseStart_3073967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073967 prefixEnd_3073967 := by exact prefixLift 3073967
  have htrace : WordTrace (prefixWord ++ tailWord_3073967) baseStart_3073967 baseEnd_3073967 := by
    simpa [prefixWord, tailWord_3073967, baseEnd_3073967] using wordTrace_append hprefix tailTrace_3073967
  have hstable : (prefixWord ++ tailWord_3073967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073967).length < 2 ^ (prefixWord ++ tailWord_3073967).sum := by decide
  have hdescent : baseEnd_3073967 < baseStart_3073967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073970 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3073970 : Nat := 118140960795 + 3073970 * 2 ^ 59
def prefixEnd_3073970 : Nat := 4983230072969 + 3 ^ 40 * 3073970 * 2
def baseEnd_3073970 : Nat := 1578424127501443311938075

theorem tailTrace_3073970 : CollatzResearch.WordTrace tailWord_3073970 prefixEnd_3073970 1578424127501443311938075 := by
  unfold tailWord_3073970
  simp only [CollatzResearch.WordTrace]
  refine ⟨28029224168384789281084841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74744597782359438082892909 28029224168384789281084841)
  ·
    refine ⟨21021918126288591960813631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28029224168384789281084841 21021918126288591960813631)
    ·
      refine ⟨31532877189432887941220447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21021918126288591960813631 31532877189432887941220447)
      ·
        refine ⟨47299315784149331911830671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31532877189432887941220447 47299315784149331911830671)
        ·
          refine ⟨70948973676223997867746007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47299315784149331911830671 70948973676223997867746007)
          ·
            refine ⟨106423460514335996801619011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70948973676223997867746007 106423460514335996801619011)
            ·
              refine ⟨159635190771503995202428517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106423460514335996801619011 159635190771503995202428517)
              ·
                refine ⟨29931598269656999100455347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159635190771503995202428517 29931598269656999100455347)
                ·
                  refine ⟨44897397404485498650683021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29931598269656999100455347 44897397404485498650683021)
                  ·
                    refine ⟨16836524026682061994006133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44897397404485498650683021 16836524026682061994006133)
                    ·
                      refine ⟨1578424127501443311938075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16836524026682061994006133 1578424127501443311938075)
                      ·
                        rfl

theorem cell23_3073970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3073970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073970 prefixEnd_3073970 := by exact prefixLift 3073970
  have htrace : WordTrace (prefixWord ++ tailWord_3073970) baseStart_3073970 baseEnd_3073970 := by
    simpa [prefixWord, tailWord_3073970, baseEnd_3073970] using wordTrace_append hprefix tailTrace_3073970
  have hstable : (prefixWord ++ tailWord_3073970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073970).length < 2 ^ (prefixWord ++ tailWord_3073970).sum := by decide
  have hdescent : baseEnd_3073970 < baseStart_3073970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3073984 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 1, 4, 2]
def baseStart_3073984 : Nat := 118140960795 + 3073984 * 2 ^ 59
def prefixEnd_3073984 : Nat := 4983230072969 + 3 ^ 40 * 3073984 * 2
def baseEnd_3073984 : Nat := 1578431316230606257163011

theorem tailTrace_3073984 : CollatzResearch.WordTrace tailWord_3073984 prefixEnd_3073984 1578431316230606257163011 := by
  unfold tailWord_3073984
  simp only [CollatzResearch.WordTrace]
  refine ⟨56058703647744218757674503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74744938196992291676899337 56058703647744218757674503)
  ·
    refine ⟨84088055471616328136511755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56058703647744218757674503 84088055471616328136511755)
    ·
      refine ⟨126132083207424492204767633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84088055471616328136511755 126132083207424492204767633)
      ·
        refine ⟨94599062405568369153575725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126132083207424492204767633 94599062405568369153575725)
        ·
          refine ⟨35474648402088138432590897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94599062405568369153575725 35474648402088138432590897)
          ·
            refine ⟨26605986301566103824443173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35474648402088138432590897 26605986301566103824443173)
            ·
              refine ⟨4988622431543644467083095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26605986301566103824443173 4988622431543644467083095)
              ·
                refine ⟨7482933647315466700624643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4988622431543644467083095 7482933647315466700624643)
                ·
                  refine ⟨11224400470973200050936965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7482933647315466700624643 11224400470973200050936965)
                  ·
                    refine ⟨2104575088307475009550681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11224400470973200050936965 2104575088307475009550681)
                    ·
                      refine ⟨1578431316230606257163011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104575088307475009550681 1578431316230606257163011)
                      ·
                        rfl

theorem cell23_3073984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 4, 2].length) (baseStart_3073984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3073984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3073984 prefixEnd_3073984 := by exact prefixLift 3073984
  have htrace : WordTrace (prefixWord ++ tailWord_3073984) baseStart_3073984 baseEnd_3073984 := by
    simpa [prefixWord, tailWord_3073984, baseEnd_3073984] using wordTrace_append hprefix tailTrace_3073984
  have hstable : (prefixWord ++ tailWord_3073984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3073984).length < 2 ^ (prefixWord ++ tailWord_3073984).sum := by decide
  have hdescent : baseEnd_3073984 < baseStart_3073984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3073984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074012 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3074012 : Nat := 118140960795 + 3074012 * 2 ^ 59
def prefixEnd_3074012 : Nat := 4983230072969 + 3 ^ 40 * 3074012 * 2
def baseEnd_3074012 : Nat := 1578445693688932147612883

theorem tailTrace_3074012 : CollatzResearch.WordTrace tailWord_3074012 prefixEnd_3074012 1578445693688932147612883 := by
  unfold tailWord_3074012
  simp only [CollatzResearch.WordTrace]
  refine ⟨56059214269693499148684145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74745619026257998864912193 56059214269693499148684145)
  ·
    refine ⟨42044410702270124361513109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56059214269693499148684145 42044410702270124361513109)
    ·
      refine ⟨1970831751668912079445927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42044410702270124361513109 1970831751668912079445927)
      ·
        refine ⟨2956247627503368119168891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1970831751668912079445927 2956247627503368119168891)
        ·
          refine ⟨4434371441255052178753337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956247627503368119168891 4434371441255052178753337)
          ·
            refine ⟨3325778580941289134065003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4434371441255052178753337 3325778580941289134065003)
            ·
              refine ⟨4988667871411933701097505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3325778580941289134065003 4988667871411933701097505)
              ·
                refine ⟨3741500903558950275823129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4988667871411933701097505 3741500903558950275823129)
                ·
                  refine ⟨2806125677669212706867347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3741500903558950275823129 2806125677669212706867347)
                  ·
                    refine ⟨4209188516503819060301021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2806125677669212706867347 4209188516503819060301021)
                    ·
                      refine ⟨1578445693688932147612883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4209188516503819060301021 1578445693688932147612883)
                      ·
                        rfl

theorem cell23_3074012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3074012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074012 prefixEnd_3074012 := by exact prefixLift 3074012
  have htrace : WordTrace (prefixWord ++ tailWord_3074012) baseStart_3074012 baseEnd_3074012 := by
    simpa [prefixWord, tailWord_3074012, baseEnd_3074012] using wordTrace_append hprefix tailTrace_3074012
  have hstable : (prefixWord ++ tailWord_3074012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074012).length < 2 ^ (prefixWord ++ tailWord_3074012).sum := by decide
  have hdescent : baseEnd_3074012 < baseStart_3074012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074017 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_3074017 : Nat := 118140960795 + 3074017 * 2 ^ 59
def prefixEnd_3074017 : Nat := 4983230072969 + 3 ^ 40 * 3074017 * 2
def baseEnd_3074017 : Nat := 1578448261092204628050359

theorem tailTrace_3074017 : CollatzResearch.WordTrace tailWord_3074017 prefixEnd_3074017 1578448261092204628050359 := by
  unfold tailWord_3074017
  simp only [CollatzResearch.WordTrace]
  refine ⟨112118610904368884151300305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74745740602912589434200203 112118610904368884151300305)
  ·
    refine ⟨84088958178276663113475229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112118610904368884151300305 84088958178276663113475229)
    ·
      refine ⟨31533359316853748667553211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84088958178276663113475229 31533359316853748667553211)
      ·
        refine ⟨47300038975280623001329817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31533359316853748667553211 47300038975280623001329817)
        ·
          refine ⟨35475029231460467250997363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47300038975280623001329817 35475029231460467250997363)
          ·
            refine ⟨53212543847190700876496045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35475029231460467250997363 53212543847190700876496045)
            ·
              refine ⟨19954703942696512828686017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53212543847190700876496045 19954703942696512828686017)
              ·
                refine ⟨14966027957022384621514513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19954703942696512828686017 14966027957022384621514513)
                ·
                  refine ⟨11224520967766788466135885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14966027957022384621514513 11224520967766788466135885)
                  ·
                    refine ⟨4209195362912545674800957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11224520967766788466135885 4209195362912545674800957)
                    ·
                      refine ⟨1578448261092204628050359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4209195362912545674800957 1578448261092204628050359)
                      ·
                        rfl

theorem cell23_3074017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_3074017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074017 prefixEnd_3074017 := by exact prefixLift 3074017
  have htrace : WordTrace (prefixWord ++ tailWord_3074017) baseStart_3074017 baseEnd_3074017 := by
    simpa [prefixWord, tailWord_3074017, baseEnd_3074017] using wordTrace_append hprefix tailTrace_3074017
  have hstable : (prefixWord ++ tailWord_3074017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074017).length < 2 ^ (prefixWord ++ tailWord_3074017).sum := by decide
  have hdescent : baseEnd_3074017 < baseStart_3074017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074027 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 1, 7, 2]
def baseStart_3074027 : Nat := 118140960795 + 3074027 * 2 ^ 59
def prefixEnd_3074027 : Nat := 4983230072969 + 3 ^ 40 * 3074027 * 2
def baseEnd_3074027 : Nat := 1578453395898749588925313

theorem tailTrace_3074027 : CollatzResearch.WordTrace tailWord_3074027 prefixEnd_3074027 1578453395898749588925313 := by
  unfold tailWord_3074027
  simp only [CollatzResearch.WordTrace]
  refine ⟨112118975634332655859164335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74745983756221770572776223 112118975634332655859164335)
  ·
    refine ⟨168178463451498983788746503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112118975634332655859164335 168178463451498983788746503)
    ·
      refine ⟨252267695177248475683119755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168178463451498983788746503 252267695177248475683119755)
      ·
        refine ⟨378401542765872713524679633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252267695177248475683119755 378401542765872713524679633)
        ·
          refine ⟨283801157074404535143509725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378401542765872713524679633 283801157074404535143509725)
          ·
            refine ⟨106425433902901700678816147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283801157074404535143509725 106425433902901700678816147)
            ·
              refine ⟨159638150854352551018224221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106425433902901700678816147 159638150854352551018224221)
              ·
                refine ⟨59864306570382206631834083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159638150854352551018224221 59864306570382206631834083)
                ·
                  refine ⟨89796459855573309947751125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59864306570382206631834083 89796459855573309947751125)
                  ·
                    refine ⟨2104604527864999451900417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 89796459855573309947751125 2104604527864999451900417)
                    ·
                      refine ⟨1578453395898749588925313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104604527864999451900417 1578453395898749588925313)
                      ·
                        rfl

theorem cell23_3074027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 7, 2].length) (baseStart_3074027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074027 prefixEnd_3074027 := by exact prefixLift 3074027
  have htrace : WordTrace (prefixWord ++ tailWord_3074027) baseStart_3074027 baseEnd_3074027 := by
    simpa [prefixWord, tailWord_3074027, baseEnd_3074027] using wordTrace_append hprefix tailTrace_3074027
  have hstable : (prefixWord ++ tailWord_3074027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074027).length < 2 ^ (prefixWord ++ tailWord_3074027).sum := by decide
  have hdescent : baseEnd_3074027 < baseStart_3074027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074058 : List Nat := [3, 1, 2, 2, 5, 1, 1, 3, 5]
def baseStart_3074058 : Nat := 118140960795 + 3074058 * 2 ^ 59
def prefixEnd_3074058 : Nat := 4983230072969 + 3 ^ 40 * 3074058 * 2
def baseEnd_3074058 : Nat := 175385479311004329737519

theorem tailTrace_3074058 : CollatzResearch.WordTrace tailWord_3074058 prefixEnd_3074058 175385479311004329737519 := by
  unfold tailWord_3074058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28030026574305087038385707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74746737531480232102361885 28030026574305087038385707)
  ·
    refine ⟨42045039861457630557578561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28030026574305087038385707 42045039861457630557578561)
    ·
      refine ⟨31533779896093222918183921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42045039861457630557578561 31533779896093222918183921)
      ·
        refine ⟨23650334922069917188637941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31533779896093222918183921 23650334922069917188637941)
        ·
          refine ⟨2217218898944054736434807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23650334922069917188637941 2217218898944054736434807)
          ·
            refine ⟨3325828348416082104652211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217218898944054736434807 3325828348416082104652211)
            ·
              refine ⟨4988742522624123156978317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3325828348416082104652211 4988742522624123156978317)
              ·
                refine ⟨1870778445984046183866869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4988742522624123156978317 1870778445984046183866869)
                ·
                  refine ⟨175385479311004329737519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1870778445984046183866869 175385479311004329737519)
                  ·
                    rfl

theorem cell23_3074058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_3074058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074058 prefixEnd_3074058 := by exact prefixLift 3074058
  have htrace : WordTrace (prefixWord ++ tailWord_3074058) baseStart_3074058 baseEnd_3074058 := by
    simpa [prefixWord, tailWord_3074058, baseEnd_3074058] using wordTrace_append hprefix tailTrace_3074058
  have hstable : (prefixWord ++ tailWord_3074058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074058).length < 2 ^ (prefixWord ++ tailWord_3074058).sum := by decide
  have hdescent : baseEnd_3074058 < baseStart_3074058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074067 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 5, 4]
def baseStart_3074067 : Nat := 118140960795 + 3074067 * 2 ^ 59
def prefixEnd_3074067 : Nat := 4983230072969 + 3 ^ 40 * 3074067 * 2
def baseEnd_3074067 : Nat := 526157978374976477475043

theorem tailTrace_3074067 : CollatzResearch.WordTrace tailWord_3074067 prefixEnd_3074067 526157978374976477475043 := by
  unfold tailWord_3074067
  simp only [CollatzResearch.WordTrace]
  refine ⟨112120434554187742690620455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74746956369458495127080303 112120434554187742690620455)
  ·
    refine ⟨168180651831281614035930683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112120434554187742690620455 168180651831281614035930683)
    ·
      refine ⟨252270977746922421053896025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168180651831281614035930683 252270977746922421053896025)
      ·
        refine ⟨189203233310191815790422019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252270977746922421053896025 189203233310191815790422019)
        ·
          refine ⟨283804849965287723685633029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189203233310191815790422019 283804849965287723685633029)
          ·
            refine ⟨53213409368491448191056193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283804849965287723685633029 53213409368491448191056193)
            ·
              refine ⟨39910057026368586143292145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53213409368491448191056193 39910057026368586143292145)
              ·
                refine ⟨29932542769776439607469109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39910057026368586143292145 29932542769776439607469109)
                ·
                  refine ⟨2806175884666541213200229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29932542769776439607469109 2806175884666541213200229)
                  ·
                    refine ⟨526157978374976477475043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2806175884666541213200229 526157978374976477475043)
                    ·
                      rfl

theorem cell23_3074067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 4].length) (baseStart_3074067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074067 prefixEnd_3074067 := by exact prefixLift 3074067
  have htrace : WordTrace (prefixWord ++ tailWord_3074067) baseStart_3074067 baseEnd_3074067 := by
    simpa [prefixWord, tailWord_3074067, baseEnd_3074067] using wordTrace_append hprefix tailTrace_3074067
  have hstable : (prefixWord ++ tailWord_3074067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074067).length < 2 ^ (prefixWord ++ tailWord_3074067).sum := by decide
  have hdescent : baseEnd_3074067 < baseStart_3074067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074074 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_3074074 : Nat := 118140960795 + 3074074 * 2 ^ 59
def prefixEnd_3074074 : Nat := 4983230072969 + 3 ^ 40 * 3074074 * 2
def baseEnd_3074074 : Nat := 1578477529489510905037597

theorem tailTrace_3074074 : CollatzResearch.WordTrace tailWord_3074074 prefixEnd_3074074 1578477529489510905037597 := by
  unfold tailWord_3074074
  simp only [CollatzResearch.WordTrace]
  refine ⟨28030172466290595721531319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74747126576774921924083517 28030172466290595721531319)
  ·
    refine ⟨42045258699435893582296979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28030172466290595721531319 42045258699435893582296979)
    ·
      refine ⟨63067888049153840373445469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42045258699435893582296979 63067888049153840373445469)
      ·
        refine ⟨23650458018432690140042051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63067888049153840373445469 23650458018432690140042051)
        ·
          refine ⟨35475687027649035210063077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23650458018432690140042051 35475687027649035210063077)
          ·
            refine ⟨6651691317684194101886827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35475687027649035210063077 6651691317684194101886827)
            ·
              refine ⟨9977536976526291152830241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6651691317684194101886827 9977536976526291152830241)
              ·
                refine ⟨7483152732394718364622681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9977536976526291152830241 7483152732394718364622681)
                ·
                  refine ⟨5612364549296038773467011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7483152732394718364622681 5612364549296038773467011)
                  ·
                    refine ⟨8418546823944058160200517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5612364549296038773467011 8418546823944058160200517)
                    ·
                      refine ⟨1578477529489510905037597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8418546823944058160200517 1578477529489510905037597)
                      ·
                        rfl

theorem cell23_3074074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_3074074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074074 prefixEnd_3074074 := by exact prefixLift 3074074
  have htrace : WordTrace (prefixWord ++ tailWord_3074074) baseStart_3074074 baseEnd_3074074 := by
    simpa [prefixWord, tailWord_3074074, baseEnd_3074074] using wordTrace_append hprefix tailTrace_3074074
  have hstable : (prefixWord ++ tailWord_3074074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074074).length < 2 ^ (prefixWord ++ tailWord_3074074).sum := by decide
  have hdescent : baseEnd_3074074 < baseStart_3074074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074181 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 4]
def baseStart_3074181 : Nat := 118140960795 + 3074181 * 2 ^ 59
def prefixEnd_3074181 : Nat := 4983230072969 + 3 ^ 40 * 3074181 * 2
def baseEnd_3074181 : Nat := 1578532471919541986399605

theorem tailTrace_3074181 : CollatzResearch.WordTrace tailWord_3074181 prefixEnd_3074181 1578532471919541986399605 := by
  unfold tailWord_3074181
  simp only [CollatzResearch.WordTrace]
  refine ⟨112124592475774740160270397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74749728317183160106846931 112124592475774740160270397)
  ·
    refine ⟨42046722178415527560101399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112124592475774740160270397 42046722178415527560101399)
    ·
      refine ⟨63070083267623291340152099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42046722178415527560101399 63070083267623291340152099)
      ·
        refine ⟨94605124901434937010228149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63070083267623291340152099 94605124901434937010228149)
        ·
          refine ⟨8869230459509525344708889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94605124901434937010228149 8869230459509525344708889)
          ·
            refine ⟨6651922844632144008531667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8869230459509525344708889 6651922844632144008531667)
            ·
              refine ⟨9977884266948216012797501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6651922844632144008531667 9977884266948216012797501)
              ·
                refine ⟨3741706600105581004799063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9977884266948216012797501 3741706600105581004799063)
                ·
                  refine ⟨5612559900158371507198595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3741706600105581004799063 5612559900158371507198595)
                  ·
                    refine ⟨8418839850237557260797893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5612559900158371507198595 8418839850237557260797893)
                    ·
                      refine ⟨1578532471919541986399605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8418839850237557260797893 1578532471919541986399605)
                      ·
                        rfl

theorem cell23_3074181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_3074181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074181 prefixEnd_3074181 := by exact prefixLift 3074181
  have htrace : WordTrace (prefixWord ++ tailWord_3074181) baseStart_3074181 baseEnd_3074181 := by
    simpa [prefixWord, tailWord_3074181, baseEnd_3074181] using wordTrace_append hprefix tailTrace_3074181
  have hstable : (prefixWord ++ tailWord_3074181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074181).length < 2 ^ (prefixWord ++ tailWord_3074181).sum := by decide
  have hdescent : baseEnd_3074181 < baseStart_3074181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074194 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3074194 : Nat := 118140960795 + 3074194 * 2 ^ 59
def prefixEnd_3074194 : Nat := 4983230072969 + 3 ^ 40 * 3074194 * 2
def baseEnd_3074194 : Nat := 1578539147168050435537045

theorem tailTrace_3074194 : CollatzResearch.WordTrace tailWord_3074194 prefixEnd_3074194 1578539147168050435537045 := by
  unfold tailWord_3074194
  simp only [CollatzResearch.WordTrace]
  refine ⟨28031266656181910845123409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 74750044416485095586995757 28031266656181910845123409)
  ·
    refine ⟨21023449992136433133842557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28031266656181910845123409 21023449992136433133842557)
    ·
      refine ⟨7883793747051162425190959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21023449992136433133842557 7883793747051162425190959)
      ·
        refine ⟨11825690620576743637786439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7883793747051162425190959 11825690620576743637786439)
        ·
          refine ⟨17738535930865115456679659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11825690620576743637786439 17738535930865115456679659)
          ·
            refine ⟨26607803896297673185019489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17738535930865115456679659 26607803896297673185019489)
            ·
              refine ⟨19955852922223254888764617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26607803896297673185019489 19955852922223254888764617)
              ·
                refine ⟨14966889691667441166573463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19955852922223254888764617 14966889691667441166573463)
                ·
                  refine ⟨22450334537501161749860195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14966889691667441166573463 22450334537501161749860195)
                  ·
                    refine ⟨33675501806251742624790293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22450334537501161749860195 33675501806251742624790293)
                    ·
                      refine ⟨1578539147168050435537045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 33675501806251742624790293 1578539147168050435537045)
                      ·
                        rfl

theorem cell23_3074194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3074194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074194 prefixEnd_3074194 := by exact prefixLift 3074194
  have htrace : WordTrace (prefixWord ++ tailWord_3074194) baseStart_3074194 baseEnd_3074194 := by
    simpa [prefixWord, tailWord_3074194, baseEnd_3074194] using wordTrace_append hprefix tailTrace_3074194
  have hstable : (prefixWord ++ tailWord_3074194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074194).length < 2 ^ (prefixWord ++ tailWord_3074194).sum := by decide
  have hdescent : baseEnd_3074194 < baseStart_3074194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074208 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 2, 4]
def baseStart_3074208 : Nat := 118140960795 + 3074208 * 2 ^ 59
def prefixEnd_3074208 : Nat := 4983230072969 + 3 ^ 40 * 3074208 * 2
def baseEnd_3074208 : Nat := 526182111965737793587327

theorem tailTrace_3074208 : CollatzResearch.WordTrace tailWord_3074208 prefixEnd_3074208 526182111965737793587327 := by
  unfold tailWord_3074208
  simp only [CollatzResearch.WordTrace]
  refine ⟨56062788623338461885751639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 74750384831117949181002185 56062788623338461885751639)
  ·
    refine ⟨84094182935007692828627459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56062788623338461885751639 84094182935007692828627459)
    ·
      refine ⟨126141274402511539242941189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84094182935007692828627459 126141274402511539242941189)
      ·
        refine ⟨23651488950470913608051473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126141274402511539242941189 23651488950470913608051473)
        ·
          refine ⟨17738616712853185206038605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23651488950470913608051473 17738616712853185206038605)
          ·
            refine ⟨6651981267319944452264477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17738616712853185206038605 6651981267319944452264477)
            ·
              refine ⟨2494492975244979169599179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6651981267319944452264477 2494492975244979169599179)
              ·
                refine ⟨3741739462867468754398769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494492975244979169599179 3741739462867468754398769)
                ·
                  refine ⟨2806304597150601565799077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3741739462867468754398769 2806304597150601565799077)
                  ·
                    refine ⟨526182111965737793587327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2806304597150601565799077 526182111965737793587327)
                    ·
                      rfl

theorem cell23_3074208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 2, 4].length) (baseStart_3074208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074208 prefixEnd_3074208 := by exact prefixLift 3074208
  have htrace : WordTrace (prefixWord ++ tailWord_3074208) baseStart_3074208 baseEnd_3074208 := by
    simpa [prefixWord, tailWord_3074208, baseEnd_3074208] using wordTrace_append hprefix tailTrace_3074208
  have hstable : (prefixWord ++ tailWord_3074208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074208).length < 2 ^ (prefixWord ++ tailWord_3074208).sum := by decide
  have hdescent : baseEnd_3074208 < baseStart_3074208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074221 : List Nat := [1, 5, 2, 1, 2, 1, 4, 7]
def baseStart_3074221 : Nat := 118140960795 + 3074221 * 2 ^ 59
def prefixEnd_3074221 : Nat := 4983230072969 + 3 ^ 40 * 3074221 * 2
def baseEnd_3074221 : Nat := 58464926338730438144423

theorem tailTrace_3074221 : CollatzResearch.WordTrace tailWord_3074221 prefixEnd_3074221 58464926338730438144423 := by
  unfold tailWord_3074221
  simp only [CollatzResearch.WordTrace]
  refine ⟨112126051395629826991726517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74750700930419884661151011 112126051395629826991726517)
  ·
    refine ⟨10511817318340296280474361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112126051395629826991726517 10511817318340296280474361)
    ·
      refine ⟨7883862988755222210355771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10511817318340296280474361 7883862988755222210355771)
      ·
        refine ⟨11825794483132833315533657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7883862988755222210355771 11825794483132833315533657)
        ·
          refine ⟨8869345862349624986650243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11825794483132833315533657 8869345862349624986650243)
          ·
            refine ⟨13304018793524437479975365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8869345862349624986650243 13304018793524437479975365)
            ·
              refine ⟨2494503523785832027495381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13304018793524437479975365 2494503523785832027495381)
              ·
                refine ⟨58464926338730438144423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2494503523785832027495381 58464926338730438144423)
                ·
                  rfl

theorem cell23_3074221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 7].length) (baseStart_3074221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074221 prefixEnd_3074221 := by exact prefixLift 3074221
  have htrace : WordTrace (prefixWord ++ tailWord_3074221) baseStart_3074221 baseEnd_3074221 := by
    simpa [prefixWord, tailWord_3074221, baseEnd_3074221] using wordTrace_append hprefix tailTrace_3074221
  have hstable : (prefixWord ++ tailWord_3074221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074221).length < 2 ^ (prefixWord ++ tailWord_3074221).sum := by decide
  have hdescent : baseEnd_3074221 < baseStart_3074221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074231 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 4, 1, 3]
def baseStart_3074231 : Nat := 118140960795 + 3074231 * 2 ^ 59
def prefixEnd_3074231 : Nat := 4983230072969 + 3 ^ 40 * 3074231 * 2
def baseEnd_3074231 : Nat := 1578558145952266790774375

theorem tailTrace_3074231 : CollatzResearch.WordTrace tailWord_3074231 prefixEnd_3074231 1578558145952266790774375 := by
  unfold tailWord_3074231
  simp only [CollatzResearch.WordTrace]
  refine ⟨112126416125593598699590547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74750944083729065799727031 112126416125593598699590547)
  ·
    refine ⟨168189624188390398049385821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112126416125593598699590547 168189624188390398049385821)
    ·
      refine ⟨63071109070646399268519683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168189624188390398049385821 63071109070646399268519683)
      ·
        refine ⟨94606663605969598902779525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63071109070646399268519683 94606663605969598902779525)
        ·
          refine ⟨17738749426119299794271161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94606663605969598902779525 17738749426119299794271161)
          ·
            refine ⟨13304062069589474845703371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17738749426119299794271161 13304062069589474845703371)
            ·
              refine ⟨19956093104384212268555057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13304062069589474845703371 19956093104384212268555057)
              ·
                refine ⟨14967069828288159201416293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19956093104384212268555057 14967069828288159201416293)
                ·
                  refine ⟨2806325592804029850265555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14967069828288159201416293 2806325592804029850265555)
                  ·
                    refine ⟨4209488389206044775398333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2806325592804029850265555 4209488389206044775398333)
                    ·
                      refine ⟨1578558145952266790774375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4209488389206044775398333 1578558145952266790774375)
                      ·
                        rfl

theorem cell23_3074231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_3074231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074231 prefixEnd_3074231 := by exact prefixLift 3074231
  have htrace : WordTrace (prefixWord ++ tailWord_3074231) baseStart_3074231 baseEnd_3074231 := by
    simpa [prefixWord, tailWord_3074231, baseEnd_3074231] using wordTrace_append hprefix tailTrace_3074231
  have hstable : (prefixWord ++ tailWord_3074231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074231).length < 2 ^ (prefixWord ++ tailWord_3074231).sum := by decide
  have hdescent : baseEnd_3074231 < baseStart_3074231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074271 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 1, 4, 2]
def baseStart_3074271 : Nat := 118140960795 + 3074271 * 2 ^ 59
def prefixEnd_3074271 : Nat := 4983230072969 + 3 ^ 40 * 3074271 * 2
def baseEnd_3074271 : Nat := 1578578685178446634274191

theorem tailTrace_3074271 : CollatzResearch.WordTrace tailWord_3074271 prefixEnd_3074271 1578578685178446634274191 := by
  unfold tailWord_3074271
  simp only [CollatzResearch.WordTrace]
  refine ⟨112127875045448685531046667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74751916696965790354031111 112127875045448685531046667)
  ·
    refine ⟨168191812568173028296570001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112127875045448685531046667 168191812568173028296570001)
    ·
      refine ⟨126143859426129771222427501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168191812568173028296570001 126143859426129771222427501)
      ·
        refine ⟨47303947284798664208410313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126143859426129771222427501 47303947284798664208410313)
        ·
          refine ⟨35477960463598998156307735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47303947284798664208410313 35477960463598998156307735)
          ·
            refine ⟨53216940695398497234461603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35477960463598998156307735 53216940695398497234461603)
            ·
              refine ⟨79825411043097745851692405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53216940695398497234461603 79825411043097745851692405)
              ·
                refine ⟨7483632285290413673596163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79825411043097745851692405 7483632285290413673596163)
                ·
                  refine ⟨11225448427935620510394245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7483632285290413673596163 11225448427935620510394245)
                  ·
                    refine ⟨2104771580237928845698921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11225448427935620510394245 2104771580237928845698921)
                    ·
                      refine ⟨1578578685178446634274191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104771580237928845698921 1578578685178446634274191)
                      ·
                        rfl

theorem cell23_3074271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_3074271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074271 prefixEnd_3074271 := by exact prefixLift 3074271
  have htrace : WordTrace (prefixWord ++ tailWord_3074271) baseStart_3074271 baseEnd_3074271 := by
    simpa [prefixWord, tailWord_3074271, baseEnd_3074271] using wordTrace_append hprefix tailTrace_3074271
  have hstable : (prefixWord ++ tailWord_3074271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074271).length < 2 ^ (prefixWord ++ tailWord_3074271).sum := by decide
  have hdescent : baseEnd_3074271 < baseStart_3074271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074275 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3074275 : Nat := 118140960795 + 3074275 * 2 ^ 59
def prefixEnd_3074275 : Nat := 4983230072969 + 3 ^ 40 * 3074275 * 2
def baseEnd_3074275 : Nat := 1578580739101064618624173

theorem tailTrace_3074275 : CollatzResearch.WordTrace tailWord_3074275 prefixEnd_3074275 1578580739101064618624173 := by
  unfold tailWord_3074275
  simp only [CollatzResearch.WordTrace]
  refine ⟨112128020937434194214192279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74752013958289462809461519 112128020937434194214192279)
  ·
    refine ⟨168192031406151291321288419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112128020937434194214192279 168192031406151291321288419)
    ·
      refine ⟨252288047109226936981932629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168192031406151291321288419 252288047109226936981932629)
      ·
        refine ⟨2956500552061253167757023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 252288047109226936981932629 2956500552061253167757023)
        ·
          refine ⟨4434750828091879751635535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956500552061253167757023 4434750828091879751635535)
          ·
            refine ⟨6652126242137819627453303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434750828091879751635535 6652126242137819627453303)
            ·
              refine ⟨9978189363206729441179955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652126242137819627453303 9978189363206729441179955)
              ·
                refine ⟨14967284044810094161769933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9978189363206729441179955 14967284044810094161769933)
                ·
                  refine ⟨5612731516803785310663725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14967284044810094161769933 5612731516803785310663725)
                  ·
                    refine ⟨2104774318801419491498897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5612731516803785310663725 2104774318801419491498897)
                    ·
                      refine ⟨1578580739101064618624173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104774318801419491498897 1578580739101064618624173)
                      ·
                        rfl

theorem cell23_3074275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3074275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074275 prefixEnd_3074275 := by exact prefixLift 3074275
  have htrace : WordTrace (prefixWord ++ tailWord_3074275) baseStart_3074275 baseEnd_3074275 := by
    simpa [prefixWord, tailWord_3074275, baseEnd_3074275] using wordTrace_append hprefix tailTrace_3074275
  have hstable : (prefixWord ++ tailWord_3074275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074275).length < 2 ^ (prefixWord ++ tailWord_3074275).sum := by decide
  have hdescent : baseEnd_3074275 < baseStart_3074275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074305 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_3074305 : Nat := 118140960795 + 3074305 * 2 ^ 59
def prefixEnd_3074305 : Nat := 4983230072969 + 3 ^ 40 * 3074305 * 2
def baseEnd_3074305 : Nat := 1578596143520699501249035

theorem tailTrace_3074305 : CollatzResearch.WordTrace tailWord_3074305 prefixEnd_3074305 1578596143520699501249035 := by
  unfold tailWord_3074305
  simp only [CollatzResearch.WordTrace]
  refine ⟨112129115127325509337784369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74752743418217006225189579 112129115127325509337784369)
  ·
    refine ⟨84096836345494132003338277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112129115127325509337784369 84096836345494132003338277)
    ·
      refine ⟨15768156814780149750625927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84096836345494132003338277 15768156814780149750625927)
      ·
        refine ⟨23652235222170224625938891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15768156814780149750625927 23652235222170224625938891)
        ·
          refine ⟨35478352833255336938908337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23652235222170224625938891 35478352833255336938908337)
          ·
            refine ⟨26608764624941502704181253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35478352833255336938908337 26608764624941502704181253)
            ·
              refine ⟨4989143367176531757033985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26608764624941502704181253 4989143367176531757033985)
              ·
                refine ⟨3741857525382398817775489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4989143367176531757033985 3741857525382398817775489)
                ·
                  refine ⟨2806393144036799113331617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3741857525382398817775489 2806393144036799113331617)
                  ·
                    refine ⟨2104794858027599334998713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2806393144036799113331617 2104794858027599334998713)
                    ·
                      refine ⟨1578596143520699501249035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104794858027599334998713 1578596143520699501249035)
                      ·
                        rfl

theorem cell23_3074305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_3074305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074305 prefixEnd_3074305 := by exact prefixLift 3074305
  have htrace : WordTrace (prefixWord ++ tailWord_3074305) baseStart_3074305 baseEnd_3074305 := by
    simpa [prefixWord, tailWord_3074305, baseEnd_3074305] using wordTrace_append hprefix tailTrace_3074305
  have hstable : (prefixWord ++ tailWord_3074305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074305).length < 2 ^ (prefixWord ++ tailWord_3074305).sum := by decide
  have hdescent : baseEnd_3074305 < baseStart_3074305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074321 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 3]
def baseStart_3074321 : Nat := 118140960795 + 3074321 * 2 ^ 59
def prefixEnd_3074321 : Nat := 4983230072969 + 3 ^ 40 * 3074321 * 2
def baseEnd_3074321 : Nat := 1578604359211171438648961

theorem tailTrace_3074321 : CollatzResearch.WordTrace tailWord_3074321 prefixEnd_3074321 1578604359211171438648961 := by
  unfold tailWord_3074321
  simp only [CollatzResearch.WordTrace]
  refine ⟨112129698695267544070366817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74753132463511696046911211 112129698695267544070366817)
  ·
    refine ⟨84097274021450658052775113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112129698695267544070366817 84097274021450658052775113)
    ·
      refine ⟨63072955516087993539581335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84097274021450658052775113 63072955516087993539581335)
      ·
        refine ⟨94609433274131990309372003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63072955516087993539581335 94609433274131990309372003)
        ·
          refine ⟨141914149911197985464058005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94609433274131990309372003 141914149911197985464058005)
          ·
            refine ⟨6652225777087405568627719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141914149911197985464058005 6652225777087405568627719)
            ·
              refine ⟨9978338665631108352941579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652225777087405568627719 9978338665631108352941579)
              ·
                refine ⟨14967507998446662529412369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9978338665631108352941579 14967507998446662529412369)
                ·
                  refine ⟨11225630998834996897059277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14967507998446662529412369 11225630998834996897059277)
                  ·
                    refine ⟨4209611624563123836397229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11225630998834996897059277 4209611624563123836397229)
                    ·
                      refine ⟨1578604359211171438648961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4209611624563123836397229 1578604359211171438648961)
                      ·
                        rfl

theorem cell23_3074321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_3074321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074321 prefixEnd_3074321 := by exact prefixLift 3074321
  have htrace : WordTrace (prefixWord ++ tailWord_3074321) baseStart_3074321 baseEnd_3074321 := by
    simpa [prefixWord, tailWord_3074321, baseEnd_3074321] using wordTrace_append hprefix tailTrace_3074321
  have hstable : (prefixWord ++ tailWord_3074321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074321).length < 2 ^ (prefixWord ++ tailWord_3074321).sum := by decide
  have hdescent : baseEnd_3074321 < baseStart_3074321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074341 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 1, 7]
def baseStart_3074341 : Nat := 118140960795 + 3074341 * 2 ^ 59
def prefixEnd_3074341 : Nat := 4983230072969 + 3 ^ 40 * 3074341 * 2
def baseEnd_3074341 : Nat := 526204876274753786799623

theorem tailTrace_3074341 : CollatzResearch.WordTrace tailWord_3074341 prefixEnd_3074341 526204876274753786799623 := by
  unfold tailWord_3074341
  simp only [CollatzResearch.WordTrace]
  refine ⟨112130428155195087486094877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74753618770130058324063251 112130428155195087486094877)
  ·
    refine ⟨42048910558198157807285579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112130428155195087486094877 42048910558198157807285579)
    ·
      refine ⟨63073365837297236710928369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42048910558198157807285579 63073365837297236710928369)
      ·
        refine ⟨47305024377972927533196277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63073365837297236710928369 47305024377972927533196277)
        ·
          refine ⟨4434846035434961956237151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47305024377972927533196277 4434846035434961956237151)
          ·
            refine ⟨6652269053152442934355727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434846035434961956237151 6652269053152442934355727)
            ·
              refine ⟨9978403579728664401533591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652269053152442934355727 9978403579728664401533591)
              ·
                refine ⟨14967605369592996602300387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9978403579728664401533591 14967605369592996602300387)
                ·
                  refine ⟨22451408054389494903450581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14967605369592996602300387 22451408054389494903450581)
                  ·
                    refine ⟨526204876274753786799623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22451408054389494903450581 526204876274753786799623)
                    ·
                      rfl

theorem cell23_3074341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_3074341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074341 prefixEnd_3074341 := by exact prefixLift 3074341
  have htrace : WordTrace (prefixWord ++ tailWord_3074341) baseStart_3074341 baseEnd_3074341 := by
    simpa [prefixWord, tailWord_3074341, baseEnd_3074341] using wordTrace_append hprefix tailTrace_3074341
  have hstable : (prefixWord ++ tailWord_3074341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074341).length < 2 ^ (prefixWord ++ tailWord_3074341).sum := by decide
  have hdescent : baseEnd_3074341 < baseStart_3074341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074343 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_3074343 : Nat := 118140960795 + 3074343 * 2 ^ 59
def prefixEnd_3074343 : Nat := 4983230072969 + 3 ^ 40 * 3074343 * 2
def baseEnd_3074343 : Nat := 1578615655785570352573861

theorem tailTrace_3074343 : CollatzResearch.WordTrace tailWord_3074343 prefixEnd_3074343 1578615655785570352573861 := by
  unfold tailWord_3074343
  simp only [CollatzResearch.WordTrace]
  refine ⟨112130501101187841827667683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74753667400791894551778455 112130501101187841827667683)
  ·
    refine ⟨168195751651781762741501525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112130501101187841827667683 168195751651781762741501525)
    ·
      refine ⟨1971043964669317532126971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 168195751651781762741501525 1971043964669317532126971)
      ·
        refine ⟨2956565947003976298190457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1971043964669317532126971 2956565947003976298190457)
        ·
          refine ⟨2217424460252982223642843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2956565947003976298190457 2217424460252982223642843)
          ·
            refine ⟨3326136690379473335464265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217424460252982223642843 3326136690379473335464265)
            ·
              refine ⟨2494602517784605001598199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3326136690379473335464265 2494602517784605001598199)
              ·
                refine ⟨3741903776676907502397299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494602517784605001598199 3741903776676907502397299)
                ·
                  refine ⟨5612855665015361253595949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3741903776676907502397299 5612855665015361253595949)
                  ·
                    refine ⟨2104820874380760470098481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5612855665015361253595949 2104820874380760470098481)
                    ·
                      refine ⟨1578615655785570352573861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2104820874380760470098481 1578615655785570352573861)
                      ·
                        rfl

theorem cell23_3074343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_3074343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074343 prefixEnd_3074343 := by exact prefixLift 3074343
  have htrace : WordTrace (prefixWord ++ tailWord_3074343) baseStart_3074343 baseEnd_3074343 := by
    simpa [prefixWord, tailWord_3074343, baseEnd_3074343] using wordTrace_append hprefix tailTrace_3074343
  have hstable : (prefixWord ++ tailWord_3074343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074343).length < 2 ^ (prefixWord ++ tailWord_3074343).sum := by decide
  have hdescent : baseEnd_3074343 < baseStart_3074343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3074371 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 3, 4]
def baseStart_3074371 : Nat := 118140960795 + 3074371 * 2 ^ 59
def prefixEnd_3074371 : Nat := 4983230072969 + 3 ^ 40 * 3074371 * 2
def baseEnd_3074371 : Nat := 526210011081298747674577

theorem tailTrace_3074371 : CollatzResearch.WordTrace tailWord_3074371 prefixEnd_3074371 526210011081298747674577 := by
  unfold tailWord_3074371
  simp only [CollatzResearch.WordTrace]
  refine ⟨112131522345086402609686967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 74754348230057601739791311 112131522345086402609686967)
  ·
    refine ⟨168197283517629603914530451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112131522345086402609686967 168197283517629603914530451)
    ·
      refine ⟨252295925276444405871795677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168197283517629603914530451 252295925276444405871795677)
      ·
        refine ⟨94610971978666652201923379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252295925276444405871795677 94610971978666652201923379)
        ·
          refine ⟨141916457967999978302885069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94610971978666652201923379 141916457967999978302885069)
          ·
            refine ⟨53218671737999991863581901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141916457967999978302885069 53218671737999991863581901)
            ·
              refine ⟨19957001901749996948843213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53218671737999991863581901 19957001901749996948843213)
              ·
                refine ⟨7483875713156248855816205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19957001901749996948843213 7483875713156248855816205)
                ·
                  refine ⟨2806453392433593320931077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7483875713156248855816205 2806453392433593320931077)
                  ·
                    refine ⟨526210011081298747674577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2806453392433593320931077 526210011081298747674577)
                    ·
                      rfl

theorem cell23_3074371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 4].length) (baseStart_3074371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3074371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3074371 prefixEnd_3074371 := by exact prefixLift 3074371
  have htrace : WordTrace (prefixWord ++ tailWord_3074371) baseStart_3074371 baseEnd_3074371 := by
    simpa [prefixWord, tailWord_3074371, baseEnd_3074371] using wordTrace_append hprefix tailTrace_3074371
  have hstable : (prefixWord ++ tailWord_3074371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3074371).length < 2 ^ (prefixWord ++ tailWord_3074371).sum := by decide
  have hdescent : baseEnd_3074371 < baseStart_3074371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3074371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
