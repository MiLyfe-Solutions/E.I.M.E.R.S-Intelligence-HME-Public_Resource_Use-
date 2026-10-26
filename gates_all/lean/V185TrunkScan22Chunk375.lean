import V185TrunkScan22Chunk374

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3343037 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_3343037 : Nat := 118140960795 + 3343037 * 2 ^ 59
def prefixEnd_3343037 : Nat := 4983230072969 + 3 ^ 40 * 3343037 * 2
def baseEnd_3343037 : Nat := 1144389884509828057375439

theorem tailTrace_3343037 : CollatzResearch.WordTrace tailWord_3343037 prefixEnd_3343037 1144389884509828057375439 := by
  unfold tailWord_3343037
  simp only [CollatzResearch.WordTrace]
  refine ⟨121930576389755369109435365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81287050926503579406290243 121930576389755369109435365)
  ·
    refine ⟨22861983073079131708019131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121930576389755369109435365 22861983073079131708019131)
    ·
      refine ⟨34292974609618697562028697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22861983073079131708019131 34292974609618697562028697)
      ·
        refine ⟨25719730957214023171521523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34292974609618697562028697 25719730957214023171521523)
        ·
          refine ⟨38579596435821034757282285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25719730957214023171521523 38579596435821034757282285)
          ·
            refine ⟨14467348663432888033980857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38579596435821034757282285 14467348663432888033980857)
            ·
              refine ⟨10850511497574666025485643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14467348663432888033980857 10850511497574666025485643)
              ·
                refine ⟨16275767246361999038228465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10850511497574666025485643 16275767246361999038228465)
                ·
                  refine ⟨12206825434771499278671349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16275767246361999038228465 12206825434771499278671349)
                  ·
                    refine ⟨1144389884509828057375439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12206825434771499278671349 1144389884509828057375439)
                    ·
                      rfl

theorem cell22_3343037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_3343037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343037 prefixEnd_3343037 := by exact prefixLift 3343037
  have htrace : WordTrace (prefixWord ++ tailWord_3343037) baseStart_3343037 baseEnd_3343037 := by
    simpa [prefixWord, tailWord_3343037, baseEnd_3343037] using wordTrace_append hprefix tailTrace_3343037
  have hstable : (prefixWord ++ tailWord_3343037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343037).length < 2 ^ (prefixWord ++ tailWord_3343037).sum := by decide
  have hdescent : baseEnd_3343037 < baseStart_3343037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343039 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 5]
def baseStart_3343039 : Nat := 118140960795 + 3343039 * 2 ^ 59
def prefixEnd_3343039 : Nat := 4983230072969 + 3 ^ 40 * 3343039 * 2
def baseEnd_3343039 : Nat := 381463523050233572941811

theorem tailTrace_3343039 : CollatzResearch.WordTrace tailWord_3343039 prefixEnd_3343039 381463523050233572941811 := by
  unfold tailWord_3343039
  simp only [CollatzResearch.WordTrace]
  refine ⟨121930649335748123451008171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81287099557165415634005447 121930649335748123451008171)
  ·
    refine ⟨182895974003622185176512257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121930649335748123451008171 182895974003622185176512257)
    ·
      refine ⟨137171980502716638882384193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182895974003622185176512257 137171980502716638882384193)
      ·
        refine ⟨102878985377037479161788145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137171980502716638882384193 102878985377037479161788145)
        ·
          refine ⟨77159239032778109371341109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102878985377037479161788145 77159239032778109371341109)
          ·
            refine ⟨7233678659322947753563229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77159239032778109371341109 7233678659322947753563229)
            ·
              refine ⟨2712629497246105407586211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7233678659322947753563229 2712629497246105407586211)
              ·
                refine ⟨4068944245869158111379317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712629497246105407586211 4068944245869158111379317)
                ·
                  refine ⟨381463523050233572941811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4068944245869158111379317 381463523050233572941811)
                  ·
                    rfl

theorem cell22_3343039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 5].length) (baseStart_3343039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343039 prefixEnd_3343039 := by exact prefixLift 3343039
  have htrace : WordTrace (prefixWord ++ tailWord_3343039) baseStart_3343039 baseEnd_3343039 := by
    simpa [prefixWord, tailWord_3343039, baseEnd_3343039] using wordTrace_append hprefix tailTrace_3343039
  have hstable : (prefixWord ++ tailWord_3343039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343039).length < 2 ^ (prefixWord ++ tailWord_3343039).sum := by decide
  have hdescent : baseEnd_3343039 < baseStart_3343039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343060 : List Nat := [2, 4, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_3343060 : Nat := 118140960795 + 3343060 * 2 ^ 59
def prefixEnd_3343060 : Nat := 4983230072969 + 3 ^ 40 * 3343060 * 2
def baseEnd_3343060 : Nat := 1144397757879863664050369

theorem tailTrace_3343060 : CollatzResearch.WordTrace tailWord_3343060 prefixEnd_3343060 1144397757879863664050369 := by
  unfold tailWord_3343060
  simp only [CollatzResearch.WordTrace]
  refine ⟨60965707634336022018761317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81287610179114696025015089 60965707634336022018761317)
  ·
    refine ⟨11431070181438004128517747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60965707634336022018761317 11431070181438004128517747)
    ·
      refine ⟨17146605272157006192776621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11431070181438004128517747 17146605272157006192776621)
      ·
        refine ⟨6429976977058877322291233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17146605272157006192776621 6429976977058877322291233)
        ·
          refine ⟨4822482732794157991718425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6429976977058877322291233 4822482732794157991718425)
          ·
            refine ⟨3616862049595618493788819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4822482732794157991718425 3616862049595618493788819)
            ·
              refine ⟨5425293074393427740683229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3616862049595618493788819 5425293074393427740683229)
              ·
                refine ⟨2034484902897535402756211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5425293074393427740683229 2034484902897535402756211)
                ·
                  refine ⟨3051727354346303104134317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034484902897535402756211 3051727354346303104134317)
                  ·
                    refine ⟨1144397757879863664050369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3051727354346303104134317 1144397757879863664050369)
                    ·
                      rfl

theorem cell22_3343060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_3343060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343060 prefixEnd_3343060 := by exact prefixLift 3343060
  have htrace : WordTrace (prefixWord ++ tailWord_3343060) baseStart_3343060 baseEnd_3343060 := by
    simpa [prefixWord, tailWord_3343060, baseEnd_3343060] using wordTrace_append hprefix tailTrace_3343060
  have hstable : (prefixWord ++ tailWord_3343060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343060).length < 2 ^ (prefixWord ++ tailWord_3343060).sum := by decide
  have hdescent : baseEnd_3343060 < baseStart_3343060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343112 : List Nat := [2, 1, 3, 2, 2, 2, 2, 8]
def baseStart_3343112 : Nat := 118140960795 + 3343112 * 2 ^ 59
def prefixEnd_3343112 : Nat := 4983230072969 + 3 ^ 40 * 3343112 * 2
def baseEnd_3343112 : Nat := 127157284282505873527801

theorem tailTrace_3343112 : CollatzResearch.WordTrace tailWord_3343112 prefixEnd_3343112 127157284282505873527801 := by
  unfold tailWord_3343112
  simp only [CollatzResearch.WordTrace]
  refine ⟨60966655932241828459207795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81288874576322437945610393 60966655932241828459207795)
  ·
    refine ⟨91449983898362742688811693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60966655932241828459207795 91449983898362742688811693)
    ·
      refine ⟨34293743961886028508304385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91449983898362742688811693 34293743961886028508304385)
      ·
        refine ⟨25720307971414521381228289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34293743961886028508304385 25720307971414521381228289)
        ·
          refine ⟨19290230978560891035921217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25720307971414521381228289 19290230978560891035921217)
          ·
            refine ⟨14467673233920668276940913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19290230978560891035921217 14467673233920668276940913)
            ·
              refine ⟨10850754925440501207705685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14467673233920668276940913 10850754925440501207705685)
              ·
                refine ⟨127157284282505873527801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10850754925440501207705685 127157284282505873527801)
                ·
                  rfl

theorem cell22_3343112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 8].length) (baseStart_3343112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343112 prefixEnd_3343112 := by exact prefixLift 3343112
  have htrace : WordTrace (prefixWord ++ tailWord_3343112) baseStart_3343112 baseEnd_3343112 := by
    simpa [prefixWord, tailWord_3343112, baseEnd_3343112] using wordTrace_append hprefix tailTrace_3343112
  have hstable : (prefixWord ++ tailWord_3343112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343112).length < 2 ^ (prefixWord ++ tailWord_3343112).sum := by decide
  have hdescent : baseEnd_3343112 < baseStart_3343112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343114 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_3343114 : Nat := 118140960795 + 3343114 * 2 ^ 59
def prefixEnd_3343114 : Nat := 4983230072969 + 3 ^ 40 * 3343114 * 2
def baseEnd_3343114 : Nat := 1144416243183425523200203

theorem tailTrace_3343114 : CollatzResearch.WordTrace tailWord_3343114 prefixEnd_3343114 1144416243183425523200203 := by
  unfold tailWord_3343114
  simp only [CollatzResearch.WordTrace]
  refine ⟨30483346202619102814997099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81288923206984274173325597 30483346202619102814997099)
  ·
    refine ⟨45725019303928654222495649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30483346202619102814997099 45725019303928654222495649)
    ·
      refine ⟨34293764477946490666871737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45725019303928654222495649 34293764477946490666871737)
      ·
        refine ⟨25720323358459868000153803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34293764477946490666871737 25720323358459868000153803)
        ·
          refine ⟨38580485037689802000230705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25720323358459868000153803 38580485037689802000230705)
          ·
            refine ⟨28935363778267351500173029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38580485037689802000230705 28935363778267351500173029)
            ·
              refine ⟨5425380708425128406282443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28935363778267351500173029 5425380708425128406282443)
              ·
                refine ⟨8138071062637692609423665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425380708425128406282443 8138071062637692609423665)
                ·
                  refine ⟨6103553296978269457067749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8138071062637692609423665 6103553296978269457067749)
                  ·
                    refine ⟨1144416243183425523200203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6103553296978269457067749 1144416243183425523200203)
                    ·
                      rfl

theorem cell22_3343114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_3343114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343114 prefixEnd_3343114 := by exact prefixLift 3343114
  have htrace : WordTrace (prefixWord ++ tailWord_3343114) baseStart_3343114 baseEnd_3343114 := by
    simpa [prefixWord, tailWord_3343114, baseEnd_3343114] using wordTrace_append hprefix tailTrace_3343114
  have hstable : (prefixWord ++ tailWord_3343114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343114).length < 2 ^ (prefixWord ++ tailWord_3343114).sum := by decide
  have hdescent : baseEnd_3343114 < baseStart_3343114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343191 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 5]
def baseStart_3343191 : Nat := 118140960795 + 3343191 * 2 ^ 59
def prefixEnd_3343191 : Nat := 4983230072969 + 3 ^ 40 * 3343191 * 2
def baseEnd_3343191 : Nat := 381480867285674329674989

theorem tailTrace_3343191 : CollatzResearch.WordTrace tailWord_3343191 prefixEnd_3343191 381480867285674329674989 := by
  unfold tailWord_3343191
  simp only [CollatzResearch.WordTrace]
  refine ⟨121936193231197453410541427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81290795487464968940360951 121936193231197453410541427)
  ·
    refine ⟨182904289846796180115812141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121936193231197453410541427 182904289846796180115812141)
    ·
      refine ⟨68589108692548567543429553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182904289846796180115812141 68589108692548567543429553)
      ·
        refine ⟨51441831519411425657572165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68589108692548567543429553 51441831519411425657572165)
        ·
          refine ⟨9645343409889642310794781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51441831519411425657572165 9645343409889642310794781)
          ·
            refine ⟨3617003778708615866548043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9645343409889642310794781 3617003778708615866548043)
            ·
              refine ⟨5425505668062923799822065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617003778708615866548043 5425505668062923799822065)
              ·
                refine ⟨4069129251047192849866549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5425505668062923799822065 4069129251047192849866549)
                ·
                  refine ⟨381480867285674329674989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4069129251047192849866549 381480867285674329674989)
                  ·
                    rfl

theorem cell22_3343191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 5].length) (baseStart_3343191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343191 prefixEnd_3343191 := by exact prefixLift 3343191
  have htrace : WordTrace (prefixWord ++ tailWord_3343191) baseStart_3343191 baseEnd_3343191 := by
    simpa [prefixWord, tailWord_3343191, baseEnd_3343191] using wordTrace_append hprefix tailTrace_3343191
  have hstable : (prefixWord ++ tailWord_3343191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343191).length < 2 ^ (prefixWord ++ tailWord_3343191).sum := by decide
  have hdescent : baseEnd_3343191 < baseStart_3343191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343221 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3343221 : Nat := 118140960795 + 3343221 * 2 ^ 59
def prefixEnd_3343221 : Nat := 4983230072969 + 3 ^ 40 * 3343221 * 2
def baseEnd_3343221 : Nat := 1144452871470112910774875

theorem tailTrace_3343221 : CollatzResearch.WordTrace tailWord_3343221 prefixEnd_3343221 1144452871470112910774875 := by
  unfold tailWord_3343221
  simp only [CollatzResearch.WordTrace]
  refine ⟨121937287421088768534133517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81291524947392512356089011 121937287421088768534133517)
  ·
    refine ⟨45726482782908288200300069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121937287421088768534133517 45726482782908288200300069)
    ·
      refine ⟨8573715521795304037556263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45726482782908288200300069 8573715521795304037556263)
      ·
        refine ⟨12860573282692956056334395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8573715521795304037556263 12860573282692956056334395)
        ·
          refine ⟨19290859924039434084501593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12860573282692956056334395 19290859924039434084501593)
          ·
            refine ⟨14468144943029575563376195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19290859924039434084501593 14468144943029575563376195)
            ·
              refine ⟨21702217414544363345064293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14468144943029575563376195 21702217414544363345064293)
              ·
                refine ⟨4069165765227068127199555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21702217414544363345064293 4069165765227068127199555)
                ·
                  refine ⟨6103748647840602190799333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069165765227068127199555 6103748647840602190799333)
                  ·
                    refine ⟨1144452871470112910774875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6103748647840602190799333 1144452871470112910774875)
                    ·
                      rfl

theorem cell22_3343221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3343221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343221 prefixEnd_3343221 := by exact prefixLift 3343221
  have htrace : WordTrace (prefixWord ++ tailWord_3343221) baseStart_3343221 baseEnd_3343221 := by
    simpa [prefixWord, tailWord_3343221, baseEnd_3343221] using wordTrace_append hprefix tailTrace_3343221
  have hstable : (prefixWord ++ tailWord_3343221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343221).length < 2 ^ (prefixWord ++ tailWord_3343221).sum := by decide
  have hdescent : baseEnd_3343221 < baseStart_3343221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343253 : List Nat := [1, 3, 2, 1, 1, 5, 3, 2, 4]
def baseStart_3343253 : Nat := 118140960795 + 3343253 * 2 ^ 59
def prefixEnd_3343253 : Nat := 4983230072969 + 3 ^ 40 * 3343253 * 2
def baseEnd_3343253 : Nat := 381487941908025164658259

theorem tailTrace_3343253 : CollatzResearch.WordTrace tailWord_3343253 prefixEnd_3343253 381487941908025164658259 := by
  unfold tailWord_3343253
  simp only [CollatzResearch.WordTrace]
  refine ⟨121938454556972837999298413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81292303037981891999532275 121938454556972837999298413)
  ·
    refine ⟨45726920458864814249736905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121938454556972837999298413 45726920458864814249736905)
    ·
      refine ⟨34295190344148610687302679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45726920458864814249736905 34295190344148610687302679)
      ·
        refine ⟨51442785516222916030954019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34295190344148610687302679 51442785516222916030954019)
        ·
          refine ⟨77164178274334374046431029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51442785516222916030954019 77164178274334374046431029)
          ·
            refine ⟨7234141713218847566852909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77164178274334374046431029 7234141713218847566852909)
            ·
              refine ⟨2712803142457067837569841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7234141713218847566852909 2712803142457067837569841)
              ·
                refine ⟨2034602356842800878177381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2712803142457067837569841 2034602356842800878177381)
                ·
                  refine ⟨381487941908025164658259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2034602356842800878177381 381487941908025164658259)
                  ·
                    rfl

theorem cell22_3343253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_3343253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343253 prefixEnd_3343253 := by exact prefixLift 3343253
  have htrace : WordTrace (prefixWord ++ tailWord_3343253) baseStart_3343253 baseEnd_3343253 := by
    simpa [prefixWord, tailWord_3343253, baseEnd_3343253] using wordTrace_append hprefix tailTrace_3343253
  have hstable : (prefixWord ++ tailWord_3343253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343253).length < 2 ^ (prefixWord ++ tailWord_3343253).sum := by decide
  have hdescent : baseEnd_3343253 < baseStart_3343253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343313 : List Nat := [1, 2, 2, 1, 2, 1, 5, 4, 1, 3]
def baseStart_3343313 : Nat := 118140960795 + 3343313 * 2 ^ 59
def prefixEnd_3343313 : Nat := 4983230072969 + 3 ^ 40 * 3343313 * 2
def baseEnd_3343313 : Nat := 1144484364950255337474593

theorem tailTrace_3343313 : CollatzResearch.WordTrace tailWord_3343313 prefixEnd_3343313 1144484364950255337474593 := by
  unfold tailWord_3343313
  simp only [CollatzResearch.WordTrace]
  refine ⟨121940642936755468246482593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81293761957836978830988395 121940642936755468246482593)
  ·
    refine ⟨91455482202566601184861945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121940642936755468246482593 91455482202566601184861945)
    ·
      refine ⟨68591611651924950888646459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91455482202566601184861945 68591611651924950888646459)
      ·
        refine ⟨102887417477887426332969689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68591611651924950888646459 102887417477887426332969689)
        ·
          refine ⟨77165563108415569749727267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102887417477887426332969689 77165563108415569749727267)
          ·
            refine ⟨115748344662623354624590901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77165563108415569749727267 115748344662623354624590901)
            ·
              refine ⟨10851407312120939496055397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115748344662623354624590901 10851407312120939496055397)
              ·
                refine ⟨2034638871022676155510387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10851407312120939496055397 2034638871022676155510387)
                ·
                  refine ⟨3051958306534014233265581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034638871022676155510387 3051958306534014233265581)
                  ·
                    refine ⟨1144484364950255337474593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3051958306534014233265581 1144484364950255337474593)
                    ·
                      rfl

theorem cell22_3343313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_3343313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343313 prefixEnd_3343313 := by exact prefixLift 3343313
  have htrace : WordTrace (prefixWord ++ tailWord_3343313) baseStart_3343313 baseEnd_3343313 := by
    simpa [prefixWord, tailWord_3343313, baseEnd_3343313] using wordTrace_append hprefix tailTrace_3343313
  have hstable : (prefixWord ++ tailWord_3343313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343313).length < 2 ^ (prefixWord ++ tailWord_3343313).sum := by decide
  have hdescent : baseEnd_3343313 < baseStart_3343313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343330 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3343330 : Nat := 118140960795 + 3343330 * 2 ^ 59
def prefixEnd_3343330 : Nat := 4983230072969 + 3 ^ 40 * 3343330 * 2
def baseEnd_3343330 : Nat := 1144490184397672959799541

theorem tailTrace_3343330 : CollatzResearch.WordTrace tailWord_3343330 prefixEnd_3343330 1144490184397672959799541 := by
  unfold tailWord_3343330
  simp only [CollatzResearch.WordTrace]
  refine ⟨30485315744423470037462861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81294175318462586766567629 30485315744423470037462861)
  ·
    refine ⟨11431993404158801264048573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30485315744423470037462861 11431993404158801264048573)
    ·
      refine ⟨4286997526559550474018215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11431993404158801264048573 4286997526559550474018215)
      ·
        refine ⟨6430496289839325711027323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4286997526559550474018215 6430496289839325711027323)
        ·
          refine ⟨9645744434758988566540985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6430496289839325711027323 9645744434758988566540985)
          ·
            refine ⟨7234308326069241424905739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9645744434758988566540985 7234308326069241424905739)
            ·
              refine ⟨10851462489103862137358609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7234308326069241424905739 10851462489103862137358609)
              ·
                refine ⟨8138596866827896603018957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10851462489103862137358609 8138596866827896603018957)
                ·
                  refine ⟨3051973825060461226132109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8138596866827896603018957 3051973825060461226132109)
                  ·
                    refine ⟨1144490184397672959799541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3051973825060461226132109 1144490184397672959799541)
                    ·
                      rfl

theorem cell22_3343330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3343330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343330 prefixEnd_3343330 := by exact prefixLift 3343330
  have htrace : WordTrace (prefixWord ++ tailWord_3343330) baseStart_3343330 baseEnd_3343330 := by
    simpa [prefixWord, tailWord_3343330, baseEnd_3343330] using wordTrace_append hprefix tailTrace_3343330
  have hstable : (prefixWord ++ tailWord_3343330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343330).length < 2 ^ (prefixWord ++ tailWord_3343330).sum := by decide
  have hdescent : baseEnd_3343330 < baseStart_3343330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343369 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_3343369 : Nat := 118140960795 + 3343369 * 2 ^ 59
def prefixEnd_3343369 : Nat := 4983230072969 + 3 ^ 40 * 3343369 * 2
def baseEnd_3343369 : Nat := 1144503534894689858074421

theorem tailTrace_3343369 : CollatzResearch.WordTrace tailWord_3343369 prefixEnd_3343369 1144503534894689858074421 := by
  unfold tailWord_3343369
  simp only [CollatzResearch.WordTrace]
  refine ⟨121942685424552589810521161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81295123616368393207014107 121942685424552589810521161)
  ·
    refine ⟨91457014068414442357890871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121942685424552589810521161 91457014068414442357890871)
    ·
      refine ⟨137185521102621663536836307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91457014068414442357890871 137185521102621663536836307)
      ·
        refine ⟨205778281653932495305254461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137185521102621663536836307 205778281653932495305254461)
        ·
          refine ⟨77166855620224685739470423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205778281653932495305254461 77166855620224685739470423)
          ·
            refine ⟨115750283430337028609205635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77166855620224685739470423 115750283430337028609205635)
            ·
              refine ⟨173625425145505542913808453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115750283430337028609205635 173625425145505542913808453)
              ·
                refine ⟨32554767214782289296339085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173625425145505542913808453 32554767214782289296339085)
                ·
                  refine ⟨12208037705543358486127157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32554767214782289296339085 12208037705543358486127157)
                  ·
                    refine ⟨1144503534894689858074421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12208037705543358486127157 1144503534894689858074421)
                    ·
                      rfl

theorem cell22_3343369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_3343369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343369 prefixEnd_3343369 := by exact prefixLift 3343369
  have htrace : WordTrace (prefixWord ++ tailWord_3343369) baseStart_3343369 baseEnd_3343369 := by
    simpa [prefixWord, tailWord_3343369, baseEnd_3343369] using wordTrace_append hprefix tailTrace_3343369
  have hstable : (prefixWord ++ tailWord_3343369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343369).length < 2 ^ (prefixWord ++ tailWord_3343369).sum := by decide
  have hdescent : baseEnd_3343369 < baseStart_3343369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343371 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 6]
def baseStart_3343371 : Nat := 118140960795 + 3343371 * 2 ^ 59
def prefixEnd_3343371 : Nat := 4983230072969 + 3 ^ 40 * 3343371 * 2
def baseEnd_3343371 : Nat := 381501406511854173174805

theorem tailTrace_3343371 : CollatzResearch.WordTrace tailWord_3343371 prefixEnd_3343371 381501406511854173174805 := by
  unfold tailWord_3343371
  simp only [CollatzResearch.WordTrace]
  refine ⟨121942758370545344152093967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81295172247030229434729311 121942758370545344152093967)
  ·
    refine ⟨182914137555818016228140951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121942758370545344152093967 182914137555818016228140951)
    ·
      refine ⟨274371206333727024342211427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182914137555818016228140951 274371206333727024342211427)
      ·
        refine ⟨411556809500590536513317141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274371206333727024342211427 411556809500590536513317141)
        ·
          refine ⟨19291725445340181399061741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 411556809500590536513317141 19291725445340181399061741)
          ·
            refine ⟨7234397042002568024648153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19291725445340181399061741 7234397042002568024648153)
            ·
              refine ⟨5425797781501926018486115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7234397042002568024648153 5425797781501926018486115)
              ·
                refine ⟨8138696672252889027729173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425797781501926018486115 8138696672252889027729173)
                ·
                  refine ⟨381501406511854173174805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8138696672252889027729173 381501406511854173174805)
                  ·
                    rfl

theorem cell22_3343371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 6].length) (baseStart_3343371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343371 prefixEnd_3343371 := by exact prefixLift 3343371
  have htrace : WordTrace (prefixWord ++ tailWord_3343371) baseStart_3343371 baseEnd_3343371 := by
    simpa [prefixWord, tailWord_3343371, baseEnd_3343371] using wordTrace_append hprefix tailTrace_3343371
  have hstable : (prefixWord ++ tailWord_3343371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343371).length < 2 ^ (prefixWord ++ tailWord_3343371).sum := by decide
  have hdescent : baseEnd_3343371 < baseStart_3343371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343416 : List Nat := [2, 1, 2, 1, 5, 3, 8]
def baseStart_3343416 : Nat := 118140960795 + 3343416 * 2 ^ 59
def prefixEnd_3343416 : Nat := 4983230072969 + 3 ^ 40 * 3343416 * 2
def baseEnd_3343416 : Nat := 42389615702044348227751

theorem tailTrace_3343416 : CollatzResearch.WordTrace tailWord_3343416 prefixEnd_3343416 42389615702044348227751 := by
  unfold tailWord_3343416
  simp only [CollatzResearch.WordTrace]
  refine ⟨60972199827691158418741051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81296266436921544558321401 60972199827691158418741051)
  ·
    refine ⟨91458299741536737628111577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60972199827691158418741051 91458299741536737628111577)
    ·
      refine ⟨68593724806152553221083683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91458299741536737628111577 68593724806152553221083683)
      ·
        refine ⟨102890587209228829831625525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68593724806152553221083683 102890587209228829831625525)
        ·
          refine ⟨9645992550865202796714893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102890587209228829831625525 9645992550865202796714893)
          ·
            refine ⟨3617247206574451048768085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9645992550865202796714893 3617247206574451048768085)
            ·
              refine ⟨42389615702044348227751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3617247206574451048768085 42389615702044348227751)
              ·
                rfl

theorem cell22_3343416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 8].length) (baseStart_3343416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343416 prefixEnd_3343416 := by exact prefixLift 3343416
  have htrace : WordTrace (prefixWord ++ tailWord_3343416) baseStart_3343416 baseEnd_3343416 := by
    simpa [prefixWord, tailWord_3343416, baseEnd_3343416] using wordTrace_append hprefix tailTrace_3343416
  have hstable : (prefixWord ++ tailWord_3343416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343416).length < 2 ^ (prefixWord ++ tailWord_3343416).sum := by decide
  have hdescent : baseEnd_3343416 < baseStart_3343416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343422 : List Nat := [4, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_3343422 : Nat := 118140960795 + 3343422 * 2 ^ 59
def prefixEnd_3343422 : Nat := 4983230072969 + 3 ^ 40 * 3343422 * 2
def baseEnd_3343422 : Nat := 381507225959271795499753

theorem tailTrace_3343422 : CollatzResearch.WordTrace tailWord_3343422 prefixEnd_3343422 381507225959271795499753 := by
  unfold tailWord_3343422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15243077311670072482775065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81296412328907053241467013 15243077311670072482775065)
  ·
    refine ⟨11432307983752554362081299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15243077311670072482775065 11432307983752554362081299)
    ·
      refine ⟨17148461975628831543121949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11432307983752554362081299 17148461975628831543121949)
      ·
        refine ⟨6430673240860811828670731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17148461975628831543121949 6430673240860811828670731)
        ·
          refine ⟨9646009861291217743006097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6430673240860811828670731 9646009861291217743006097)
          ·
            refine ⟨7234507395968413307254573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9646009861291217743006097 7234507395968413307254573)
            ·
              refine ⟨2712940273488154990220465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7234507395968413307254573 2712940273488154990220465)
              ·
                refine ⟨2034705205116116242665349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2712940273488154990220465 2034705205116116242665349)
                ·
                  refine ⟨381507225959271795499753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2034705205116116242665349 381507225959271795499753)
                  ·
                    rfl

theorem cell22_3343422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_3343422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343422 prefixEnd_3343422 := by exact prefixLift 3343422
  have htrace : WordTrace (prefixWord ++ tailWord_3343422) baseStart_3343422 baseEnd_3343422 := by
    simpa [prefixWord, tailWord_3343422, baseEnd_3343422] using wordTrace_append hprefix tailTrace_3343422
  have hstable : (prefixWord ++ tailWord_3343422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343422).length < 2 ^ (prefixWord ++ tailWord_3343422).sum := by decide
  have hdescent : baseEnd_3343422 < baseStart_3343422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343437 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3343437 : Nat := 118140960795 + 3343437 * 2 ^ 59
def prefixEnd_3343437 : Nat := 4983230072969 + 3 ^ 40 * 3343437 * 2
def baseEnd_3343437 : Nat := 1144526812684360347374213

theorem tailTrace_3343437 : CollatzResearch.WordTrace tailWord_3343437 prefixEnd_3343437 1144526812684360347374213 := by
  unfold tailWord_3343437
  simp only [CollatzResearch.WordTrace]
  refine ⟨121945165588306237423996565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81296777058870824949331043 121945165588306237423996565)
  ·
    refine ⟨5716179636951854879249839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121945165588306237423996565 5716179636951854879249839)
    ·
      refine ⟨8574269455427782318874759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5716179636951854879249839 8574269455427782318874759)
      ·
        refine ⟨12861404183141673478312139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8574269455427782318874759 12861404183141673478312139)
        ·
          refine ⟨19292106274712510217468209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12861404183141673478312139 19292106274712510217468209)
          ·
            refine ⟨14469079706034382663101157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19292106274712510217468209 14469079706034382663101157)
            ·
              refine ⟨2712952444881446749331467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14469079706034382663101157 2712952444881446749331467)
              ·
                refine ⟨4069428667322170123997201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712952444881446749331467 4069428667322170123997201)
                ·
                  refine ⟨3052071500491627592997901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4069428667322170123997201 3052071500491627592997901)
                  ·
                    refine ⟨1144526812684360347374213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3052071500491627592997901 1144526812684360347374213)
                    ·
                      rfl

theorem cell22_3343437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3343437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343437 prefixEnd_3343437 := by exact prefixLift 3343437
  have htrace : WordTrace (prefixWord ++ tailWord_3343437) baseStart_3343437 baseEnd_3343437 := by
    simpa [prefixWord, tailWord_3343437, baseEnd_3343437] using wordTrace_append hprefix tailTrace_3343437
  have hstable : (prefixWord ++ tailWord_3343437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343437).length < 2 ^ (prefixWord ++ tailWord_3343437).sum := by decide
  have hdescent : baseEnd_3343437 < baseStart_3343437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343491 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 5, 4]
def baseStart_3343491 : Nat := 118140960795 + 3343491 * 2 ^ 59
def prefixEnd_3343491 : Nat := 4983230072969 + 3 ^ 40 * 3343491 * 2
def baseEnd_3343491 : Nat := 1144545297987922206524047

theorem tailTrace_3343491 : CollatzResearch.WordTrace tailWord_3343491 prefixEnd_3343491 1144545297987922206524047 := by
  unfold tailWord_3343491
  simp only [CollatzResearch.WordTrace]
  refine ⟨121947135130110604646462327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81298090086740403097641551 121947135130110604646462327)
  ·
    refine ⟨182920702695165906969693491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121947135130110604646462327 182920702695165906969693491)
    ·
      refine ⟨274381054042748860454540237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182920702695165906969693491 274381054042748860454540237)
      ·
        refine ⟨102892895266030822670452589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274381054042748860454540237 102892895266030822670452589)
        ·
          refine ⟨38584835724761558501419721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102892895266030822670452589 38584835724761558501419721)
          ·
            refine ⟨28938626793571168876064791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38584835724761558501419721 28938626793571168876064791)
            ·
              refine ⟨43407940190356753314097187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28938626793571168876064791 43407940190356753314097187)
              ·
                refine ⟨65111910285535129971145781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43407940190356753314097187 65111910285535129971145781)
                ·
                  refine ⟨6104241589268918434794917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65111910285535129971145781 6104241589268918434794917)
                  ·
                    refine ⟨1144545297987922206524047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6104241589268918434794917 1144545297987922206524047)
                    ·
                      rfl

theorem cell22_3343491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 4].length) (baseStart_3343491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343491 prefixEnd_3343491 := by exact prefixLift 3343491
  have htrace : WordTrace (prefixWord ++ tailWord_3343491) baseStart_3343491 baseEnd_3343491 := by
    simpa [prefixWord, tailWord_3343491, baseEnd_3343491] using wordTrace_append hprefix tailTrace_3343491
  have hstable : (prefixWord ++ tailWord_3343491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343491).length < 2 ^ (prefixWord ++ tailWord_3343491).sum := by decide
  have hdescent : baseEnd_3343491 < baseStart_3343491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343493 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_3343493 : Nat := 118140960795 + 3343493 * 2 ^ 59
def prefixEnd_3343493 : Nat := 4983230072969 + 3 ^ 40 * 3343493 * 2
def baseEnd_3343493 : Nat := 1144545982628794867974041

theorem tailTrace_3343493 : CollatzResearch.WordTrace tailWord_3343493 prefixEnd_3343493 1144545982628794867974041 := by
  unfold tailWord_3343493
  simp only [CollatzResearch.WordTrace]
  refine ⟨121947208076103358988035133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81298138717402239325356755 121947208076103358988035133)
  ·
    refine ⟨45730203028538759620513175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121947208076103358988035133 45730203028538759620513175)
    ·
      refine ⟨68595304542808139430769763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45730203028538759620513175 68595304542808139430769763)
      ·
        refine ⟨102892956814212209146154645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68595304542808139430769763 102892956814212209146154645)
        ·
          refine ⟨4823107350666197303725999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102892956814212209146154645 4823107350666197303725999)
          ·
            refine ⟨7234661025999295955588999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4823107350666197303725999 7234661025999295955588999)
            ·
              refine ⟨10851991538998943933383499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7234661025999295955588999 10851991538998943933383499)
              ·
                refine ⟨16277987308498415900075249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10851991538998943933383499 16277987308498415900075249)
                ·
                  refine ⟨12208490481373811925056437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16277987308498415900075249 12208490481373811925056437)
                  ·
                    refine ⟨1144545982628794867974041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12208490481373811925056437 1144545982628794867974041)
                    ·
                      rfl

theorem cell22_3343493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_3343493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343493 prefixEnd_3343493 := by exact prefixLift 3343493
  have htrace : WordTrace (prefixWord ++ tailWord_3343493) baseStart_3343493 baseEnd_3343493 := by
    simpa [prefixWord, tailWord_3343493, baseEnd_3343493] using wordTrace_append hprefix tailTrace_3343493
  have hstable : (prefixWord ++ tailWord_3343493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343493).length < 2 ^ (prefixWord ++ tailWord_3343493).sum := by decide
  have hdescent : baseEnd_3343493 < baseStart_3343493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343525 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 1, 4]
def baseStart_3343525 : Nat := 118140960795 + 3343525 * 2 ^ 59
def prefixEnd_3343525 : Nat := 4983230072969 + 3 ^ 40 * 3343525 * 2
def baseEnd_3343525 : Nat := 1144556936882757451173943

theorem tailTrace_3343525 : CollatzResearch.WordTrace tailWord_3343525 prefixEnd_3343525 1144556936882757451173943 := by
  unfold tailWord_3343525
  simp only [CollatzResearch.WordTrace]
  refine ⟨121948375211987428453200029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81298916807991618968800019 121948375211987428453200029)
  ·
    refine ⟨45730640704495285669950011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121948375211987428453200029 45730640704495285669950011)
    ·
      refine ⟨68595961056742928504925017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45730640704495285669950011 68595961056742928504925017)
      ·
        refine ⟨51446970792557196378693763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68595961056742928504925017 51446970792557196378693763)
        ·
          refine ⟨77170456188835794568040645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51446970792557196378693763 77170456188835794568040645)
          ·
            refine ⟨14469460535406711481507621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77170456188835794568040645 14469460535406711481507621)
            ·
              refine ⟨2713023850388758402782679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14469460535406711481507621 2713023850388758402782679)
              ·
                refine ⟨4069535775583137604174019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713023850388758402782679 4069535775583137604174019)
                ·
                  refine ⟨6104303663374706406261029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069535775583137604174019 6104303663374706406261029)
                  ·
                    refine ⟨1144556936882757451173943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6104303663374706406261029 1144556936882757451173943)
                    ·
                      rfl

theorem cell22_3343525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_3343525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343525 prefixEnd_3343525 := by exact prefixLift 3343525
  have htrace : WordTrace (prefixWord ++ tailWord_3343525) baseStart_3343525 baseEnd_3343525 := by
    simpa [prefixWord, tailWord_3343525, baseEnd_3343525] using wordTrace_append hprefix tailTrace_3343525
  have hstable : (prefixWord ++ tailWord_3343525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343525).length < 2 ^ (prefixWord ++ tailWord_3343525).sum := by decide
  have hdescent : baseEnd_3343525 < baseStart_3343525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343583 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 5, 3]
def baseStart_3343583 : Nat := 118140960795 + 3343583 * 2 ^ 59
def prefixEnd_3343583 : Nat := 4983230072969 + 3 ^ 40 * 3343583 * 2
def baseEnd_3343583 : Nat := 1144576791468064633223765

theorem tailTrace_3343583 : CollatzResearch.WordTrace tailWord_3343583 prefixEnd_3343583 1144576791468064633223765 := by
  unfold tailWord_3343583
  simp only [CollatzResearch.WordTrace]
  refine ⟨121950490645777304358811403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81300327097184869572540935 121950490645777304358811403)
  ·
    refine ⟨182925735968665956538217105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121950490645777304358811403 182925735968665956538217105)
    ·
      refine ⟨137194301976499467403662829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182925735968665956538217105 137194301976499467403662829)
      ·
        refine ⟨51447863241187300276373561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137194301976499467403662829 51447863241187300276373561)
        ·
          refine ⟨38585897430890475207280171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51447863241187300276373561 38585897430890475207280171)
          ·
            refine ⟨57878846146335712810920257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38585897430890475207280171 57878846146335712810920257)
            ·
              refine ⟨43409134609751784608190193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57878846146335712810920257 43409134609751784608190193)
              ·
                refine ⟨32556850957313838456142645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43409134609751784608190193 32556850957313838456142645)
                ·
                  refine ⟨3052204777248172355263373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32556850957313838456142645 3052204777248172355263373)
                  ·
                    refine ⟨1144576791468064633223765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3052204777248172355263373 1144576791468064633223765)
                    ·
                      rfl

theorem cell22_3343583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 3].length) (baseStart_3343583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343583 prefixEnd_3343583 := by exact prefixLift 3343583
  have htrace : WordTrace (prefixWord ++ tailWord_3343583) baseStart_3343583 baseEnd_3343583 := by
    simpa [prefixWord, tailWord_3343583, baseEnd_3343583] using wordTrace_append hprefix tailTrace_3343583
  have hstable : (prefixWord ++ tailWord_3343583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343583).length < 2 ^ (prefixWord ++ tailWord_3343583).sum := by decide
  have hdescent : baseEnd_3343583 < baseStart_3343583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343692 : List Nat := [2, 2, 1, 3, 2, 3, 2, 3, 4]
def baseStart_3343692 : Nat := 118140960795 + 3343692 * 2 ^ 59
def prefixEnd_3343692 : Nat := 4983230072969 + 3 ^ 40 * 3343692 * 2
def baseEnd_3343692 : Nat := 381538034798541560749477

theorem tailTrace_3343692 : CollatzResearch.WordTrace tailWord_3343692 prefixEnd_3343692 381538034798541560749477 := by
  unfold tailWord_3343692
  simp only [CollatzResearch.WordTrace]
  refine ⟨60977233101191207987264665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81302977468254943983019553 60977233101191207987264665)
  ·
    refine ⟨45732924825893405990448499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60977233101191207987264665 45732924825893405990448499)
    ·
      refine ⟨68599387238840108985672749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45732924825893405990448499 68599387238840108985672749)
      ·
        refine ⟨25724770214565040869627281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68599387238840108985672749 25724770214565040869627281)
        ·
          refine ⟨19293577660923780652220461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25724770214565040869627281 19293577660923780652220461)
          ·
            refine ⟨7235091622846417744582673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19293577660923780652220461 7235091622846417744582673)
            ·
              refine ⟨5426318717134813308437005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7235091622846417744582673 5426318717134813308437005)
              ·
                refine ⟨2034869518925554990663877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5426318717134813308437005 2034869518925554990663877)
                ·
                  refine ⟨381538034798541560749477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2034869518925554990663877 381538034798541560749477)
                  ·
                    rfl

theorem cell22_3343692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_3343692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343692 prefixEnd_3343692 := by exact prefixLift 3343692
  have htrace : WordTrace (prefixWord ++ tailWord_3343692) baseStart_3343692 baseEnd_3343692 := by
    simpa [prefixWord, tailWord_3343692, baseEnd_3343692] using wordTrace_append hprefix tailTrace_3343692
  have hstable : (prefixWord ++ tailWord_3343692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343692).length < 2 ^ (prefixWord ++ tailWord_3343692).sum := by decide
  have hdescent : baseEnd_3343692 < baseStart_3343692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343703 : List Nat := [1, 1, 3, 2, 3, 3, 9]
def baseStart_3343703 : Nat := 118140960795 + 3343703 * 2 ^ 59
def prefixEnd_3343703 : Nat := 4983230072969 + 3 ^ 40 * 3343703 * 2
def baseEnd_3343703 : Nat := 42393254441497197045311

theorem tailTrace_3343703 : CollatzResearch.WordTrace tailWord_3343703 prefixEnd_3343703 42393254441497197045311 := by
  unfold tailWord_3343703
  simp only [CollatzResearch.WordTrace]
  refine ⟨121954867405342564853179763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81303244936895043235453175 121954867405342564853179763)
  ·
    refine ⟨182932301108013847279769645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121954867405342564853179763 182932301108013847279769645)
    ·
      refine ⟨68599612915505192729913617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182932301108013847279769645 68599612915505192729913617)
      ·
        refine ⟨51449709686628894547435213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68599612915505192729913617 51449709686628894547435213)
        ·
          refine ⟨19293641132485835455288205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51449709686628894547435213 19293641132485835455288205)
          ·
            refine ⟨7235115424682188295733077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19293641132485835455288205 7235115424682188295733077)
            ·
              refine ⟨42393254441497197045311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7235115424682188295733077 42393254441497197045311)
              ·
                rfl

theorem cell22_3343703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 9].length) (baseStart_3343703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343703 prefixEnd_3343703 := by exact prefixLift 3343703
  have htrace : WordTrace (prefixWord ++ tailWord_3343703) baseStart_3343703 baseEnd_3343703 := by
    simpa [prefixWord, tailWord_3343703, baseEnd_3343703] using wordTrace_append hprefix tailTrace_3343703
  have hstable : (prefixWord ++ tailWord_3343703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343703).length < 2 ^ (prefixWord ++ tailWord_3343703).sum := by decide
  have hdescent : baseEnd_3343703 < baseStart_3343703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343724 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 2, 3]
def baseStart_3343724 : Nat := 118140960795 + 3343724 * 2 ^ 59
def prefixEnd_3343724 : Nat := 4983230072969 + 3 ^ 40 * 3343724 * 2
def baseEnd_3343724 : Nat := 1144625058649587265448333

theorem tailTrace_3343724 : CollatzResearch.WordTrace tailWord_3343724 prefixEnd_3343724 1144625058649587265448333 := by
  unfold tailWord_3343724
  simp only [CollatzResearch.WordTrace]
  refine ⟨60977816669133242719847113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81303755558844323626462817 60977816669133242719847113)
  ·
    refine ⟨45733362501849932039885335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60977816669133242719847113 45733362501849932039885335)
    ·
      refine ⟨68600043752774898059828003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45733362501849932039885335 68600043752774898059828003)
      ·
        refine ⟨102900065629162347089742005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68600043752774898059828003 102900065629162347089742005)
        ·
          refine ⟨9646881152733970039663313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102900065629162347089742005 9646881152733970039663313)
          ·
            refine ⟨7235160864550477529747485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9646881152733970039663313 7235160864550477529747485)
            ·
              refine ⟨2713185324206429073655307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7235160864550477529747485 2713185324206429073655307)
              ·
                refine ⟨4069777986309643610482961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713185324206429073655307 4069777986309643610482961)
                ·
                  refine ⟨3052333489732232707862221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4069777986309643610482961 3052333489732232707862221)
                  ·
                    refine ⟨1144625058649587265448333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3052333489732232707862221 1144625058649587265448333)
                    ·
                      rfl

theorem cell22_3343724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_3343724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343724 prefixEnd_3343724 := by exact prefixLift 3343724
  have htrace : WordTrace (prefixWord ++ tailWord_3343724) baseStart_3343724 baseEnd_3343724 := by
    simpa [prefixWord, tailWord_3343724, baseEnd_3343724] using wordTrace_append hprefix tailTrace_3343724
  have hstable : (prefixWord ++ tailWord_3343724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343724).length < 2 ^ (prefixWord ++ tailWord_3343724).sum := by decide
  have hdescent : baseEnd_3343724 < baseStart_3343724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343735 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 3, 3]
def baseStart_3343735 : Nat := 118140960795 + 3343735 * 2 ^ 59
def prefixEnd_3343735 : Nat := 4983230072969 + 3 ^ 40 * 3343735 * 2
def baseEnd_3343735 : Nat := 1144628824174386903423299

theorem tailTrace_3343735 : CollatzResearch.WordTrace tailWord_3343735 prefixEnd_3343735 1144628824174386903423299 := by
  unfold tailWord_3343735
  simp only [CollatzResearch.WordTrace]
  refine ⟨121956034541226634318344659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81304023027484422878896439 121956034541226634318344659)
  ·
    refine ⟨182934051811839951477516989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121956034541226634318344659 182934051811839951477516989)
    ·
      refine ⟨68600269429439981804068871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182934051811839951477516989 68600269429439981804068871)
      ·
        refine ⟨102900404144159972706103307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68600269429439981804068871 102900404144159972706103307)
        ·
          refine ⟨154350606216239959059154961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102900404144159972706103307 154350606216239959059154961)
          ·
            refine ⟨115762954662179969294366221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154350606216239959059154961 115762954662179969294366221)
            ·
              refine ⟨43411107998317488485387333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115762954662179969294366221 43411107998317488485387333)
              ·
                refine ⟨8139582749684529091010125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43411107998317488485387333 8139582749684529091010125)
                ·
                  refine ⟨3052343531131698409128797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8139582749684529091010125 3052343531131698409128797)
                  ·
                    refine ⟨1144628824174386903423299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3052343531131698409128797 1144628824174386903423299)
                    ·
                      rfl

theorem cell22_3343735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_3343735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343735 prefixEnd_3343735 := by exact prefixLift 3343735
  have htrace : WordTrace (prefixWord ++ tailWord_3343735) baseStart_3343735 baseEnd_3343735 := by
    simpa [prefixWord, tailWord_3343735, baseEnd_3343735] using wordTrace_append hprefix tailTrace_3343735
  have hstable : (prefixWord ++ tailWord_3343735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343735).length < 2 ^ (prefixWord ++ tailWord_3343735).sum := by decide
  have hdescent : baseEnd_3343735 < baseStart_3343735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343857 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 2, 4]
def baseStart_3343857 : Nat := 118140960795 + 3343857 * 2 ^ 59
def prefixEnd_3343857 : Nat := 4983230072969 + 3 ^ 40 * 3343857 * 2
def baseEnd_3343857 : Nat := 1144670587267619251872925

theorem tailTrace_3343857 : CollatzResearch.WordTrace tailWord_3343857 prefixEnd_3343857 1144670587267619251872925 := by
  unfold tailWord_3343857
  simp only [CollatzResearch.WordTrace]
  refine ⟨121960484246784649154285825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81306989497856432769523883 121960484246784649154285825)
  ·
    refine ⟨91470363185088486865714369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121960484246784649154285825 91470363185088486865714369)
    ·
      refine ⟨68602772388816365149285777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91470363185088486865714369 68602772388816365149285777)
      ·
        refine ⟨51452079291612273861964333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68602772388816365149285777 51452079291612273861964333)
        ·
          refine ⟨19294529734354602698236625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51452079291612273861964333 19294529734354602698236625)
          ·
            refine ⟨14470897300765952023677469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19294529734354602698236625 14470897300765952023677469)
            ·
              refine ⟨5426586487787232008879051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14470897300765952023677469 5426586487787232008879051)
              ·
                refine ⟨8139879731680848013318577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5426586487787232008879051 8139879731680848013318577)
                ·
                  refine ⟨6104909798760636009988933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8139879731680848013318577 6104909798760636009988933)
                  ·
                    refine ⟨1144670587267619251872925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6104909798760636009988933 1144670587267619251872925)
                    ·
                      rfl

theorem cell22_3343857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_3343857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343857 prefixEnd_3343857 := by exact prefixLift 3343857
  have htrace : WordTrace (prefixWord ++ tailWord_3343857) baseStart_3343857 baseEnd_3343857 := by
    simpa [prefixWord, tailWord_3343857, baseEnd_3343857] using wordTrace_append hprefix tailTrace_3343857
  have hstable : (prefixWord ++ tailWord_3343857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343857).length < 2 ^ (prefixWord ++ tailWord_3343857).sum := by decide
  have hdescent : baseEnd_3343857 < baseStart_3343857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343861 : List Nat := [1, 3, 5, 1, 1, 2, 2, 3, 4]
def baseStart_3343861 : Nat := 118140960795 + 3343861 * 2 ^ 59
def prefixEnd_3343861 : Nat := 4983230072969 + 3 ^ 40 * 3343861 * 2
def baseEnd_3343861 : Nat := 381557318849788191590971

theorem tailTrace_3343861 : CollatzResearch.WordTrace tailWord_3343861 prefixEnd_3343861 381557318849788191590971 := by
  unfold tailWord_3343861
  simp only [CollatzResearch.WordTrace]
  refine ⟨121960630138770157837431437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81307086759180105224954291 121960630138770157837431437)
  ·
    refine ⟨45735236302038809189036789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121960630138770157837431437 45735236302038809189036789)
    ·
      refine ⟨4287678403316138361472199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45735236302038809189036789 4287678403316138361472199)
      ·
        refine ⟨6431517604974207542208299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4287678403316138361472199 6431517604974207542208299)
        ·
          refine ⟨9647276407461311313312449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6431517604974207542208299 9647276407461311313312449)
          ·
            refine ⟨7235457305595983484984337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9647276407461311313312449 7235457305595983484984337)
            ·
              refine ⟨5426592979196987613738253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7235457305595983484984337 5426592979196987613738253)
              ·
                refine ⟨2034972367198870355151845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5426592979196987613738253 2034972367198870355151845)
                ·
                  refine ⟨381557318849788191590971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2034972367198870355151845 381557318849788191590971)
                  ·
                    rfl

theorem cell22_3343861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_3343861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343861 prefixEnd_3343861 := by exact prefixLift 3343861
  have htrace : WordTrace (prefixWord ++ tailWord_3343861) baseStart_3343861 baseEnd_3343861 := by
    simpa [prefixWord, tailWord_3343861, baseEnd_3343861] using wordTrace_append hprefix tailTrace_3343861
  have hstable : (prefixWord ++ tailWord_3343861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343861).length < 2 ^ (prefixWord ++ tailWord_3343861).sum := by decide
  have hdescent : baseEnd_3343861 < baseStart_3343861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343878 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3343878 : Nat := 118140960795 + 3343878 * 2 ^ 59
def prefixEnd_3343878 : Nat := 4983230072969 + 3 ^ 40 * 3343878 * 2
def baseEnd_3343878 : Nat := 381559258665594065699287

theorem tailTrace_3343878 : CollatzResearch.WordTrace tailWord_3343878 prefixEnd_3343878 381559258665594065699287 := by
  unfold tailWord_3343878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811289068115892804400009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81307500119805713160533525 3811289068115892804400009)
  ·
    refine ⟨2858466801086919603300007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3811289068115892804400009 2858466801086919603300007)
    ·
      refine ⟨4287700201630379404950011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2858466801086919603300007 4287700201630379404950011)
      ·
        refine ⟨6431550302445569107425017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4287700201630379404950011 6431550302445569107425017)
        ·
          refine ⟨4823662726834176830568763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6431550302445569107425017 4823662726834176830568763)
          ·
            refine ⟨7235494090251265245853145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4823662726834176830568763 7235494090251265245853145)
            ·
              refine ⟨5426620567688448934389859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7235494090251265245853145 5426620567688448934389859)
              ·
                refine ⟨8139930851532673401584789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5426620567688448934389859 8139930851532673401584789)
                ·
                  refine ⟨381559258665594065699287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8139930851532673401584789 381559258665594065699287)
                  ·
                    rfl

theorem cell22_3343878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3343878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343878 prefixEnd_3343878 := by exact prefixLift 3343878
  have htrace : WordTrace (prefixWord ++ tailWord_3343878) baseStart_3343878 baseEnd_3343878 := by
    simpa [prefixWord, tailWord_3343878, baseEnd_3343878] using wordTrace_append hprefix tailTrace_3343878
  have hstable : (prefixWord ++ tailWord_3343878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343878).length < 2 ^ (prefixWord ++ tailWord_3343878).sum := by decide
  have hdescent : baseEnd_3343878 < baseStart_3343878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343904 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 3, 3]
def baseStart_3343904 : Nat := 118140960795 + 3343904 * 2 ^ 59
def prefixEnd_3343904 : Nat := 4983230072969 + 3 ^ 40 * 3343904 * 2
def baseEnd_3343904 : Nat := 1144686676328126795947781

theorem tailTrace_3343904 : CollatzResearch.WordTrace tailWord_3343904 prefixEnd_3343904 1144686676328126795947781 := by
  unfold tailWord_3343904
  simp only [CollatzResearch.WordTrace]
  refine ⟨60981099238807188090623383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81308132318409584120831177 60981099238807188090623383)
  ·
    refine ⟨91471648858210782135935075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60981099238807188090623383 91471648858210782135935075)
    ·
      refine ⟨137207473287316173203902613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91471648858210782135935075 137207473287316173203902613)
      ·
        refine ⟨6431600310342945618932935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137207473287316173203902613 6431600310342945618932935)
        ·
          refine ⟨9647400465514418428399403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6431600310342945618932935 9647400465514418428399403)
          ·
            refine ⟨14471100698271627642599105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9647400465514418428399403 14471100698271627642599105)
            ·
              refine ⟨10853325523703720731949329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14471100698271627642599105 10853325523703720731949329)
              ·
                refine ⟨8139994142777790548961997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10853325523703720731949329 8139994142777790548961997)
                ·
                  refine ⟨3052497803541671455860749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8139994142777790548961997 3052497803541671455860749)
                  ·
                    refine ⟨1144686676328126795947781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3052497803541671455860749 1144686676328126795947781)
                    ·
                      rfl

theorem cell22_3343904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3, 3].length) (baseStart_3343904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343904 prefixEnd_3343904 := by exact prefixLift 3343904
  have htrace : WordTrace (prefixWord ++ tailWord_3343904) baseStart_3343904 baseEnd_3343904 := by
    simpa [prefixWord, tailWord_3343904, baseEnd_3343904] using wordTrace_append hprefix tailTrace_3343904
  have hstable : (prefixWord ++ tailWord_3343904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343904).length < 2 ^ (prefixWord ++ tailWord_3343904).sum := by decide
  have hdescent : baseEnd_3343904 < baseStart_3343904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343964 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3343964 : Nat := 118140960795 + 3343964 * 2 ^ 59
def prefixEnd_3343964 : Nat := 4983230072969 + 3 ^ 40 * 3343964 * 2
def baseEnd_3343964 : Nat := 1144707215554306639447597

theorem tailTrace_3343964 : CollatzResearch.WordTrace tailWord_3343964 prefixEnd_3343964 1144707215554306639447597 := by
  unfold tailWord_3343964
  simp only [CollatzResearch.WordTrace]
  refine ⟨60982193428698503214215473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81309591238264670952287297 60982193428698503214215473)
  ·
    refine ⟨45736645071523877410661605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60982193428698503214215473 45736645071523877410661605)
    ·
      refine ⟨8575620950910727014499051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45736645071523877410661605 8575620950910727014499051)
      ·
        refine ⟨12863431426366090521748577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8575620950910727014499051 12863431426366090521748577)
        ·
          refine ⟨9647573569774567891311433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12863431426366090521748577 9647573569774567891311433)
          ·
            refine ⟨7235680177330925918483575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9647573569774567891311433 7235680177330925918483575)
            ·
              refine ⟨10853520265996388877725363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7235680177330925918483575 10853520265996388877725363)
              ·
                refine ⟨16280280398994583316588045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10853520265996388877725363 16280280398994583316588045)
                ·
                  refine ⟨6105105149622968743720517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16280280398994583316588045 6105105149622968743720517)
                  ·
                    refine ⟨1144707215554306639447597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105105149622968743720517 1144707215554306639447597)
                    ·
                      rfl

theorem cell22_3343964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3343964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343964 prefixEnd_3343964 := by exact prefixLift 3343964
  have htrace : WordTrace (prefixWord ++ tailWord_3343964) baseStart_3343964 baseEnd_3343964 := by
    simpa [prefixWord, tailWord_3343964, baseEnd_3343964] using wordTrace_append hprefix tailTrace_3343964
  have hstable : (prefixWord ++ tailWord_3343964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343964).length < 2 ^ (prefixWord ++ tailWord_3343964).sum := by decide
  have hdescent : baseEnd_3343964 < baseStart_3343964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3343977 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 6, 3]
def baseStart_3343977 : Nat := 118140960795 + 3343977 * 2 ^ 59
def prefixEnd_3343977 : Nat := 4983230072969 + 3 ^ 40 * 3343977 * 2
def baseEnd_3343977 : Nat := 1144711665719978938872557

theorem tailTrace_3343977 : CollatzResearch.WordTrace tailWord_3343977 prefixEnd_3343977 1144711665719978938872557 := by
  unfold tailWord_3343977
  simp only [CollatzResearch.WordTrace]
  refine ⟨121964861006349909648654185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81309907337566606432436123 121964861006349909648654185)
  ·
    refine ⟨91473645754762432236490639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121964861006349909648654185 91473645754762432236490639)
    ·
      refine ⟨137210468632143648354735959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91473645754762432236490639 137210468632143648354735959)
      ·
        refine ⟨205815702948215472532103939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137210468632143648354735959 205815702948215472532103939)
        ·
          refine ⟨308723554422323208798155909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205815702948215472532103939 308723554422323208798155909)
          ·
            refine ⟨57885666454185601649654233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308723554422323208798155909 57885666454185601649654233)
            ·
              refine ⟨43414249840639201237240675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57885666454185601649654233 43414249840639201237240675)
              ·
                refine ⟨65121374760958801855861013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43414249840639201237240675 65121374760958801855861013)
                ·
                  refine ⟨3052564441919943836993485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65121374760958801855861013 3052564441919943836993485)
                  ·
                    refine ⟨1144711665719978938872557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3052564441919943836993485 1144711665719978938872557)
                    ·
                      rfl

theorem cell22_3343977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 3].length) (baseStart_3343977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3343977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3343977 prefixEnd_3343977 := by exact prefixLift 3343977
  have htrace : WordTrace (prefixWord ++ tailWord_3343977) baseStart_3343977 baseEnd_3343977 := by
    simpa [prefixWord, tailWord_3343977, baseEnd_3343977] using wordTrace_append hprefix tailTrace_3343977
  have hstable : (prefixWord ++ tailWord_3343977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3343977).length < 2 ^ (prefixWord ++ tailWord_3343977).sum := by decide
  have hdescent : baseEnd_3343977 < baseStart_3343977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3343977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344007 : List Nat := [1, 1, 4, 2, 1, 3, 3, 7]
def baseStart_3344007 : Nat := 118140960795 + 3344007 * 2 ^ 59
def prefixEnd_3344007 : Nat := 4983230072969 + 3 ^ 40 * 3344007 * 2
def baseEnd_3344007 : Nat := 127191326148118762291385

theorem tailTrace_3344007 : CollatzResearch.WordTrace tailWord_3344007 prefixEnd_3344007 127191326148118762291385 := by
  unfold tailWord_3344007
  simp only [CollatzResearch.WordTrace]
  refine ⟨121965955196241224772246275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81310636797494149848164183 121965955196241224772246275)
  ·
    refine ⟨182948932794361837158369413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121965955196241224772246275 182948932794361837158369413)
    ·
      refine ⟨34302924898942844467194265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182948932794361837158369413 34302924898942844467194265)
      ·
        refine ⟨25727193674207133350395699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34302924898942844467194265 25727193674207133350395699)
        ·
          refine ⟨38590790511310700025593549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25727193674207133350395699 38590790511310700025593549)
          ·
            refine ⟨14471546441741512509597581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38590790511310700025593549 14471546441741512509597581)
            ·
              refine ⟨5426829915653067191099093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14471546441741512509597581 5426829915653067191099093)
              ·
                refine ⟨127191326148118762291385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5426829915653067191099093 127191326148118762291385)
                ·
                  rfl

theorem cell22_3344007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 7].length) (baseStart_3344007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344007 prefixEnd_3344007 := by exact prefixLift 3344007
  have htrace : WordTrace (prefixWord ++ tailWord_3344007) baseStart_3344007 baseEnd_3344007 := by
    simpa [prefixWord, tailWord_3344007, baseEnd_3344007] using wordTrace_append hprefix tailTrace_3344007
  have hstable : (prefixWord ++ tailWord_3344007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344007).length < 2 ^ (prefixWord ++ tailWord_3344007).sum := by decide
  have hdescent : baseEnd_3344007 < baseStart_3344007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344024 : List Nat := [2, 1, 2, 4, 1, 3, 3, 6]
def baseStart_3344024 : Nat := 118140960795 + 3344024 * 2 ^ 59
def prefixEnd_3344024 : Nat := 4983230072969 + 3 ^ 40 * 3344024 * 2
def baseEnd_3344024 : Nat := 127191972753387386994157

theorem tailTrace_3344024 : CollatzResearch.WordTrace tailWord_3344024 prefixEnd_3344024 127191972753387386994157 := by
  unfold tailWord_3344024
  simp only [CollatzResearch.WordTrace]
  refine ⟨60983287618589818337807563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81311050158119757783743417 60983287618589818337807563)
  ·
    refine ⟨91474931427884727506711345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60983287618589818337807563 91474931427884727506711345)
    ·
      refine ⟨68606198570913545630033509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91474931427884727506711345 68606198570913545630033509)
      ·
        refine ⟨12863662232046289805631283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68606198570913545630033509 12863662232046289805631283)
        ·
          refine ⟨19295493348069434708446925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12863662232046289805631283 19295493348069434708446925)
          ·
            refine ⟨7235810005526038015667597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19295493348069434708446925 7235810005526038015667597)
            ·
              refine ⟨2713428752072264255875349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7235810005526038015667597 2713428752072264255875349)
              ·
                refine ⟨127191972753387386994157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2713428752072264255875349 127191972753387386994157)
                ·
                  rfl

theorem cell22_3344024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 6].length) (baseStart_3344024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344024 prefixEnd_3344024 := by exact prefixLift 3344024
  have htrace : WordTrace (prefixWord ++ tailWord_3344024) baseStart_3344024 baseEnd_3344024 := by
    simpa [prefixWord, tailWord_3344024, baseEnd_3344024] using wordTrace_append hprefix tailTrace_3344024
  have hstable : (prefixWord ++ tailWord_3344024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344024).length < 2 ^ (prefixWord ++ tailWord_3344024).sum := by decide
  have hdescent : baseEnd_3344024 < baseStart_3344024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344112 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_3344112 : Nat := 118140960795 + 3344112 * 2 ^ 59
def prefixEnd_3344112 : Nat := 4983230072969 + 3 ^ 40 * 3344112 * 2
def baseEnd_3344112 : Nat := 1144757878978883586747143

theorem tailTrace_3344112 : CollatzResearch.WordTrace tailWord_3344112 prefixEnd_3344112 1144757878978883586747143 := by
  unfold tailWord_3344112
  simp only [CollatzResearch.WordTrace]
  refine ⟨60984892430430413852409295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81313189907240551803212393 60984892430430413852409295)
  ·
    refine ⟨91477338645645620778613943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60984892430430413852409295 91477338645645620778613943)
    ·
      refine ⟨137216007968468431167920915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91477338645645620778613943 137216007968468431167920915)
      ·
        refine ⟨205824011952702646751881373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137216007968468431167920915 205824011952702646751881373)
        ·
          refine ⟨77184004482263492531955515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205824011952702646751881373 77184004482263492531955515)
          ·
            refine ⟨115776006723395238797933273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77184004482263492531955515 115776006723395238797933273)
            ·
              refine ⟨86832005042546429098449955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115776006723395238797933273 86832005042546429098449955)
              ·
                refine ⟨130248007563819643647674933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86832005042546429098449955 130248007563819643647674933)
                ·
                  refine ⟨12210750709108091591969525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130248007563819643647674933 12210750709108091591969525)
                  ·
                    refine ⟨1144757878978883586747143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12210750709108091591969525 1144757878978883586747143)
                    ·
                      rfl

theorem cell22_3344112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_3344112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344112 prefixEnd_3344112 := by exact prefixLift 3344112
  have htrace : WordTrace (prefixWord ++ tailWord_3344112) baseStart_3344112 baseEnd_3344112 := by
    simpa [prefixWord, tailWord_3344112, baseEnd_3344112] using wordTrace_append hprefix tailTrace_3344112
  have hstable : (prefixWord ++ tailWord_3344112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344112).length < 2 ^ (prefixWord ++ tailWord_3344112).sum := by decide
  have hdescent : baseEnd_3344112 < baseStart_3344112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344127 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 3, 6]
def baseStart_3344127 : Nat := 118140960795 + 3344127 * 2 ^ 59
def prefixEnd_3344127 : Nat := 4983230072969 + 3 ^ 40 * 3344127 * 2
def baseEnd_3344127 : Nat := 1144763013785428547622097

theorem tailTrace_3344127 : CollatzResearch.WordTrace tailWord_3344127 prefixEnd_3344127 1144763013785428547622097 := by
  unfold tailWord_3344127
  simp only [CollatzResearch.WordTrace]
  refine ⟨121970331955806485266614635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81313554637204323511076423 121970331955806485266614635)
  ·
    refine ⟨182955497933709727899921953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121970331955806485266614635 182955497933709727899921953)
    ·
      refine ⟨137216623450282295924941465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182955497933709727899921953 137216623450282295924941465)
      ·
        refine ⟨102912467587711721943706099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137216623450282295924941465 102912467587711721943706099)
        ·
          refine ⟨154368701381567582915559149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102912467587711721943706099 154368701381567582915559149)
          ·
            refine ⟨57888263018087843593334681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154368701381567582915559149 57888263018087843593334681)
            ·
              refine ⟨43416197263565882695001011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57888263018087843593334681 43416197263565882695001011)
              ·
                refine ⟨65124295895348824042501517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43416197263565882695001011 65124295895348824042501517)
                ·
                  refine ⟨24421610960755809015938069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65124295895348824042501517 24421610960755809015938069)
                  ·
                    refine ⟨1144763013785428547622097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24421610960755809015938069 1144763013785428547622097)
                    ·
                      rfl

theorem cell22_3344127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_3344127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344127 prefixEnd_3344127 := by exact prefixLift 3344127
  have htrace : WordTrace (prefixWord ++ tailWord_3344127) baseStart_3344127 baseEnd_3344127 := by
    simpa [prefixWord, tailWord_3344127, baseEnd_3344127] using wordTrace_append hprefix tailTrace_3344127
  have hstable : (prefixWord ++ tailWord_3344127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344127).length < 2 ^ (prefixWord ++ tailWord_3344127).sum := by decide
  have hdescent : baseEnd_3344127 < baseStart_3344127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344146 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3344146 : Nat := 118140960795 + 3344146 * 2 ^ 59
def prefixEnd_3344146 : Nat := 4983230072969 + 3 ^ 40 * 3344146 * 2
def baseEnd_3344146 : Nat := 1144769517873718831397039

theorem tailTrace_3344146 : CollatzResearch.WordTrace tailWord_3344146 prefixEnd_3344146 1144769517873718831397039 := by
  unfold tailWord_3344146
  simp only [CollatzResearch.WordTrace]
  refine ⟨30492756235684412877889073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81314016628491767674370861 30492756235684412877889073)
  ·
    refine ⟨22869567176763309658416805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30492756235684412877889073 22869567176763309658416805)
    ·
      refine ⟨4288043845643120560953151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22869567176763309658416805 4288043845643120560953151)
      ·
        refine ⟨6432065768464680841429727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4288043845643120560953151 6432065768464680841429727)
        ·
          refine ⟨9648098652697021262144591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6432065768464680841429727 9648098652697021262144591)
          ·
            refine ⟨14472147979045531893216887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9648098652697021262144591 14472147979045531893216887)
            ·
              refine ⟨21708221968568297839825331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14472147979045531893216887 21708221968568297839825331)
              ·
                refine ⟨32562332952852446759737997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21708221968568297839825331 32562332952852446759737997)
                ·
                  refine ⟨12210874857319667534901749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32562332952852446759737997 12210874857319667534901749)
                  ·
                    refine ⟨1144769517873718831397039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12210874857319667534901749 1144769517873718831397039)
                    ·
                      rfl

theorem cell22_3344146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3344146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344146 prefixEnd_3344146 := by exact prefixLift 3344146
  have htrace : WordTrace (prefixWord ++ tailWord_3344146) baseStart_3344146 baseEnd_3344146 := by
    simpa [prefixWord, tailWord_3344146, baseEnd_3344146] using wordTrace_append hprefix tailTrace_3344146
  have hstable : (prefixWord ++ tailWord_3344146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344146).length < 2 ^ (prefixWord ++ tailWord_3344146).sum := by decide
  have hdescent : baseEnd_3344146 < baseStart_3344146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344249 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 6]
def baseStart_3344249 : Nat := 118140960795 + 3344249 * 2 ^ 59
def prefixEnd_3344249 : Nat := 4983230072969 + 3 ^ 40 * 3344249 * 2
def baseEnd_3344249 : Nat := 381601592292886965357241

theorem tailTrace_3344249 : CollatzResearch.WordTrace tailWord_3344249 prefixEnd_3344249 381601592292886965357241 := by
  unfold tailWord_3344249
  simp only [CollatzResearch.WordTrace]
  refine ⟨121974781661364500102555801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81316521107576333401703867 121974781661364500102555801)
  ·
    refine ⟨91481086246023375076916851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121974781661364500102555801 91481086246023375076916851)
    ·
      refine ⟨137221629369035062615375277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91481086246023375076916851 137221629369035062615375277)
      ·
        refine ⟨51458111013388148480765729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137221629369035062615375277 51458111013388148480765729)
        ·
          refine ⟨38593583260041111360574297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51458111013388148480765729 38593583260041111360574297)
          ·
            refine ⟨28945187445030833520430723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38593583260041111360574297 28945187445030833520430723)
            ·
              refine ⟨43417781167546250280646085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28945187445030833520430723 43417781167546250280646085)
              ·
                refine ⟨8140833968914921927621141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43417781167546250280646085 8140833968914921927621141)
                ·
                  refine ⟨381601592292886965357241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8140833968914921927621141 381601592292886965357241)
                  ·
                    rfl

theorem cell22_3344249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_3344249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344249 prefixEnd_3344249 := by exact prefixLift 3344249
  have htrace : WordTrace (prefixWord ++ tailWord_3344249) baseStart_3344249 baseEnd_3344249 := by
    simpa [prefixWord, tailWord_3344249, baseEnd_3344249] using wordTrace_append hprefix tailTrace_3344249
  have hstable : (prefixWord ++ tailWord_3344249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344249).length < 2 ^ (prefixWord ++ tailWord_3344249).sum := by decide
  have hdescent : baseEnd_3344249 < baseStart_3344249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344281 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 4, 3]
def baseStart_3344281 : Nat := 118140960795 + 3344281 * 2 ^ 59
def prefixEnd_3344281 : Nat := 4983230072969 + 3 ^ 40 * 3344281 * 2
def baseEnd_3344281 : Nat := 1144815731132623479271625

theorem tailTrace_3344281 : CollatzResearch.WordTrace tailWord_3344281 prefixEnd_3344281 1144815731132623479271625 := by
  unfold tailWord_3344281
  simp only [CollatzResearch.WordTrace]
  refine ⟨121975948797248569567720697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81317299198165713045147131 121975948797248569567720697)
  ·
    refine ⟨91481961597936427175790523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121975948797248569567720697 91481961597936427175790523)
    ·
      refine ⟨137222942396904640763685785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91481961597936427175790523 137222942396904640763685785)
      ·
        refine ⟨102917206797678480572764339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137222942396904640763685785 102917206797678480572764339)
        ·
          refine ⟨154375810196517720859146509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102917206797678480572764339 154375810196517720859146509)
          ·
            refine ⟨57890928823694145322179941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154375810196517720859146509 57890928823694145322179941)
            ·
              refine ⟨10854549154442652247908739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57890928823694145322179941 10854549154442652247908739)
              ·
                refine ⟨16281823731663978371863109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10854549154442652247908739 16281823731663978371863109)
                ·
                  refine ⟨3052841949686995944724333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16281823731663978371863109 3052841949686995944724333)
                  ·
                    refine ⟨1144815731132623479271625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3052841949686995944724333 1144815731132623479271625)
                    ·
                      rfl

theorem cell22_3344281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 3].length) (baseStart_3344281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344281 prefixEnd_3344281 := by exact prefixLift 3344281
  have htrace : WordTrace (prefixWord ++ tailWord_3344281) baseStart_3344281 baseEnd_3344281 := by
    simpa [prefixWord, tailWord_3344281, baseEnd_3344281] using wordTrace_append hprefix tailTrace_3344281
  have hstable : (prefixWord ++ tailWord_3344281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344281).length < 2 ^ (prefixWord ++ tailWord_3344281).sum := by decide
  have hdescent : baseEnd_3344281 < baseStart_3344281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344302 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3344302 : Nat := 118140960795 + 3344302 * 2 ^ 59
def prefixEnd_3344302 : Nat := 4983230072969 + 3 ^ 40 * 3344302 * 2
def baseEnd_3344302 : Nat := 1144822919861786424496561

theorem tailTrace_3344302 : CollatzResearch.WordTrace tailWord_3344302 prefixEnd_3344302 1144822919861786424496561 := by
  unfold tailWord_3344302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15247089341271561269279395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81317809820114993436156773 15247089341271561269279395)
  ·
    refine ⟨22870634011907341903919093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15247089341271561269279395 22870634011907341903919093)
    ·
      refine ⟨2144121938616313303492415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22870634011907341903919093 2144121938616313303492415)
      ·
        refine ⟨3216182907924469955238623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144121938616313303492415 3216182907924469955238623)
        ·
          refine ⟨4824274361886704932857935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216182907924469955238623 4824274361886704932857935)
          ·
            refine ⟨7236411542830057399286903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824274361886704932857935 7236411542830057399286903)
            ·
              refine ⟨10854617314245086098930355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236411542830057399286903 10854617314245086098930355)
              ·
                refine ⟨16281925971367629148395533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10854617314245086098930355 16281925971367629148395533)
                ·
                  refine ⟨6105722239262860930648325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16281925971367629148395533 6105722239262860930648325)
                  ·
                    refine ⟨1144822919861786424496561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105722239262860930648325 1144822919861786424496561)
                    ·
                      rfl

theorem cell22_3344302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3344302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344302 prefixEnd_3344302 := by exact prefixLift 3344302
  have htrace : WordTrace (prefixWord ++ tailWord_3344302) baseStart_3344302 baseEnd_3344302 := by
    simpa [prefixWord, tailWord_3344302, baseEnd_3344302] using wordTrace_append hprefix tailTrace_3344302
  have hstable : (prefixWord ++ tailWord_3344302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344302).length < 2 ^ (prefixWord ++ tailWord_3344302).sum := by decide
  have hdescent : baseEnd_3344302 < baseStart_3344302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344341 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3344341 : Nat := 118140960795 + 3344341 * 2 ^ 59
def prefixEnd_3344341 : Nat := 4983230072969 + 3 ^ 40 * 3344341 * 2
def baseEnd_3344341 : Nat := 1144836270358803322771441

theorem tailTrace_3344341 : CollatzResearch.WordTrace tailWord_3344341 prefixEnd_3344341 1144836270358803322771441 := by
  unfold tailWord_3344341
  simp only [CollatzResearch.WordTrace]
  refine ⟨121978137177031199814904877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81318758118020799876603251 121978137177031199814904877)
  ·
    refine ⟨45741801441386699930589329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121978137177031199814904877 45741801441386699930589329)
    ·
      refine ⟨34306351081040024947941997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45741801441386699930589329 34306351081040024947941997)
      ·
        refine ⟨12864881655390009355478249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34306351081040024947941997 12864881655390009355478249)
        ·
          refine ⟨9648661241542507016608687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12864881655390009355478249 9648661241542507016608687)
          ·
            refine ⟨14472991862313760524913031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9648661241542507016608687 14472991862313760524913031)
            ·
              refine ⟨21709487793470640787369547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14472991862313760524913031 21709487793470640787369547)
              ·
                refine ⟨32564231690205961181054321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21709487793470640787369547 32564231690205961181054321)
                ·
                  refine ⟨24423173767654470885790741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32564231690205961181054321 24423173767654470885790741)
                  ·
                    refine ⟨1144836270358803322771441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24423173767654470885790741 1144836270358803322771441)
                    ·
                      rfl

theorem cell22_3344341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3344341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344341 prefixEnd_3344341 := by exact prefixLift 3344341
  have htrace : WordTrace (prefixWord ++ tailWord_3344341) baseStart_3344341 baseEnd_3344341 := by
    simpa [prefixWord, tailWord_3344341, baseEnd_3344341] using wordTrace_append hprefix tailTrace_3344341
  have hstable : (prefixWord ++ tailWord_3344341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344341).length < 2 ^ (prefixWord ++ tailWord_3344341).sum := by decide
  have hdescent : baseEnd_3344341 < baseStart_3344341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344356 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 5]
def baseStart_3344356 : Nat := 118140960795 + 3344356 * 2 ^ 59
def prefixEnd_3344356 : Nat := 4983230072969 + 3 ^ 40 * 3344356 * 2
def baseEnd_3344356 : Nat := 381613801721782761215465

theorem tailTrace_3344356 : CollatzResearch.WordTrace tailWord_3344356 prefixEnd_3344356 381613801721782761215465 := by
  unfold tailWord_3344356
  simp only [CollatzResearch.WordTrace]
  refine ⟨60989342135988428688350461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81319122847984571584467281 60989342135988428688350461)
  ·
    refine ⟨22871003300995660758131423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60989342135988428688350461 22871003300995660758131423)
    ·
      refine ⟨34306504951493491137197135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22871003300995660758131423 34306504951493491137197135)
      ·
        refine ⟨51459757427240236705795703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34306504951493491137197135 51459757427240236705795703)
        ·
          refine ⟨77189636140860355058693555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51459757427240236705795703 77189636140860355058693555)
          ·
            refine ⟨115784454211290532588040333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77189636140860355058693555 115784454211290532588040333)
            ·
              refine ⟨43419170329233949720515125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115784454211290532588040333 43419170329233949720515125)
              ·
                refine ⟨4070547218365682786298293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43419170329233949720515125 4070547218365682786298293)
                ·
                  refine ⟨381613801721782761215465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4070547218365682786298293 381613801721782761215465)
                  ·
                    rfl

theorem cell22_3344356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_3344356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344356 prefixEnd_3344356 := by exact prefixLift 3344356
  have htrace : WordTrace (prefixWord ++ tailWord_3344356) baseStart_3344356 baseEnd_3344356 := by
    simpa [prefixWord, tailWord_3344356, baseEnd_3344356] using wordTrace_append hprefix tailTrace_3344356
  have hstable : (prefixWord ++ tailWord_3344356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344356).length < 2 ^ (prefixWord ++ tailWord_3344356).sum := by decide
  have hdescent : baseEnd_3344356 < baseStart_3344356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344433 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 4, 3]
def baseStart_3344433 : Nat := 118140960795 + 3344433 * 2 ^ 59
def prefixEnd_3344433 : Nat := 4983230072969 + 3 ^ 40 * 3344433 * 2
def baseEnd_3344433 : Nat := 1144867763838945749471159

theorem tailTrace_3344433 : CollatzResearch.WordTrace tailWord_3344433 prefixEnd_3344433 1144867763838945749471159 := by
  unfold tailWord_3344433
  simp only [CollatzResearch.WordTrace]
  refine ⟨121981492692697899527253953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81320995128465266351502635 121981492692697899527253953)
  ·
    refine ⟨91486119519523424645440465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121981492692697899527253953 91486119519523424645440465)
    ·
      refine ⟨68614589639642568484080349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91486119519523424645440465 68614589639642568484080349)
      ·
        refine ⟨25730471114865963181530131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68614589639642568484080349 25730471114865963181530131)
        ·
          refine ⟨38595706672298944772295197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25730471114865963181530131 38595706672298944772295197)
          ·
            refine ⟨14473390002112104289610699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38595706672298944772295197 14473390002112104289610699)
            ·
              refine ⟨21710085003168156434416049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14473390002112104289610699 21710085003168156434416049)
              ·
                refine ⟨16282563752376117325812037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21710085003168156434416049 16282563752376117325812037)
                ·
                  refine ⟨3052980703570521998589757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16282563752376117325812037 3052980703570521998589757)
                  ·
                    refine ⟨1144867763838945749471159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3052980703570521998589757 1144867763838945749471159)
                    ·
                      rfl

theorem cell22_3344433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_3344433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344433 prefixEnd_3344433 := by exact prefixLift 3344433
  have htrace : WordTrace (prefixWord ++ tailWord_3344433) baseStart_3344433 baseEnd_3344433 := by
    simpa [prefixWord, tailWord_3344433, baseEnd_3344433] using wordTrace_append hprefix tailTrace_3344433
  have hstable : (prefixWord ++ tailWord_3344433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344433).length < 2 ^ (prefixWord ++ tailWord_3344433).sum := by decide
  have hdescent : baseEnd_3344433 < baseStart_3344433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344448 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 2, 4]
def baseStart_3344448 : Nat := 118140960795 + 3344448 * 2 ^ 59
def prefixEnd_3344448 : Nat := 4983230072969 + 3 ^ 40 * 3344448 * 2
def baseEnd_3344448 : Nat := 1144872898645490710346113

theorem tailTrace_3344448 : CollatzResearch.WordTrace tailWord_3344448 prefixEnd_3344448 1144872898645490710346113 := by
  unfold tailWord_3344448
  simp only [CollatzResearch.WordTrace]
  refine ⟨60991019893821778544524999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81321359858429038059366665 60991019893821778544524999)
  ·
    refine ⟨91486529840732667816787499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60991019893821778544524999 91486529840732667816787499)
    ·
      refine ⟨137229794761099001725181249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91486529840732667816787499 137229794761099001725181249)
      ·
        refine ⟨102922346070824251293885937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137229794761099001725181249 102922346070824251293885937)
        ·
          refine ⟨77191759553118188470414453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102922346070824251293885937 77191759553118188470414453)
          ·
            refine ⟨7236727458104830169101355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77191759553118188470414453 7236727458104830169101355)
            ·
              refine ⟨10855091187157245253652033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236727458104830169101355 10855091187157245253652033)
              ·
                refine ⟨8141318390367933940239025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10855091187157245253652033 8141318390367933940239025)
                ·
                  refine ⟨6105988792775950455179269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8141318390367933940239025 6105988792775950455179269)
                  ·
                    refine ⟨1144872898645490710346113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6105988792775950455179269 1144872898645490710346113)
                    ·
                      rfl

theorem cell22_3344448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_3344448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344448 prefixEnd_3344448 := by exact prefixLift 3344448
  have htrace : WordTrace (prefixWord ++ tailWord_3344448) baseStart_3344448 baseEnd_3344448 := by
    simpa [prefixWord, tailWord_3344448, baseEnd_3344448] using wordTrace_append hprefix tailTrace_3344448
  have hstable : (prefixWord ++ tailWord_3344448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344448).length < 2 ^ (prefixWord ++ tailWord_3344448).sum := by decide
  have hdescent : baseEnd_3344448 < baseStart_3344448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344482 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3344482 : Nat := 118140960795 + 3344482 * 2 ^ 59
def prefixEnd_3344482 : Nat := 4983230072969 + 3 ^ 40 * 3344482 * 2
def baseEnd_3344482 : Nat := 1144884537540325954996009

theorem tailTrace_3344482 : CollatzResearch.WordTrace tailWord_3344482 prefixEnd_3344482 1144884537540325954996009 := by
  unfold tailWord_3344482
  simp only [CollatzResearch.WordTrace]
  refine ⟨30495819967380095223946925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81322186579680253930525133 30495819967380095223946925)
  ·
    refine ⟨11435932487767535708980097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30495819967380095223946925 11435932487767535708980097)
    ·
      refine ⟨8576949365825651781735073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11435932487767535708980097 8576949365825651781735073)
      ·
        refine ⟨6432712024369238836301305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8576949365825651781735073 6432712024369238836301305)
        ·
          refine ⟨4824534018276929127225979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6432712024369238836301305 4824534018276929127225979)
          ·
            refine ⟨7236801027415393690838969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824534018276929127225979 7236801027415393690838969)
            ·
              refine ⟨5427600770561545268129227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7236801027415393690838969 5427600770561545268129227)
              ·
                refine ⟨8141401155842317902193841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427600770561545268129227 8141401155842317902193841)
                ·
                  refine ⟨6106050866881738426645381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8141401155842317902193841 6106050866881738426645381)
                  ·
                    refine ⟨1144884537540325954996009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6106050866881738426645381 1144884537540325954996009)
                    ·
                      rfl

theorem cell22_3344482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3344482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344482 prefixEnd_3344482 := by exact prefixLift 3344482
  have htrace : WordTrace (prefixWord ++ tailWord_3344482) baseStart_3344482 baseEnd_3344482 := by
    simpa [prefixWord, tailWord_3344482, baseEnd_3344482] using wordTrace_append hprefix tailTrace_3344482
  have hstable : (prefixWord ++ tailWord_3344482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344482).length < 2 ^ (prefixWord ++ tailWord_3344482).sum := by decide
  have hdescent : baseEnd_3344482 < baseStart_3344482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344506 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_3344506 : Nat := 118140960795 + 3344506 * 2 ^ 59
def prefixEnd_3344506 : Nat := 4983230072969 + 3 ^ 40 * 3344506 * 2
def baseEnd_3344506 : Nat := 1144892753230797892395935

theorem tailTrace_3344506 : CollatzResearch.WordTrace tailWord_3344506 prefixEnd_3344506 1144892753230797892395935 := by
  unfold tailWord_3344506
  simp only [CollatzResearch.WordTrace]
  refine ⟨30496038805358358248665343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81322770147622288663107581 30496038805358358248665343)
  ·
    refine ⟨45744058208037537372998015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30496038805358358248665343 45744058208037537372998015)
    ·
      refine ⟨68616087312056306059497023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45744058208037537372998015 68616087312056306059497023)
      ·
        refine ⟨102924130968084459089245535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68616087312056306059497023 102924130968084459089245535)
        ·
          refine ⟨154386196452126688633868303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102924130968084459089245535 154386196452126688633868303)
          ·
            refine ⟨231579294678190032950802455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154386196452126688633868303 231579294678190032950802455)
            ·
              refine ⟨347368942017285049426203683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231579294678190032950802455 347368942017285049426203683)
              ·
                refine ⟨521053413025927574139305525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347368942017285049426203683 521053413025927574139305525)
                ·
                  refine ⟨48848757471180710075559893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 521053413025927574139305525 48848757471180710075559893)
                  ·
                    refine ⟨1144892753230797892395935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48848757471180710075559893 1144892753230797892395935)
                    ·
                      rfl

theorem cell22_3344506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_3344506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344506 prefixEnd_3344506 := by exact prefixLift 3344506
  have htrace : WordTrace (prefixWord ++ tailWord_3344506) baseStart_3344506 baseEnd_3344506 := by
    simpa [prefixWord, tailWord_3344506, baseEnd_3344506] using wordTrace_append hprefix tailTrace_3344506
  have hstable : (prefixWord ++ tailWord_3344506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344506).length < 2 ^ (prefixWord ++ tailWord_3344506).sum := by decide
  have hdescent : baseEnd_3344506 < baseStart_3344506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344508 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 5]
def baseStart_3344508 : Nat := 118140960795 + 3344508 * 2 ^ 59
def prefixEnd_3344508 : Nat := 4983230072969 + 3 ^ 40 * 3344508 * 2
def baseEnd_3344508 : Nat := 381631145957223517948643

theorem tailTrace_3344508 : CollatzResearch.WordTrace tailWord_3344508 prefixEnd_3344508 381631145957223517948643 := by
  unfold tailWord_3344508
  simp only [CollatzResearch.WordTrace]
  refine ⟨60992114083713093668117089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81322818778284124890822785 60992114083713093668117089)
  ·
    refine ⟨45744085562784820251087817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60992114083713093668117089 45744085562784820251087817)
    ·
      refine ⟨34308064172088615188315863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45744085562784820251087817 34308064172088615188315863)
      ·
        refine ⟨51462096258132922782473795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34308064172088615188315863 51462096258132922782473795)
        ·
          refine ⟨77193144387199384173710693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51462096258132922782473795 77193144387199384173710693)
          ·
            refine ⟨14473714572599884532570755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77193144387199384173710693 14473714572599884532570755)
            ·
              refine ⟨21710571858899826798856133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14473714572599884532570755 21710571858899826798856133)
              ·
                refine ⟨4070732223543717524785525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21710571858899826798856133 4070732223543717524785525)
                ·
                  refine ⟨381631145957223517948643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4070732223543717524785525 381631145957223517948643)
                  ·
                    rfl

theorem cell22_3344508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_3344508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344508 prefixEnd_3344508 := by exact prefixLift 3344508
  have htrace : WordTrace (prefixWord ++ tailWord_3344508) baseStart_3344508 baseEnd_3344508 := by
    simpa [prefixWord, tailWord_3344508, baseEnd_3344508] using wordTrace_append hprefix tailTrace_3344508
  have hstable : (prefixWord ++ tailWord_3344508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344508).length < 2 ^ (prefixWord ++ tailWord_3344508).sum := by decide
  have hdescent : baseEnd_3344508 < baseStart_3344508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344570 : List Nat := [3, 1, 1, 1, 2, 2, 4, 4, 4]
def baseStart_3344570 : Nat := 118140960795 + 3344570 * 2 ^ 59
def prefixEnd_3344570 : Nat := 4983230072969 + 3 ^ 40 * 3344570 * 2
def baseEnd_3344570 : Nat := 381638220579574352931913

theorem tailTrace_3344570 : CollatzResearch.WordTrace tailWord_3344570 prefixEnd_3344570 381638220579574352931913 := by
  unfold tailWord_3344570
  simp only [CollatzResearch.WordTrace]
  refine ⟨30496622373300392981247791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81324326328801047949994109 30496622373300392981247791)
  ·
    refine ⟨45744933559950589471871687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30496622373300392981247791 45744933559950589471871687)
    ·
      refine ⟨68617400339925884207807531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45744933559950589471871687 68617400339925884207807531)
      ·
        refine ⟨102926100509888826311711297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68617400339925884207807531 102926100509888826311711297)
        ·
          refine ⟨77194575382416619733783473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102926100509888826311711297 77194575382416619733783473)
          ·
            refine ⟨57895931536812464800337605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77194575382416619733783473 57895931536812464800337605)
            ·
              refine ⟨10855487163152337150063301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57895931536812464800337605 10855487163152337150063301)
              ·
                refine ⟨2035403843091063215636869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10855487163152337150063301 2035403843091063215636869)
                ·
                  refine ⟨381638220579574352931913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2035403843091063215636869 381638220579574352931913)
                  ·
                    rfl

theorem cell22_3344570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_3344570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344570 prefixEnd_3344570 := by exact prefixLift 3344570
  have htrace : WordTrace (prefixWord ++ tailWord_3344570) baseStart_3344570 baseEnd_3344570 := by
    simpa [prefixWord, tailWord_3344570, baseEnd_3344570] using wordTrace_append hprefix tailTrace_3344570
  have hstable : (prefixWord ++ tailWord_3344570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344570).length < 2 ^ (prefixWord ++ tailWord_3344570).sum := by decide
  have hdescent : baseEnd_3344570 < baseStart_3344570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344615 : List Nat := [1, 1, 5, 3, 1, 3, 8]
def baseStart_3344615 : Nat := 118140960795 + 3344615 * 2 ^ 59
def prefixEnd_3344615 : Nat := 4983230072969 + 3 ^ 40 * 3344615 * 2
def baseEnd_3344615 : Nat := 42404817265124368200763

theorem tailTrace_3344615 : CollatzResearch.WordTrace tailWord_3344615 prefixEnd_3344615 42404817265124368200763 := by
  unfold tailWord_3344615
  simp only [CollatzResearch.WordTrace]
  refine ⟨121988130778038544610379299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81325420518692363073586199 121988130778038544610379299)
  ·
    refine ⟨182982196167057816915568949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121988130778038544610379299 182982196167057816915568949)
    ·
      refine ⟨17154580890661670335834589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182982196167057816915568949 17154580890661670335834589)
      ·
        refine ⟨6432967833998126375937971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17154580890661670335834589 6432967833998126375937971)
        ·
          refine ⟨9649451750997189563906957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6432967833998126375937971 9649451750997189563906957)
          ·
            refine ⟨3618544406623946086465109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9649451750997189563906957 3618544406623946086465109)
            ·
              refine ⟨42404817265124368200763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3618544406623946086465109 42404817265124368200763)
              ·
                rfl

theorem cell22_3344615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 8].length) (baseStart_3344615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344615 prefixEnd_3344615 := by exact prefixLift 3344615
  have htrace : WordTrace (prefixWord ++ tailWord_3344615) baseStart_3344615 baseEnd_3344615 := by
    simpa [prefixWord, tailWord_3344615, baseEnd_3344615] using wordTrace_append hprefix tailTrace_3344615
  have hstable : (prefixWord ++ tailWord_3344615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344615).length < 2 ^ (prefixWord ++ tailWord_3344615).sum := by decide
  have hdescent : baseEnd_3344615 < baseStart_3344615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344677 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 5]
def baseStart_3344677 : Nat := 118140960795 + 3344677 * 2 ^ 59
def prefixEnd_3344677 : Nat := 4983230072969 + 3 ^ 40 * 3344677 * 2
def baseEnd_3344677 : Nat := 381650430008470148790137

theorem tailTrace_3344677 : CollatzResearch.WordTrace tailWord_3344677 prefixEnd_3344677 381650430008470148790137 := by
  unfold tailWord_3344677
  simp only [CollatzResearch.WordTrace]
  refine ⟨121990392103813929199136285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81326928069209286132757523 121990392103813929199136285)
  ·
    refine ⟨45746397038930223449676107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121990392103813929199136285 45746397038930223449676107)
    ·
      refine ⟨68619595558395335174514161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45746397038930223449676107 68619595558395335174514161)
      ·
        refine ⟨51464696668796501380885621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68619595558395335174514161 51464696668796501380885621)
        ·
          refine ⟨4824815312699672004458027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51464696668796501380885621 4824815312699672004458027)
          ·
            refine ⟨7237222969049508006687041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824815312699672004458027 7237222969049508006687041)
            ·
              refine ⟨5427917226787131005015281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7237222969049508006687041 5427917226787131005015281)
              ·
                refine ⟨4070937920090348253761461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5427917226787131005015281 4070937920090348253761461)
                ·
                  refine ⟨381650430008470148790137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4070937920090348253761461 381650430008470148790137)
                  ·
                    rfl

theorem cell22_3344677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_3344677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344677 prefixEnd_3344677 := by exact prefixLift 3344677
  have htrace : WordTrace (prefixWord ++ tailWord_3344677) baseStart_3344677 baseEnd_3344677 := by
    simpa [prefixWord, tailWord_3344677, baseEnd_3344677] using wordTrace_append hprefix tailTrace_3344677
  have hstable : (prefixWord ++ tailWord_3344677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344677).length < 2 ^ (prefixWord ++ tailWord_3344677).sum := by decide
  have hdescent : baseEnd_3344677 < baseStart_3344677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344692 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3344692 : Nat := 118140960795 + 3344692 * 2 ^ 59
def prefixEnd_3344692 : Nat := 4983230072969 + 3 ^ 40 * 3344692 * 2
def baseEnd_3344692 : Nat := 1144956424831955407245365

theorem tailTrace_3344692 : CollatzResearch.WordTrace tailWord_3344692 prefixEnd_3344692 1144956424831955407245365 := by
  unfold tailWord_3344692
  simp only [CollatzResearch.WordTrace]
  refine ⟨60995469599379793380466165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81327292799173057840621553 60995469599379793380466165)
  ·
    refine ⟨5718325274941855629418703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60995469599379793380466165 5718325274941855629418703)
    ·
      refine ⟨8577487912412783444128055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5718325274941855629418703 8577487912412783444128055)
      ·
        refine ⟨12866231868619175166192083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8577487912412783444128055 12866231868619175166192083)
        ·
          refine ⟨19299347802928762749288125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12866231868619175166192083 19299347802928762749288125)
          ·
            refine ⟨7237255426098286030983047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19299347802928762749288125 7237255426098286030983047)
            ·
              refine ⟨10855883139147429046474571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7237255426098286030983047 10855883139147429046474571)
              ·
                refine ⟨16283824708721143569711857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10855883139147429046474571 16283824708721143569711857)
                ·
                  refine ⟨12212868531540857677283893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16283824708721143569711857 12212868531540857677283893)
                  ·
                    refine ⟨1144956424831955407245365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12212868531540857677283893 1144956424831955407245365)
                    ·
                      rfl

theorem cell22_3344692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3344692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344692 prefixEnd_3344692 := by exact prefixLift 3344692
  have htrace : WordTrace (prefixWord ++ tailWord_3344692) baseStart_3344692 baseEnd_3344692 := by
    simpa [prefixWord, tailWord_3344692, baseEnd_3344692] using wordTrace_append hprefix tailTrace_3344692
  have hstable : (prefixWord ++ tailWord_3344692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344692).length < 2 ^ (prefixWord ++ tailWord_3344692).sum := by decide
  have hdescent : baseEnd_3344692 < baseStart_3344692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344720 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 1, 5]
def baseStart_3344720 : Nat := 118140960795 + 3344720 * 2 ^ 59
def prefixEnd_3344720 : Nat := 4983230072969 + 3 ^ 40 * 3344720 * 2
def baseEnd_3344720 : Nat := 1144966009804172667545279

theorem tailTrace_3344720 : CollatzResearch.WordTrace tailWord_3344720 prefixEnd_3344720 1144966009804172667545279 := by
  unfold tailWord_3344720
  simp only [CollatzResearch.WordTrace]
  refine ⟨60995980221329073771475807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81327973628438765028634409 60995980221329073771475807)
  ·
    refine ⟨91493970331993610657213711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60995980221329073771475807 91493970331993610657213711)
    ·
      refine ⟨137240955497990415985820567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91493970331993610657213711 137240955497990415985820567)
      ·
        refine ⟨205861433246985623978730851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137240955497990415985820567 205861433246985623978730851)
        ·
          refine ⟨308792149870478435968096277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205861433246985623978730851 308792149870478435968096277)
          ·
            refine ⟨14474632025178676686004513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 308792149870478435968096277 14474632025178676686004513)
            ·
              refine ⟨10855974018884007514503385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14474632025178676686004513 10855974018884007514503385)
              ·
                refine ⟨8141980514163005635877539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10855974018884007514503385 8141980514163005635877539)
                ·
                  refine ⟨12212970771244508453816309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8141980514163005635877539 12212970771244508453816309)
                  ·
                    refine ⟨1144966009804172667545279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12212970771244508453816309 1144966009804172667545279)
                    ·
                      rfl

theorem cell22_3344720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_3344720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344720 prefixEnd_3344720 := by exact prefixLift 3344720
  have htrace : WordTrace (prefixWord ++ tailWord_3344720) baseStart_3344720 baseEnd_3344720 := by
    simpa [prefixWord, tailWord_3344720, baseEnd_3344720] using wordTrace_append hprefix tailTrace_3344720
  have hstable : (prefixWord ++ tailWord_3344720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344720).length < 2 ^ (prefixWord ++ tailWord_3344720).sum := by decide
  have hdescent : baseEnd_3344720 < baseStart_3344720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344722 : List Nat := [3, 2, 2, 1, 1, 1, 3, 5, 4]
def baseStart_3344722 : Nat := 118140960795 + 3344722 * 2 ^ 59
def prefixEnd_3344722 : Nat := 4983230072969 + 3 ^ 40 * 3344722 * 2
def baseEnd_3344722 : Nat := 381655564815015109665091

theorem tailTrace_3344722 : CollatzResearch.WordTrace tailWord_3344722 prefixEnd_3344722 381655564815015109665091 := by
  unfold tailWord_3344722
  simp only [CollatzResearch.WordTrace]
  refine ⟨30498008347162725471131105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81328022259100601256349613 30498008347162725471131105)
  ·
    refine ⟨22873506260372044103348329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30498008347162725471131105 22873506260372044103348329)
    ·
      refine ⟨17155129695279033077511247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22873506260372044103348329 17155129695279033077511247)
      ·
        refine ⟨25732694542918549616266871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17155129695279033077511247 25732694542918549616266871)
        ·
          refine ⟨38599041814377824424400307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25732694542918549616266871 38599041814377824424400307)
          ·
            refine ⟨57898562721566736636600461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38599041814377824424400307 57898562721566736636600461)
            ·
              refine ⟨21711961020587526238725173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57898562721566736636600461 21711961020587526238725173)
              ·
                refine ⟨2035496345680080584880485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21711961020587526238725173 2035496345680080584880485)
                ·
                  refine ⟨381655564815015109665091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2035496345680080584880485 381655564815015109665091)
                  ·
                    rfl

theorem cell22_3344722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_3344722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344722 prefixEnd_3344722 := by exact prefixLift 3344722
  have htrace : WordTrace (prefixWord ++ tailWord_3344722) baseStart_3344722 baseEnd_3344722 := by
    simpa [prefixWord, tailWord_3344722, baseEnd_3344722] using wordTrace_append hprefix tailTrace_3344722
  have hstable : (prefixWord ++ tailWord_3344722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344722).length < 2 ^ (prefixWord ++ tailWord_3344722).sum := by decide
  have hdescent : baseEnd_3344722 < baseStart_3344722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344724 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_3344724 : Nat := 118140960795 + 3344724 * 2 ^ 59
def prefixEnd_3344724 : Nat := 4983230072969 + 3 ^ 40 * 3344724 * 2
def baseEnd_3344724 : Nat := 1144967379085917990445267

theorem tailTrace_3344724 : CollatzResearch.WordTrace tailWord_3344724 prefixEnd_3344724 1144967379085917990445267 := by
  unfold tailWord_3344724
  simp only [CollatzResearch.WordTrace]
  refine ⟨60996053167321828113048613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81328070889762437484064817 60996053167321828113048613)
  ·
    refine ⟨11436759968872842771196615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60996053167321828113048613 11436759968872842771196615)
    ·
      refine ⟨17155139953309264156794923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11436759968872842771196615 17155139953309264156794923)
      ·
        refine ⟨25732709929963896235192385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17155139953309264156794923 25732709929963896235192385)
        ·
          refine ⟨19299532447472922176394289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25732709929963896235192385 19299532447472922176394289)
          ·
            refine ⟨14474649335604691632295717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19299532447472922176394289 14474649335604691632295717)
            ·
              refine ⟨2713996750425879681055447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14474649335604691632295717 2713996750425879681055447)
              ·
                refine ⟨4070995125638819521583171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713996750425879681055447 4070995125638819521583171)
                ·
                  refine ⟨6106492688458229282374757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4070995125638819521583171 6106492688458229282374757)
                  ·
                    refine ⟨1144967379085917990445267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6106492688458229282374757 1144967379085917990445267)
                    ·
                      rfl

theorem cell22_3344724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_3344724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344724 prefixEnd_3344724 := by exact prefixLift 3344724
  have htrace : WordTrace (prefixWord ++ tailWord_3344724) baseStart_3344724 baseEnd_3344724 := by
    simpa [prefixWord, tailWord_3344724, baseEnd_3344724] using wordTrace_append hprefix tailTrace_3344724
  have hstable : (prefixWord ++ tailWord_3344724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344724).length < 2 ^ (prefixWord ++ tailWord_3344724).sum := by decide
  have hdescent : baseEnd_3344724 < baseStart_3344724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344735 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 2, 4]
def baseStart_3344735 : Nat := 118140960795 + 3344735 * 2 ^ 59
def prefixEnd_3344735 : Nat := 4983230072969 + 3 ^ 40 * 3344735 * 2
def baseEnd_3344735 : Nat := 1144971144610717628420233

theorem tailTrace_3344735 : CollatzResearch.WordTrace tailWord_3344735 prefixEnd_3344735 1144971144610717628420233 := by
  unfold tailWord_3344735
  simp only [CollatzResearch.WordTrace]
  refine ⟨121992507537603805104747659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81328338358402536736498439 121992507537603805104747659)
  ·
    refine ⟨182988761306405707657121489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121992507537603805104747659 182988761306405707657121489)
    ·
      refine ⟨137241570979804280742841117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182988761306405707657121489 137241570979804280742841117)
      ·
        refine ⟨51465589117426605278565419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137241570979804280742841117 51465589117426605278565419)
        ·
          refine ⟨77198383676139907917848129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51465589117426605278565419 77198383676139907917848129)
          ·
            refine ⟨57898787757104930938386097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77198383676139907917848129 57898787757104930938386097)
            ·
              refine ⟨43424090817828698203789573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57898787757104930938386097 43424090817828698203789573)
              ·
                refine ⟨8142017028342880913210545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43424090817828698203789573 8142017028342880913210545)
                ·
                  refine ⟨6106512771257160684907909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8142017028342880913210545 6106512771257160684907909)
                  ·
                    refine ⟨1144971144610717628420233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6106512771257160684907909 1144971144610717628420233)
                    ·
                      rfl

theorem cell22_3344735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_3344735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344735 prefixEnd_3344735 := by exact prefixLift 3344735
  have htrace : WordTrace (prefixWord ++ tailWord_3344735) baseStart_3344735 baseEnd_3344735 := by
    simpa [prefixWord, tailWord_3344735, baseEnd_3344735] using wordTrace_append hprefix tailTrace_3344735
  have hstable : (prefixWord ++ tailWord_3344735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344735).length < 2 ^ (prefixWord ++ tailWord_3344735).sum := by decide
  have hdescent : baseEnd_3344735 < baseStart_3344735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344790 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3344790 : Nat := 118140960795 + 3344790 * 2 ^ 59
def prefixEnd_3344790 : Nat := 4983230072969 + 3 ^ 40 * 3344790 * 2
def baseEnd_3344790 : Nat := 381663324078238606098355

theorem tailTrace_3344790 : CollatzResearch.WordTrace tailWord_3344790 prefixEnd_3344790 381663324078238606098355 := by
  unfold tailWord_3344790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7624657097025284343624989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81329675701603032998666549 7624657097025284343624989)
  ·
    refine ⟨2859246411384481628859371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7624657097025284343624989 2859246411384481628859371)
    ·
      refine ⟨4288869617076722443289057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2859246411384481628859371 4288869617076722443289057)
      ·
        refine ⟨3216652212807541832466793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4288869617076722443289057 3216652212807541832466793)
        ·
          refine ⟨2412489159605656374350095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3216652212807541832466793 2412489159605656374350095)
          ·
            refine ⟨3618733739408484561525143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412489159605656374350095 3618733739408484561525143)
            ·
              refine ⟨5428100609112726842287715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3618733739408484561525143 5428100609112726842287715)
              ·
                refine ⟨8142150913669090263431573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428100609112726842287715 8142150913669090263431573)
                ·
                  refine ⟨381663324078238606098355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8142150913669090263431573 381663324078238606098355)
                  ·
                    rfl

theorem cell22_3344790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3344790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344790 prefixEnd_3344790 := by exact prefixLift 3344790
  have htrace : WordTrace (prefixWord ++ tailWord_3344790) baseStart_3344790 baseEnd_3344790 := by
    simpa [prefixWord, tailWord_3344790, baseEnd_3344790] using wordTrace_append hprefix tailTrace_3344790
  have hstable : (prefixWord ++ tailWord_3344790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344790).length < 2 ^ (prefixWord ++ tailWord_3344790).sum := by decide
  have hdescent : baseEnd_3344790 < baseStart_3344790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344872 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 1, 5]
def baseStart_3344872 : Nat := 118140960795 + 3344872 * 2 ^ 59
def prefixEnd_3344872 : Nat := 4983230072969 + 3 ^ 40 * 3344872 * 2
def baseEnd_3344872 : Nat := 1145018042510494937744813

theorem tailTrace_3344872 : CollatzResearch.WordTrace tailWord_3344872 prefixEnd_3344872 1145018042510494937744813 := by
  unfold tailWord_3344872
  simp only [CollatzResearch.WordTrace]
  refine ⟨60998752169053738751242435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81331669558738318334989913 60998752169053738751242435)
  ·
    refine ⟨91498128253580608126863653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60998752169053738751242435 91498128253580608126863653)
    ·
      refine ⟨17155899047546364023786935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91498128253580608126863653 17155899047546364023786935)
      ·
        refine ⟨25733848571319546035680403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17155899047546364023786935 25733848571319546035680403)
        ·
          refine ⟨38600772856979319053520605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25733848571319546035680403 38600772856979319053520605)
          ·
            refine ⟨14475289821367244645070227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38600772856979319053520605 14475289821367244645070227)
            ·
              refine ⟨21712934732050866967605341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14475289821367244645070227 21712934732050866967605341)
              ·
                refine ⟨8142350524519075112852003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21712934732050866967605341 8142350524519075112852003)
                ·
                  refine ⟨12213525786778612669278005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8142350524519075112852003 12213525786778612669278005)
                  ·
                    refine ⟨1145018042510494937744813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12213525786778612669278005 1145018042510494937744813)
                    ·
                      rfl

theorem cell22_3344872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_3344872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344872 prefixEnd_3344872 := by exact prefixLift 3344872
  have htrace : WordTrace (prefixWord ++ tailWord_3344872) baseStart_3344872 baseEnd_3344872 := by
    simpa [prefixWord, tailWord_3344872, baseEnd_3344872] using wordTrace_append hprefix tailTrace_3344872
  have hstable : (prefixWord ++ tailWord_3344872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344872).length < 2 ^ (prefixWord ++ tailWord_3344872).sum := by decide
  have hdescent : baseEnd_3344872 < baseStart_3344872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344936 : List Nat := [2, 1, 5, 2, 1, 3, 2, 6]
def baseStart_3344936 : Nat := 118140960795 + 3344936 * 2 ^ 59
def prefixEnd_3344936 : Nat := 4983230072969 + 3 ^ 40 * 3344936 * 2
def baseEnd_3344936 : Nat := 127226661224268900460513

theorem tailTrace_3344936 : CollatzResearch.WordTrace tailWord_3344936 prefixEnd_3344936 127226661224268900460513 := by
  unfold tailWord_3344936
  simp only [CollatzResearch.WordTrace]
  refine ⟨60999919304937808216407331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81333225739917077621876441 60999919304937808216407331)
  ·
    refine ⟨91499878957406712324610997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60999919304937808216407331 91499878957406712324610997)
    ·
      refine ⟨8578113652256879280432281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91499878957406712324610997 8578113652256879280432281)
      ·
        refine ⟨6433585239192659460324211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8578113652256879280432281 6433585239192659460324211)
        ·
          refine ⟨9650377858788989190486317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6433585239192659460324211 9650377858788989190486317)
          ·
            refine ⟨3618891697045870946432369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9650377858788989190486317 3618891697045870946432369)
            ·
              refine ⟨2714168772784403209824277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3618891697045870946432369 2714168772784403209824277)
              ·
                refine ⟨127226661224268900460513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2714168772784403209824277 127226661224268900460513)
                ·
                  rfl

theorem cell22_3344936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 6].length) (baseStart_3344936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344936 prefixEnd_3344936 := by exact prefixLift 3344936
  have htrace : WordTrace (prefixWord ++ tailWord_3344936) baseStart_3344936 baseEnd_3344936 := by
    simpa [prefixWord, tailWord_3344936, baseEnd_3344936] using wordTrace_append hprefix tailTrace_3344936
  have hstable : (prefixWord ++ tailWord_3344936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344936).length < 2 ^ (prefixWord ++ tailWord_3344936).sum := by decide
  have hdescent : baseEnd_3344936 < baseStart_3344936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3344992 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 6]
def baseStart_3344992 : Nat := 118140960795 + 3344992 * 2 ^ 59
def prefixEnd_3344992 : Nat := 4983230072969 + 3 ^ 40 * 3344992 * 2
def baseEnd_3344992 : Nat := 381686373654284874914815

theorem tailTrace_3344992 : CollatzResearch.WordTrace tailWord_3344992 prefixEnd_3344992 381686373654284874914815 := by
  unfold tailWord_3344992
  simp only [CollatzResearch.WordTrace]
  refine ⟨61000940548836368998426615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81334587398448491997902153 61000940548836368998426615)
  ·
    refine ⟨91501410823254553497639923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61000940548836368998426615 91501410823254553497639923)
    ·
      refine ⟨137252116234881830246459885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91501410823254553497639923 137252116234881830246459885)
      ·
        refine ⟨51469543588080686342422457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137252116234881830246459885 51469543588080686342422457)
        ·
          refine ⟨38602157691060514756816843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51469543588080686342422457 38602157691060514756816843)
          ·
            refine ⟨57903236536590772135225265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38602157691060514756816843 57903236536590772135225265)
            ·
              refine ⟨43427427402443079101418949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57903236536590772135225265 43427427402443079101418949)
              ·
                refine ⟨8142642637958077331516053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43427427402443079101418949 8142642637958077331516053)
                ·
                  refine ⟨381686373654284874914815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8142642637958077331516053 381686373654284874914815)
                  ·
                    rfl

theorem cell22_3344992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_3344992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3344992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3344992 prefixEnd_3344992 := by exact prefixLift 3344992
  have htrace : WordTrace (prefixWord ++ tailWord_3344992) baseStart_3344992 baseEnd_3344992 := by
    simpa [prefixWord, tailWord_3344992, baseEnd_3344992] using wordTrace_append hprefix tailTrace_3344992
  have hstable : (prefixWord ++ tailWord_3344992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3344992).length < 2 ^ (prefixWord ++ tailWord_3344992).sum := by decide
  have hdescent : baseEnd_3344992 < baseStart_3344992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3344992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345007 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 3, 5]
def baseStart_3345007 : Nat := 118140960795 + 3345007 * 2 ^ 59
def prefixEnd_3345007 : Nat := 4983230072969 + 3 ^ 40 * 3345007 * 2
def baseEnd_3345007 : Nat := 1145064255769399585619399

theorem tailTrace_3345007 : CollatzResearch.WordTrace tailWord_3345007 prefixEnd_3345007 1145064255769399585619399 := by
  unfold tailWord_3345007
  simp only [CollatzResearch.WordTrace]
  refine ⟨122002428192618395558649275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81334952128412263705766183 122002428192618395558649275)
  ·
    refine ⟨183003642288927593337973913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122002428192618395558649275 183003642288927593337973913)
    ·
      refine ⟨137252731716695695003480435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183003642288927593337973913 137252731716695695003480435)
      ·
        refine ⟨205879097575043542505220653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137252731716695695003480435 205879097575043542505220653)
        ·
          refine ⟨77204661590641328439457745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205879097575043542505220653 77204661590641328439457745)
          ·
            refine ⟨57903496192980996329593309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77204661590641328439457745 57903496192980996329593309)
            ·
              refine ⟨21713811072367873623597491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57903496192980996329593309 21713811072367873623597491)
              ·
                refine ⟨32570716608551810435396237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21713811072367873623597491 32570716608551810435396237)
                ·
                  refine ⟨12214018728206928913273589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32570716608551810435396237 12214018728206928913273589)
                  ·
                    refine ⟨1145064255769399585619399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12214018728206928913273589 1145064255769399585619399)
                    ·
                      rfl

theorem cell22_3345007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_3345007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345007 prefixEnd_3345007 := by exact prefixLift 3345007
  have htrace : WordTrace (prefixWord ++ tailWord_3345007) baseStart_3345007 baseEnd_3345007 := by
    simpa [prefixWord, tailWord_3345007, baseEnd_3345007] using wordTrace_append hprefix tailTrace_3345007
  have hstable : (prefixWord ++ tailWord_3345007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345007).length < 2 ^ (prefixWord ++ tailWord_3345007).sum := by decide
  have hdescent : baseEnd_3345007 < baseStart_3345007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345116 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 7]
def baseStart_3345116 : Nat := 118140960795 + 3345116 * 2 ^ 59
def prefixEnd_3345116 : Nat := 4983230072969 + 3 ^ 40 * 3345116 * 2
def baseEnd_3345116 : Nat := 381700522898986544881355

theorem tailTrace_3345116 : CollatzResearch.WordTrace tailWord_3345116 prefixEnd_3345116 381700522898986544881355 := by
  unfold tailWord_3345116
  simp only [CollatzResearch.WordTrace]
  refine ⟨61003201874611753587183601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81337602499482338116244801 61003201874611753587183601)
  ·
    refine ⟨45752401405958815190387701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61003201874611753587183601 45752401405958815190387701)
    ·
      refine ⟨4289287631808638924098847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45752401405958815190387701 4289287631808638924098847)
      ·
        refine ⟨6433931447712958386148271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4289287631808638924098847 6433931447712958386148271)
        ·
          refine ⟨9650897171569437579222407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6433931447712958386148271 9650897171569437579222407)
          ·
            refine ⟨14476345757354156368833611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9650897171569437579222407 14476345757354156368833611)
            ·
              refine ⟨21714518636031234553250417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14476345757354156368833611 21714518636031234553250417)
              ·
                refine ⟨16285888977023425914937813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21714518636031234553250417 16285888977023425914937813)
                ·
                  refine ⟨381700522898986544881355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16285888977023425914937813 381700522898986544881355)
                  ·
                    rfl

theorem cell22_3345116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_3345116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345116 prefixEnd_3345116 := by exact prefixLift 3345116
  have htrace : WordTrace (prefixWord ++ tailWord_3345116) baseStart_3345116 baseEnd_3345116 := by
    simpa [prefixWord, tailWord_3345116, baseEnd_3345116] using wordTrace_append hprefix tailTrace_3345116
  have hstable : (prefixWord ++ tailWord_3345116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345116).length < 2 ^ (prefixWord ++ tailWord_3345116).sum := by decide
  have hdescent : baseEnd_3345116 < baseStart_3345116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345150 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_3345150 : Nat := 118140960795 + 3345150 * 2 ^ 59
def prefixEnd_3345150 : Nat := 4983230072969 + 3 ^ 40 * 3345150 * 2
def baseEnd_3345150 : Nat := 381704402530598293097987

theorem tailTrace_3345150 : CollatzResearch.WordTrace tailWord_3345150 prefixEnd_3345150 381704402530598293097987 := by
  unfold tailWord_3345150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15250955478887541372638113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81338429220733553987403269 15250955478887541372638113)
  ·
    refine ⟨11438216609165656029478585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15250955478887541372638113 11438216609165656029478585)
    ·
      refine ⟨8578662456874242022108939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11438216609165656029478585 8578662456874242022108939)
      ·
        refine ⟨12867993685311363033163409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8578662456874242022108939 12867993685311363033163409)
        ·
          refine ⟨9650995263983522274872557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12867993685311363033163409 9650995263983522274872557)
          ·
            refine ⟨3619123223993820853077209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9650995263983522274872557 3619123223993820853077209)
            ·
              refine ⟨2714342417995365639807907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3619123223993820853077209 2714342417995365639807907)
              ·
                refine ⟨4071513626993048459711861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714342417995365639807907 4071513626993048459711861)
                ·
                  refine ⟨381704402530598293097987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4071513626993048459711861 381704402530598293097987)
                  ·
                    rfl

theorem cell22_3345150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_3345150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345150 prefixEnd_3345150 := by exact prefixLift 3345150
  have htrace : WordTrace (prefixWord ++ tailWord_3345150) baseStart_3345150 baseEnd_3345150 := by
    simpa [prefixWord, tailWord_3345150, baseEnd_3345150] using wordTrace_append hprefix tailTrace_3345150
  have hstable : (prefixWord ++ tailWord_3345150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345150).length < 2 ^ (prefixWord ++ tailWord_3345150).sum := by decide
  have hdescent : baseEnd_3345150 < baseStart_3345150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345219 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 2, 6]
def baseStart_3345219 : Nat := 118140960795 + 3345219 * 2 ^ 59
def prefixEnd_3345219 : Nat := 4983230072969 + 3 ^ 40 * 3345219 * 2
def baseEnd_3345219 : Nat := 1145136827701901699318749

theorem tailTrace_3345219 : CollatzResearch.WordTrace tailWord_3345219 prefixEnd_3345219 1145136827701901699318749 := by
  unfold tailWord_3345219
  simp only [CollatzResearch.WordTrace]
  refine ⟨122010160467850355765366711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81340106978566903843577807 122010160467850355765366711)
  ·
    refine ⟨183015240701775533648050067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122010160467850355765366711 183015240701775533648050067)
    ·
      refine ⟨274522861052663300472075101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183015240701775533648050067 274522861052663300472075101)
      ·
        refine ⟨102946072894748737677028163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274522861052663300472075101 102946072894748737677028163)
        ·
          refine ⟨154419109342123106515542245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102946072894748737677028163 154419109342123106515542245)
          ·
            refine ⟨28953583001648082471664171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154419109342123106515542245 28953583001648082471664171)
            ·
              refine ⟨43430374502472123707496257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28953583001648082471664171 43430374502472123707496257)
              ·
                refine ⟨32572780876854092780622193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43430374502472123707496257 32572780876854092780622193)
                ·
                  refine ⟨24429585657640569585466645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32572780876854092780622193 24429585657640569585466645)
                  ·
                    refine ⟨1145136827701901699318749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24429585657640569585466645 1145136827701901699318749)
                    ·
                      rfl

theorem cell22_3345219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_3345219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345219 prefixEnd_3345219 := by exact prefixLift 3345219
  have htrace : WordTrace (prefixWord ++ tailWord_3345219) baseStart_3345219 baseEnd_3345219 := by
    simpa [prefixWord, tailWord_3345219, baseEnd_3345219] using wordTrace_append hprefix tailTrace_3345219
  have hstable : (prefixWord ++ tailWord_3345219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345219).length < 2 ^ (prefixWord ++ tailWord_3345219).sum := by decide
  have hdescent : baseEnd_3345219 < baseStart_3345219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345251 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 7]
def baseStart_3345251 : Nat := 118140960795 + 3345251 * 2 ^ 59
def prefixEnd_3345251 : Nat := 4983230072969 + 3 ^ 40 * 3345251 * 2
def baseEnd_3345251 : Nat := 381715927318621427506217

theorem tailTrace_3345251 : CollatzResearch.WordTrace tailWord_3345251 prefixEnd_3345251 381715927318621427506217 := by
  unfold tailWord_3345251
  simp only [CollatzResearch.WordTrace]
  refine ⟨122011327603734425230531607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81340885069156283487021071 122011327603734425230531607)
  ·
    refine ⟨183016991405601637845797411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122011327603734425230531607 183016991405601637845797411)
    ·
      refine ⟨274525487108402456768696117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183016991405601637845797411 274525487108402456768696117)
      ·
        refine ⟨25736764416412730322065261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 274525487108402456768696117 25736764416412730322065261)
        ·
          refine ⟨9651286656154773870774473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25736764416412730322065261 9651286656154773870774473)
          ·
            refine ⟨7238464992116080403080855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9651286656154773870774473 7238464992116080403080855)
            ·
              refine ⟨10857697488174120604621283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7238464992116080403080855 10857697488174120604621283)
              ·
                refine ⟨16286546232261180906931925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10857697488174120604621283 16286546232261180906931925)
                ·
                  refine ⟨381715927318621427506217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16286546232261180906931925 381715927318621427506217)
                  ·
                    rfl

theorem cell22_3345251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 7].length) (baseStart_3345251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345251 prefixEnd_3345251 := by exact prefixLift 3345251
  have htrace : WordTrace (prefixWord ++ tailWord_3345251) baseStart_3345251 baseEnd_3345251 := by
    simpa [prefixWord, tailWord_3345251, baseEnd_3345251] using wordTrace_append hprefix tailTrace_3345251
  have hstable : (prefixWord ++ tailWord_3345251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345251).length < 2 ^ (prefixWord ++ tailWord_3345251).sum := by decide
  have hdescent : baseEnd_3345251 < baseStart_3345251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345255 : List Nat := [1, 1, 5, 1, 2, 2, 2, 4, 1, 3]
def baseStart_3345255 : Nat := 118140960795 + 3345255 * 2 ^ 59
def prefixEnd_3345255 : Nat := 4983230072969 + 3 ^ 40 * 3345255 * 2
def baseEnd_3345255 : Nat := 1145149151237609605418639

theorem tailTrace_3345255 : CollatzResearch.WordTrace tailWord_3345255 prefixEnd_3345255 1145149151237609605418639 := by
  unfold tailWord_3345255
  simp only [CollatzResearch.WordTrace]
  refine ⟨122011473495719933913677219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81340982330479955942451479 122011473495719933913677219)
  ·
    refine ⟨183017210243579900870515829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122011473495719933913677219 183017210243579900870515829)
    ·
      refine ⟨17157863460335615706610859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183017210243579900870515829 17157863460335615706610859)
      ·
        refine ⟨25736795190503423559916289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17157863460335615706610859 25736795190503423559916289)
        ·
          refine ⟨19302596392877567669937217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25736795190503423559916289 19302596392877567669937217)
          ·
            refine ⟨14476947294658175752452913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19302596392877567669937217 14476947294658175752452913)
            ·
              refine ⟨10857710470993631814339685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14476947294658175752452913 10857710470993631814339685)
              ·
                refine ⟨2035820713311305965188691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10857710470993631814339685 2035820713311305965188691)
                ·
                  refine ⟨3053731069966958947783037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2035820713311305965188691 3053731069966958947783037)
                  ·
                    refine ⟨1145149151237609605418639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3053731069966958947783037 1145149151237609605418639)
                    ·
                      rfl

theorem cell22_3345255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_3345255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345255 prefixEnd_3345255 := by exact prefixLift 3345255
  have htrace : WordTrace (prefixWord ++ tailWord_3345255) baseStart_3345255 baseEnd_3345255 := by
    simpa [prefixWord, tailWord_3345255, baseEnd_3345255] using wordTrace_append hprefix tailTrace_3345255
  have hstable : (prefixWord ++ tailWord_3345255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345255).length < 2 ^ (prefixWord ++ tailWord_3345255).sum := by decide
  have hdescent : baseEnd_3345255 < baseStart_3345255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345266 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_3345266 : Nat := 118140960795 + 3345266 * 2 ^ 59
def prefixEnd_3345266 : Nat := 4983230072969 + 3 ^ 40 * 3345266 * 2
def baseEnd_3345266 : Nat := 1145152916762409243393605

theorem tailTrace_3345266 : CollatzResearch.WordTrace tailWord_3345266 prefixEnd_3345266 1145152916762409243393605 := by
  unfold tailWord_3345266
  simp only [CollatzResearch.WordTrace]
  refine ⟨30502968674670020698081913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81341249799120055194885101 30502968674670020698081913)
  ·
    refine ⟨22877226506002515523561435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30502968674670020698081913 22877226506002515523561435)
    ·
      refine ⟨34315839759003773285342153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22877226506002515523561435 34315839759003773285342153)
      ·
        refine ⟨25736879819252829964006615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34315839759003773285342153 25736879819252829964006615)
        ·
          refine ⟨38605319728879244946009923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25736879819252829964006615 38605319728879244946009923)
          ·
            refine ⟨57907979593318867419014885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38605319728879244946009923 57907979593318867419014885)
            ·
              refine ⟨10857746173747287641065291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57907979593318867419014885 10857746173747287641065291)
              ·
                refine ⟨16286619260620931461597937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10857746173747287641065291 16286619260620931461597937)
                ·
                  refine ⟨12214964445465698596198453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16286619260620931461597937 12214964445465698596198453)
                  ·
                    refine ⟨1145152916762409243393605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12214964445465698596198453 1145152916762409243393605)
                    ·
                      rfl

theorem cell22_3345266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_3345266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345266 prefixEnd_3345266 := by exact prefixLift 3345266
  have htrace : WordTrace (prefixWord ++ tailWord_3345266) baseStart_3345266 baseEnd_3345266 := by
    simpa [prefixWord, tailWord_3345266, baseEnd_3345266] using wordTrace_append hprefix tailTrace_3345266
  have hstable : (prefixWord ++ tailWord_3345266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345266).length < 2 ^ (prefixWord ++ tailWord_3345266).sum := by decide
  have hdescent : baseEnd_3345266 < baseStart_3345266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345313 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 6]
def baseStart_3345313 : Nat := 118140960795 + 3345313 * 2 ^ 59
def prefixEnd_3345313 : Nat := 4983230072969 + 3 ^ 40 * 3345313 * 2
def baseEnd_3345313 : Nat := 381723001940972262489487

theorem tailTrace_3345313 : CollatzResearch.WordTrace tailWord_3345313 prefixEnd_3345313 381723001940972262489487 := by
  unfold tailWord_3345313
  simp only [CollatzResearch.WordTrace]
  refine ⟨122013588929509809819288593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81342392619673206546192395 122013588929509809819288593)
  ·
    refine ⟨91510191697132357364466445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122013588929509809819288593 91510191697132357364466445)
    ·
      refine ⟨34316321886424634011674917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91510191697132357364466445 34316321886424634011674917)
      ·
        refine ⟨6434310353704618877189047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34316321886424634011674917 6434310353704618877189047)
        ·
          refine ⟨9651465530556928315783571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6434310353704618877189047 9651465530556928315783571)
          ·
            refine ⟨14477198295835392473675357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9651465530556928315783571 14477198295835392473675357)
            ·
              refine ⟨5428949360938272177628259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14477198295835392473675357 5428949360938272177628259)
              ·
                refine ⟨8143424041407408266442389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428949360938272177628259 8143424041407408266442389)
                ·
                  refine ⟨381723001940972262489487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8143424041407408266442389 381723001940972262489487)
                  ·
                    rfl

theorem cell22_3345313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_3345313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345313 prefixEnd_3345313 := by exact prefixLift 3345313
  have htrace : WordTrace (prefixWord ++ tailWord_3345313) baseStart_3345313 baseEnd_3345313 := by
    simpa [prefixWord, tailWord_3345313, baseEnd_3345313] using wordTrace_append hprefix tailTrace_3345313
  have hstable : (prefixWord ++ tailWord_3345313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345313).length < 2 ^ (prefixWord ++ tailWord_3345313).sum := by decide
  have hdescent : baseEnd_3345313 < baseStart_3345313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345332 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3345332 : Nat := 118140960795 + 3345332 * 2 ^ 59
def prefixEnd_3345332 : Nat := 4983230072969 + 3 ^ 40 * 3345332 * 2
def baseEnd_3345332 : Nat := 1145175509911207071243403

theorem tailTrace_3345332 : CollatzResearch.WordTrace tailWord_3345332 prefixEnd_3345332 1145175509911207071243403 := by
  unfold tailWord_3345332
  simp only [CollatzResearch.WordTrace]
  refine ⟨61007140958220488032115125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81342854610960650709486833 61007140958220488032115125)
  ·
    refine ⟨5719419464833170753010793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61007140958220488032115125 5719419464833170753010793)
    ·
      refine ⟨4289564598624878064758095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5719419464833170753010793 4289564598624878064758095)
      ·
        refine ⟨6434346897937317097137143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4289564598624878064758095 6434346897937317097137143)
        ·
          refine ⟨9651520346905975645705715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6434346897937317097137143 9651520346905975645705715)
          ·
            refine ⟨14477280520358963468558573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9651520346905975645705715 14477280520358963468558573)
            ·
              refine ⟨5428980195134611300709465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14477280520358963468558573 5428980195134611300709465)
              ·
                refine ⟨4071735146350958475532099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5428980195134611300709465 4071735146350958475532099)
                ·
                  refine ⟨6107602719526437713298149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071735146350958475532099 6107602719526437713298149)
                  ·
                    refine ⟨1145175509911207071243403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6107602719526437713298149 1145175509911207071243403)
                    ·
                      rfl

theorem cell22_3345332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3345332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345332 prefixEnd_3345332 := by exact prefixLift 3345332
  have htrace : WordTrace (prefixWord ++ tailWord_3345332) baseStart_3345332 baseEnd_3345332 := by
    simpa [prefixWord, tailWord_3345332, baseEnd_3345332] using wordTrace_append hprefix tailTrace_3345332
  have hstable : (prefixWord ++ tailWord_3345332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345332).length < 2 ^ (prefixWord ++ tailWord_3345332).sum := by decide
  have hdescent : baseEnd_3345332 < baseStart_3345332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345362 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_3345362 : Nat := 118140960795 + 3345362 * 2 ^ 59
def prefixEnd_3345362 : Nat := 4983230072969 + 3 ^ 40 * 3345362 * 2
def baseEnd_3345362 : Nat := 1145185779524296992993311

theorem tailTrace_3345362 : CollatzResearch.WordTrace tailWord_3345362 prefixEnd_3345362 1145185779524296992993311 := by
  unfold tailWord_3345362
  simp only [CollatzResearch.WordTrace]
  refine ⟨30503844026583072796955585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81343584070888194125214893 30503844026583072796955585)
  ·
    refine ⟨22877883019937304597716689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30503844026583072796955585 22877883019937304597716689)
    ·
      refine ⟨17158412264952978448287517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22877883019937304597716689 17158412264952978448287517)
      ·
        refine ⟨6434404599357366918107819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17158412264952978448287517 6434404599357366918107819)
        ·
          refine ⟨9651606899036050377161729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6434404599357366918107819 9651606899036050377161729)
          ·
            refine ⟨7238705174277037782871297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9651606899036050377161729 7238705174277037782871297)
            ·
              refine ⟨5429028880707778337153473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7238705174277037782871297 5429028880707778337153473)
              ·
                refine ⟨4071771660530833752865105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5429028880707778337153473 4071771660530833752865105)
                ·
                  refine ⟨3053828745398125314648829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4071771660530833752865105 3053828745398125314648829)
                  ·
                    refine ⟨1145185779524296992993311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3053828745398125314648829 1145185779524296992993311)
                    ·
                      rfl

theorem cell22_3345362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_3345362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345362 prefixEnd_3345362 := by exact prefixLift 3345362
  have htrace : WordTrace (prefixWord ++ tailWord_3345362) baseStart_3345362 baseEnd_3345362 := by
    simpa [prefixWord, tailWord_3345362, baseEnd_3345362] using wordTrace_append hprefix tailTrace_3345362
  have hstable : (prefixWord ++ tailWord_3345362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345362).length < 2 ^ (prefixWord ++ tailWord_3345362).sum := by decide
  have hdescent : baseEnd_3345362 < baseStart_3345362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345375 : List Nat := [1, 1, 2, 3, 6, 1, 1, 7]
def baseStart_3345375 : Nat := 118140960795 + 3345375 * 2 ^ 59
def prefixEnd_3345375 : Nat := 4983230072969 + 3 ^ 40 * 3345375 * 2
def baseEnd_3345375 : Nat := 127243358854441032490919

theorem tailTrace_3345375 : CollatzResearch.WordTrace tailWord_3345375 prefixEnd_3345375 127243358854441032490919 := by
  unfold tailWord_3345375
  simp only [CollatzResearch.WordTrace]
  refine ⟨122015850255285194408045579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81343900170190129605363719 122015850255285194408045579)
  ·
    refine ⟨183023775382927791612068369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122015850255285194408045579 183023775382927791612068369)
    ·
      refine ⟨137267831537195843709051277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183023775382927791612068369 137267831537195843709051277)
      ·
        refine ⟨51475436826448441390894229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137267831537195843709051277 51475436826448441390894229)
        ·
          refine ⟨2412911101239770690198167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51475436826448441390894229 2412911101239770690198167)
          ·
            refine ⟨3619366651859656035297251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412911101239770690198167 3619366651859656035297251)
            ·
              refine ⟨5429049977789484052945877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619366651859656035297251 5429049977789484052945877)
              ·
                refine ⟨127243358854441032490919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5429049977789484052945877 127243358854441032490919)
                ·
                  rfl

theorem cell22_3345375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 7].length) (baseStart_3345375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345375 prefixEnd_3345375 := by exact prefixLift 3345375
  have htrace : WordTrace (prefixWord ++ tailWord_3345375) baseStart_3345375 baseEnd_3345375 := by
    simpa [prefixWord, tailWord_3345375, baseEnd_3345375] using wordTrace_append hprefix tailTrace_3345375
  have hstable : (prefixWord ++ tailWord_3345375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345375).length < 2 ^ (prefixWord ++ tailWord_3345375).sum := by decide
  have hdescent : baseEnd_3345375 < baseStart_3345375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345394 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_3345394 : Nat := 118140960795 + 3345394 * 2 ^ 59
def prefixEnd_3345394 : Nat := 4983230072969 + 3 ^ 40 * 3345394 * 2
def baseEnd_3345394 : Nat := 1145196733778259576193213

theorem tailTrace_3345394 : CollatzResearch.WordTrace tailWord_3345394 prefixEnd_3345394 1145196733778259576193213 := by
  unfold tailWord_3345394
  simp only [CollatzResearch.WordTrace]
  refine ⟨30504135810554090163246809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81344362161477573768658157 30504135810554090163246809)
  ·
    refine ⟨22878101857915567622435107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30504135810554090163246809 22878101857915567622435107)
    ·
      refine ⟨34317152786873351433652661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22878101857915567622435107 34317152786873351433652661)
      ·
        refine ⟨3217233073769376696904937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34317152786873351433652661 3217233073769376696904937)
        ·
          refine ⟨2412924805327032522678703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3217233073769376696904937 2412924805327032522678703)
          ·
            refine ⟨3619387207990548784018055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412924805327032522678703 3619387207990548784018055)
            ·
              refine ⟨5429080811985823176027083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619387207990548784018055 5429080811985823176027083)
              ·
                refine ⟨8143621217978734764040625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5429080811985823176027083 8143621217978734764040625)
                ·
                  refine ⟨6107715913484051073030469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8143621217978734764040625 6107715913484051073030469)
                  ·
                    refine ⟨1145196733778259576193213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6107715913484051073030469 1145196733778259576193213)
                    ·
                      rfl

theorem cell22_3345394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_3345394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345394 prefixEnd_3345394 := by exact prefixLift 3345394
  have htrace : WordTrace (prefixWord ++ tailWord_3345394) baseStart_3345394 baseEnd_3345394 := by
    simpa [prefixWord, tailWord_3345394, baseEnd_3345394] using wordTrace_append hprefix tailTrace_3345394
  have hstable : (prefixWord ++ tailWord_3345394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345394).length < 2 ^ (prefixWord ++ tailWord_3345394).sum := by decide
  have hdescent : baseEnd_3345394 < baseStart_3345394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345401 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_3345401 : Nat := 118140960795 + 3345401 * 2 ^ 59
def prefixEnd_3345401 : Nat := 4983230072969 + 3 ^ 40 * 3345401 * 2
def baseEnd_3345401 : Nat := 1145199130021313891268191

theorem tailTrace_3345401 : CollatzResearch.WordTrace tailWord_3345401 prefixEnd_3345401 1145199130021313891268191 := by
  unfold tailWord_3345401
  simp only [CollatzResearch.WordTrace]
  refine ⟨122016798553191000848492057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81344532368794000565661371 122016798553191000848492057)
  ·
    refine ⟨91512598914893250636369043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122016798553191000848492057 91512598914893250636369043)
    ·
      refine ⟨137268898372339875954553565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91512598914893250636369043 137268898372339875954553565)
      ·
        refine ⟨51475836889627453482957587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137268898372339875954553565 51475836889627453482957587)
        ·
          refine ⟨77213755334441180224436381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51475836889627453482957587 77213755334441180224436381)
          ·
            refine ⟨28955158250415442584163643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77213755334441180224436381 28955158250415442584163643)
            ·
              refine ⟨43432737375623163876245465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28955158250415442584163643 43432737375623163876245465)
              ·
                refine ⟨32574553031717372907184099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43432737375623163876245465 32574553031717372907184099)
                ·
                  refine ⟨48861829547576059360776149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32574553031717372907184099 48861829547576059360776149)
                  ·
                    refine ⟨1145199130021313891268191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48861829547576059360776149 1145199130021313891268191)
                    ·
                      rfl

theorem cell22_3345401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_3345401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345401 prefixEnd_3345401 := by exact prefixLift 3345401
  have htrace : WordTrace (prefixWord ++ tailWord_3345401) baseStart_3345401 baseEnd_3345401 := by
    simpa [prefixWord, tailWord_3345401, baseEnd_3345401] using wordTrace_append hprefix tailTrace_3345401
  have hstable : (prefixWord ++ tailWord_3345401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345401).length < 2 ^ (prefixWord ++ tailWord_3345401).sum := by decide
  have hdescent : baseEnd_3345401 < baseStart_3345401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345418 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_3345418 : Nat := 118140960795 + 3345418 * 2 ^ 59
def prefixEnd_3345418 : Nat := 4983230072969 + 3 ^ 40 * 3345418 * 2
def baseEnd_3345418 : Nat := 1145204949468731513593139

theorem tailTrace_3345418 : CollatzResearch.WordTrace tailWord_3345418 prefixEnd_3345418 1145204949468731513593139 := by
  unfold tailWord_3345418
  simp only [CollatzResearch.WordTrace]
  refine ⟨30504354648532353187965227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81344945729419608501240605 30504354648532353187965227)
  ·
    refine ⟨45756531972798529781947841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30504354648532353187965227 45756531972798529781947841)
    ·
      refine ⟨34317398979598897336460881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45756531972798529781947841 34317398979598897336460881)
      ·
        refine ⟨25738049234699173002345661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34317398979598897336460881 25738049234699173002345661)
        ·
          refine ⟨9651768463012189875879623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25738049234699173002345661 9651768463012189875879623)
          ·
            refine ⟨14477652694518284813819435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9651768463012189875879623 14477652694518284813819435)
            ·
              refine ⟨21716479041777427220729153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14477652694518284813819435 21716479041777427220729153)
              ·
                refine ⟨16287359281333070415546865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21716479041777427220729153 16287359281333070415546865)
                ·
                  refine ⟨12215519460999802811660149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16287359281333070415546865 12215519460999802811660149)
                  ·
                    refine ⟨1145204949468731513593139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12215519460999802811660149 1145204949468731513593139)
                    ·
                      rfl

theorem cell22_3345418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_3345418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345418 prefixEnd_3345418 := by exact prefixLift 3345418
  have htrace : WordTrace (prefixWord ++ tailWord_3345418) baseStart_3345418 baseEnd_3345418 := by
    simpa [prefixWord, tailWord_3345418, baseEnd_3345418] using wordTrace_append hprefix tailTrace_3345418
  have hstable : (prefixWord ++ tailWord_3345418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345418).length < 2 ^ (prefixWord ++ tailWord_3345418).sum := by decide
  have hdescent : baseEnd_3345418 < baseStart_3345418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345420 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 5]
def baseStart_3345420 : Nat := 118140960795 + 3345420 * 2 ^ 59
def prefixEnd_3345420 : Nat := 4983230072969 + 3 ^ 40 * 3345420 * 2
def baseEnd_3345420 : Nat := 381735211369868058347711

theorem tailTrace_3345420 : CollatzResearch.WordTrace tailWord_3345420 prefixEnd_3345420 381735211369868058347711 := by
  unfold tailWord_3345420
  simp only [CollatzResearch.WordTrace]
  refine ⟨61008745770061083546716857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81344994360081444728955809 61008745770061083546716857)
  ·
    refine ⟨45756559327545812660037643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61008745770061083546716857 45756559327545812660037643)
    ·
      refine ⟨68634838991318718990056465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45756559327545812660037643 68634838991318718990056465)
      ·
        refine ⟨51476129243489039242542349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68634838991318718990056465 51476129243489039242542349)
        ·
          refine ⟨19303548466308389715953381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51476129243489039242542349 19303548466308389715953381)
          ·
            refine ⟨3619415337432823071741259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19303548466308389715953381 3619415337432823071741259)
            ·
              refine ⟨5429123006149234607611889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619415337432823071741259 5429123006149234607611889)
              ·
                refine ⟨4071842254611925955708917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5429123006149234607611889 4071842254611925955708917)
                ·
                  refine ⟨381735211369868058347711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4071842254611925955708917 381735211369868058347711)
                  ·
                    rfl

theorem cell22_3345420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_3345420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345420 prefixEnd_3345420 := by exact prefixLift 3345420
  have htrace : WordTrace (prefixWord ++ tailWord_3345420) baseStart_3345420 baseEnd_3345420 := by
    simpa [prefixWord, tailWord_3345420, baseEnd_3345420] using wordTrace_append hprefix tailTrace_3345420
  have hstable : (prefixWord ++ tailWord_3345420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345420).length < 2 ^ (prefixWord ++ tailWord_3345420).sum := by decide
  have hdescent : baseEnd_3345420 < baseStart_3345420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345437 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 5]
def baseStart_3345437 : Nat := 118140960795 + 3345437 * 2 ^ 59
def prefixEnd_3345437 : Nat := 4983230072969 + 3 ^ 40 * 3345437 * 2
def baseEnd_3345437 : Nat := 381737151185673932456027

theorem tailTrace_3345437 : CollatzResearch.WordTrace tailWord_3345437 prefixEnd_3345437 381737151185673932456027 := by
  unfold tailWord_3345437
  simp only [CollatzResearch.WordTrace]
  refine ⟨122018111581060578996802565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81345407720707052664535043 122018111581060578996802565)
  ·
    refine ⟨22878395921448858561900481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122018111581060578996802565 22878395921448858561900481)
    ·
      refine ⟨17158796941086643921425361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22878395921448858561900481 17158796941086643921425361)
      ·
        refine ⟨12869097705814982941069021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17158796941086643921425361 12869097705814982941069021)
        ·
          refine ⟨4825911639680618602900883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12869097705814982941069021 4825911639680618602900883)
          ·
            refine ⟨7238867459520927904351325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4825911639680618602900883 7238867459520927904351325)
            ·
              refine ⟨2714575297320347964131747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7238867459520927904351325 2714575297320347964131747)
              ·
                refine ⟨4071862945980521946197621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714575297320347964131747 4071862945980521946197621)
                ·
                  refine ⟨381737151185673932456027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4071862945980521946197621 381737151185673932456027)
                  ·
                    rfl

theorem cell22_3345437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_3345437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345437 prefixEnd_3345437 := by exact prefixLift 3345437
  have htrace : WordTrace (prefixWord ++ tailWord_3345437) baseStart_3345437 baseEnd_3345437 := by
    simpa [prefixWord, tailWord_3345437, baseEnd_3345437] using wordTrace_append hprefix tailTrace_3345437
  have hstable : (prefixWord ++ tailWord_3345437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345437).length < 2 ^ (prefixWord ++ tailWord_3345437).sum := by decide
  have hdescent : baseEnd_3345437 < baseStart_3345437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345480 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 2, 3]
def baseStart_3345480 : Nat := 118140960795 + 3345480 * 2 ^ 59
def prefixEnd_3345480 : Nat := 4983230072969 + 3 ^ 40 * 3345480 * 2
def baseEnd_3345480 : Nat := 1145226173335784018542949

theorem tailTrace_3345480 : CollatzResearch.WordTrace tailWord_3345480 prefixEnd_3345480 1145226173335784018542949 := by
  unfold tailWord_3345480
  simp only [CollatzResearch.WordTrace]
  refine ⟨61009839959952398670308947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81346453279936531560411929 61009839959952398670308947)
  ·
    refine ⟨91514759939928598005463421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61009839959952398670308947 91514759939928598005463421)
    ·
      refine ⟨34318034977473224252048783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91514759939928598005463421 34318034977473224252048783)
      ·
        refine ⟨51477052466209836378073175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34318034977473224252048783 51477052466209836378073175)
        ·
          refine ⟨77215578699314754567109763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51477052466209836378073175 77215578699314754567109763)
          ·
            refine ⟨115823368048972131850664645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77215578699314754567109763 115823368048972131850664645)
            ·
              refine ⟨21716881509182274721999621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115823368048972131850664645 21716881509182274721999621)
              ·
                refine ⟨4071915282971676510374929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21716881509182274721999621 4071915282971676510374929)
                ·
                  refine ⟨3053936462228757382781197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4071915282971676510374929 3053936462228757382781197)
                  ·
                    refine ⟨1145226173335784018542949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3053936462228757382781197 1145226173335784018542949)
                    ·
                      rfl

theorem cell22_3345480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_3345480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345480 prefixEnd_3345480 := by exact prefixLift 3345480
  have htrace : WordTrace (prefixWord ++ tailWord_3345480) baseStart_3345480 baseEnd_3345480 := by
    simpa [prefixWord, tailWord_3345480, baseEnd_3345480] using wordTrace_append hprefix tailTrace_3345480
  have hstable : (prefixWord ++ tailWord_3345480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345480).length < 2 ^ (prefixWord ++ tailWord_3345480).sum := by decide
  have hdescent : baseEnd_3345480 < baseStart_3345480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345493 : List Nat := [1, 3, 2, 2, 1, 2, 4, 7]
def baseStart_3345493 : Nat := 118140960795 + 3345493 * 2 ^ 59
def prefixEnd_3345493 : Nat := 4983230072969 + 3 ^ 40 * 3345493 * 2
def baseEnd_3345493 : Nat := 127247847055717368663101

theorem tailTrace_3345493 : CollatzResearch.WordTrace tailWord_3345493 prefixEnd_3345493 127247847055717368663101 := by
  unfold tailWord_3345493
  simp only [CollatzResearch.WordTrace]
  refine ⟨122020154068857700560841133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81346769379238467040560755 122020154068857700560841133)
  ·
    refine ⟨45757557775821637710315425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122020154068857700560841133 45757557775821637710315425)
    ·
      refine ⟨34318168331866228282736569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45757557775821637710315425 34318168331866228282736569)
      ·
        refine ⟨25738626248899671212052427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34318168331866228282736569 25738626248899671212052427)
        ·
          refine ⟨38607939373349506818078641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25738626248899671212052427 38607939373349506818078641)
          ·
            refine ⟨28955954530012130113558981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38607939373349506818078641 28955954530012130113558981)
            ·
              refine ⟨5429241474377274396292309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28955954530012130113558981 5429241474377274396292309)
              ·
                refine ⟨127247847055717368663101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5429241474377274396292309 127247847055717368663101)
                ·
                  rfl

theorem cell22_3345493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 7].length) (baseStart_3345493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345493 prefixEnd_3345493 := by exact prefixLift 3345493
  have htrace : WordTrace (prefixWord ++ tailWord_3345493) baseStart_3345493 baseEnd_3345493 := by
    simpa [prefixWord, tailWord_3345493, baseEnd_3345493] using wordTrace_append hprefix tailTrace_3345493
  have hstable : (prefixWord ++ tailWord_3345493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345493).length < 2 ^ (prefixWord ++ tailWord_3345493).sum := by decide
  have hdescent : baseEnd_3345493 < baseStart_3345493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345501 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3345501 : Nat := 118140960795 + 3345501 * 2 ^ 59
def prefixEnd_3345501 : Nat := 4983230072969 + 3 ^ 40 * 3345501 * 2
def baseEnd_3345501 : Nat := 1145233362064946963767885

theorem tailTrace_3345501 : CollatzResearch.WordTrace tailWord_3345501 prefixEnd_3345501 1145233362064946963767885 := by
  unfold tailWord_3345501
  simp only [CollatzResearch.WordTrace]
  refine ⟨122020445852828717927132357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81346963901885811951421571 122020445852828717927132357)
  ·
    refine ⟨22878833597405384611337317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122020445852828717927132357 22878833597405384611337317)
    ·
      refine ⟨4289781299513509614625747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22878833597405384611337317 4289781299513509614625747)
      ·
        refine ⟨6434671949270264421938621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4289781299513509614625747 6434671949270264421938621)
        ·
          refine ⟨2413001980976349158226983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6434671949270264421938621 2413001980976349158226983)
          ·
            refine ⟨3619502971464523737340475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413001980976349158226983 3619502971464523737340475)
            ·
              refine ⟨5429254457196785606010713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619502971464523737340475 5429254457196785606010713)
              ·
                refine ⟨4071940842897589204508035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5429254457196785606010713 4071940842897589204508035)
                ·
                  refine ⟨6107911264346383806762053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071940842897589204508035 6107911264346383806762053)
                  ·
                    refine ⟨1145233362064946963767885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6107911264346383806762053 1145233362064946963767885)
                    ·
                      rfl

theorem cell22_3345501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3345501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345501 prefixEnd_3345501 := by exact prefixLift 3345501
  have htrace : WordTrace (prefixWord ++ tailWord_3345501) baseStart_3345501 baseEnd_3345501 := by
    simpa [prefixWord, tailWord_3345501, baseEnd_3345501] using wordTrace_append hprefix tailTrace_3345501
  have hstable : (prefixWord ++ tailWord_3345501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345501).length < 2 ^ (prefixWord ++ tailWord_3345501).sum := by decide
  have hdescent : baseEnd_3345501 < baseStart_3345501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345645 : List Nat := [1, 5, 1, 2, 2, 1, 10]
def baseStart_3345645 : Nat := 118140960795 + 3345645 * 2 ^ 59
def prefixEnd_3345645 : Nat := 4983230072969 + 3 ^ 40 * 3345645 * 2
def baseEnd_3345645 : Nat := 42417876155843651413609

theorem tailTrace_3345645 : CollatzResearch.WordTrace tailWord_3345645 prefixEnd_3345645 42417876155843651413609 := by
  unfold tailWord_3345645
  simp only [CollatzResearch.WordTrace]
  refine ⟨122025697964307030520374389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81350465309538020346916259 122025697964307030520374389)
  ·
    refine ⟨11439909184153784111285099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122025697964307030520374389 11439909184153784111285099)
    ·
      refine ⟨17159863776230676166927649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11439909184153784111285099 17159863776230676166927649)
      ·
        refine ⟨12869897832173007125195737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17159863776230676166927649 12869897832173007125195737)
        ·
          refine ⟨9652423374129755343896803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12869897832173007125195737 9652423374129755343896803)
          ·
            refine ⟨14478635061194633015845205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9652423374129755343896803 14478635061194633015845205)
            ·
              refine ⟨42417876155843651413609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14478635061194633015845205 42417876155843651413609)
              ·
                rfl

theorem cell22_3345645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 10].length) (baseStart_3345645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345645 prefixEnd_3345645 := by exact prefixLift 3345645
  have htrace : WordTrace (prefixWord ++ tailWord_3345645) baseStart_3345645 baseEnd_3345645 := by
    simpa [prefixWord, tailWord_3345645, baseEnd_3345645] using wordTrace_append hprefix tailTrace_3345645
  have hstable : (prefixWord ++ tailWord_3345645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345645).length < 2 ^ (prefixWord ++ tailWord_3345645).sum := by decide
  have hdescent : baseEnd_3345645 < baseStart_3345645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345647 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 2, 4]
def baseStart_3345647 : Nat := 118140960795 + 3345647 * 2 ^ 59
def prefixEnd_3345647 : Nat := 4983230072969 + 3 ^ 40 * 3345647 * 2
def baseEnd_3345647 : Nat := 1145283340848651249617437

theorem tailTrace_3345647 : CollatzResearch.WordTrace tailWord_3345647 prefixEnd_3345647 1145283340848651249617437 := by
  unfold tailWord_3345647
  simp only [CollatzResearch.WordTrace]
  refine ⟨122025770910299784861947195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81350513940199856574631463 122025770910299784861947195)
  ·
    refine ⟨183038656365449677292920793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122025770910299784861947195 183038656365449677292920793)
    ·
      refine ⟨137278992274087257969690595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183038656365449677292920793 137278992274087257969690595)
      ·
        refine ⟨205918488411130886954535893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137278992274087257969690595 205918488411130886954535893)
        ·
          refine ⟨4826214572135880162996935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 205918488411130886954535893 4826214572135880162996935)
          ·
            refine ⟨7239321858203820244495403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826214572135880162996935 7239321858203820244495403)
            ·
              refine ⟨10858982787305730366743105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7239321858203820244495403 10858982787305730366743105)
              ·
                refine ⟨8144237090479297775057329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10858982787305730366743105 8144237090479297775057329)
                ·
                  refine ⟨6108177817859473331292997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8144237090479297775057329 6108177817859473331292997)
                  ·
                    refine ⟨1145283340848651249617437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6108177817859473331292997 1145283340848651249617437)
                    ·
                      rfl

theorem cell22_3345647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_3345647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345647 prefixEnd_3345647 := by exact prefixLift 3345647
  have htrace : WordTrace (prefixWord ++ tailWord_3345647) baseStart_3345647 baseEnd_3345647 := by
    simpa [prefixWord, tailWord_3345647, baseEnd_3345647] using wordTrace_append hprefix tailTrace_3345647
  have hstable : (prefixWord ++ tailWord_3345647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345647).length < 2 ^ (prefixWord ++ tailWord_3345647).sum := by decide
  have hdescent : baseEnd_3345647 < baseStart_3345647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345662 : List Nat := [4, 2, 2, 1, 1, 3, 2, 7]
def baseStart_3345662 : Nat := 118140960795 + 3345662 * 2 ^ 59
def prefixEnd_3345662 : Nat := 4983230072969 + 3 ^ 40 * 3345662 * 2
def baseEnd_3345662 : Nat := 127254275072799578943599

theorem tailTrace_3345662 : CollatzResearch.WordTrace tailWord_3345662 prefixEnd_3345662 127254275072799578943599 := by
  unfold tailWord_3345662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15253289750655680302967905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81350878670163628282495493 15253289750655680302967905)
  ·
    refine ⟨11439967312991760227225929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15253289750655680302967905 11439967312991760227225929)
    ·
      refine ⟨8579975484743820170419447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11439967312991760227225929 8579975484743820170419447)
      ·
        refine ⟨12869963227115730255629171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8579975484743820170419447 12869963227115730255629171)
        ·
          refine ⟨19304944840673595383443757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12869963227115730255629171 19304944840673595383443757)
          ·
            refine ⟨7239354315252598268791409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19304944840673595383443757 7239354315252598268791409)
            ·
              refine ⟨5429515736439448701593557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7239354315252598268791409 5429515736439448701593557)
              ·
                refine ⟨127254275072799578943599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5429515736439448701593557 127254275072799578943599)
                ·
                  rfl

theorem cell22_3345662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_3345662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345662 prefixEnd_3345662 := by exact prefixLift 3345662
  have htrace : WordTrace (prefixWord ++ tailWord_3345662) baseStart_3345662 baseEnd_3345662 := by
    simpa [prefixWord, tailWord_3345662, baseEnd_3345662] using wordTrace_append hprefix tailTrace_3345662
  have hstable : (prefixWord ++ tailWord_3345662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345662).length < 2 ^ (prefixWord ++ tailWord_3345662).sum := by decide
  have hdescent : baseEnd_3345662 < baseStart_3345662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345666 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_3345666 : Nat := 118140960795 + 3345666 * 2 ^ 59
def prefixEnd_3345666 : Nat := 4983230072969 + 3 ^ 40 * 3345666 * 2
def baseEnd_3345666 : Nat := 1145289844936941533392379

theorem tailTrace_3345666 : CollatzResearch.WordTrace tailWord_3345666 prefixEnd_3345666 1145289844936941533392379 := by
  unfold tailWord_3345666
  simp only [CollatzResearch.WordTrace]
  refine ⟨30506615974307737776722213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81350975931487300737925901 30506615974307737776722213)
  ·
    refine ⟨5719990495182700833135415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30506615974307737776722213 5719990495182700833135415)
    ·
      refine ⟨8579985742774051249703123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719990495182700833135415 8579985742774051249703123)
      ·
        refine ⟨12869978614161076874554685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8579985742774051249703123 12869978614161076874554685)
        ·
          refine ⟨4826241980310403827958007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12869978614161076874554685 4826241980310403827958007)
          ·
            refine ⟨7239362970465605741937011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826241980310403827958007 7239362970465605741937011)
            ·
              refine ⟨10859044455698408612905517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7239362970465605741937011 10859044455698408612905517)
              ·
                refine ⟨4072141670886903229839569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10859044455698408612905517 4072141670886903229839569)
                ·
                  refine ⟨3054106253165177422379677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4072141670886903229839569 3054106253165177422379677)
                  ·
                    refine ⟨1145289844936941533392379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3054106253165177422379677 1145289844936941533392379)
                    ·
                      rfl

theorem cell22_3345666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_3345666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345666 prefixEnd_3345666 := by exact prefixLift 3345666
  have htrace : WordTrace (prefixWord ++ tailWord_3345666) baseStart_3345666 baseEnd_3345666 := by
    simpa [prefixWord, tailWord_3345666, baseEnd_3345666] using wordTrace_append hprefix tailTrace_3345666
  have hstable : (prefixWord ++ tailWord_3345666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345666).length < 2 ^ (prefixWord ++ tailWord_3345666).sum := by decide
  have hdescent : baseEnd_3345666 < baseStart_3345666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345735 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 8]
def baseStart_3345735 : Nat := 118140960795 + 3345735 * 2 ^ 59
def prefixEnd_3345735 : Nat := 4983230072969 + 3 ^ 40 * 3345735 * 2
def baseEnd_3345735 : Nat := 381771155015682784472389

theorem tailTrace_3345735 : CollatzResearch.WordTrace tailWord_3345735 prefixEnd_3345735 381771155015682784472389 := by
  unfold tailWord_3345735
  simp only [CollatzResearch.WordTrace]
  refine ⟨122028980533980975891150659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81352653689320650594100439 122028980533980975891150659)
  ·
    refine ⟨183043470800971463836725989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122028980533980975891150659 183043470800971463836725989)
    ·
      refine ⟨34320650775182149469386123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183043470800971463836725989 34320650775182149469386123)
      ·
        refine ⟨51480976162773224204079185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34320650775182149469386123 51480976162773224204079185)
        ·
          refine ⟨38610732122079918153059389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51480976162773224204079185 38610732122079918153059389)
          ·
            refine ⟨14479024545779969307397271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38610732122079918153059389 14479024545779969307397271)
            ·
              refine ⟨21718536818669953961095907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14479024545779969307397271 21718536818669953961095907)
              ·
                refine ⟨32577805228004930941643861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21718536818669953961095907 32577805228004930941643861)
                ·
                  refine ⟨381771155015682784472389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32577805228004930941643861 381771155015682784472389)
                  ·
                    rfl

theorem cell22_3345735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 8].length) (baseStart_3345735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345735 prefixEnd_3345735 := by exact prefixLift 3345735
  have htrace : WordTrace (prefixWord ++ tailWord_3345735) baseStart_3345735 baseEnd_3345735 := by
    simpa [prefixWord, tailWord_3345735, baseEnd_3345735] using wordTrace_append hprefix tailTrace_3345735
  have hstable : (prefixWord ++ tailWord_3345735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345735).length < 2 ^ (prefixWord ++ tailWord_3345735).sum := by decide
  have hdescent : baseEnd_3345735 < baseStart_3345735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345754 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 1, 4]
def baseStart_3345754 : Nat := 118140960795 + 3345754 * 2 ^ 59
def prefixEnd_3345754 : Nat := 4983230072969 + 3 ^ 40 * 3345754 * 2
def baseEnd_3345754 : Nat := 1145319969135338637192109

theorem tailTrace_3345754 : CollatzResearch.WordTrace tailWord_3345754 prefixEnd_3345754 1145319969135338637192109 := by
  unfold tailWord_3345754
  simp only [CollatzResearch.WordTrace]
  refine ⟨30507418380228035534023079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81353115680608094757394877 30507418380228035534023079)
  ·
    refine ⟨45761127570342053301034619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30507418380228035534023079 45761127570342053301034619)
    ·
      refine ⟨68641691355513079951551929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45761127570342053301034619 68641691355513079951551929)
      ·
        refine ⟨51481268516634809963663947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68641691355513079951551929 51481268516634809963663947)
        ·
          refine ⟨77221902774952214945495921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51481268516634809963663947 77221902774952214945495921)
          ·
            refine ⟨57916427081214161209121941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77221902774952214945495921 57916427081214161209121941)
            ·
              refine ⟨2714832519431913806677591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57916427081214161209121941 2714832519431913806677591)
              ·
                refine ⟨4072248779147870710016387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714832519431913806677591 4072248779147870710016387)
                ·
                  refine ⟨6108373168721806065024581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4072248779147870710016387 6108373168721806065024581)
                  ·
                    refine ⟨1145319969135338637192109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6108373168721806065024581 1145319969135338637192109)
                    ·
                      rfl

theorem cell22_3345754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_3345754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345754 prefixEnd_3345754 := by exact prefixLift 3345754
  have htrace : WordTrace (prefixWord ++ tailWord_3345754) baseStart_3345754 baseEnd_3345754 := by
    simpa [prefixWord, tailWord_3345754, baseEnd_3345754] using wordTrace_append hprefix tailTrace_3345754
  have hstable : (prefixWord ++ tailWord_3345754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345754).length < 2 ^ (prefixWord ++ tailWord_3345754).sum := by decide
  have hdescent : baseEnd_3345754 < baseStart_3345754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345797 : List Nat := [1, 3, 1, 1, 3, 1, 6, 6]
def baseStart_3345797 : Nat := 118140960795 + 3345797 * 2 ^ 59
def prefixEnd_3345797 : Nat := 4983230072969 + 3 ^ 40 * 3345797 * 2
def baseEnd_3345797 : Nat := 127259409879344539818553

theorem tailTrace_3345797 : CollatzResearch.WordTrace tailWord_3345797 prefixEnd_3345797 127259409879344539818553 := by
  unfold tailWord_3345797
  simp only [CollatzResearch.WordTrace]
  refine ⟨122031241859756360479907645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81354161239837573653271763 122031241859756360479907645)
  ·
    refine ⟨45761715697408635179965367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122031241859756360479907645 45761715697408635179965367)
    ·
      refine ⟨68642573546112952769948051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45761715697408635179965367 68642573546112952769948051)
      ·
        refine ⟨102963860319169429154922077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68642573546112952769948051 102963860319169429154922077)
        ·
          refine ⟨38611447619688535933095779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102963860319169429154922077 38611447619688535933095779)
          ·
            refine ⟨57917171429532803899643669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38611447619688535933095779 57917171429532803899643669)
            ·
              refine ⟨2714867410759350182795797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57917171429532803899643669 2714867410759350182795797)
              ·
                refine ⟨127259409879344539818553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2714867410759350182795797 127259409879344539818553)
                ·
                  rfl

theorem cell22_3345797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 6].length) (baseStart_3345797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345797 prefixEnd_3345797 := by exact prefixLift 3345797
  have htrace : WordTrace (prefixWord ++ tailWord_3345797) baseStart_3345797 baseEnd_3345797 := by
    simpa [prefixWord, tailWord_3345797, baseEnd_3345797] using wordTrace_append hprefix tailTrace_3345797
  have hstable : (prefixWord ++ tailWord_3345797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345797).length < 2 ^ (prefixWord ++ tailWord_3345797).sum := by decide
  have hdescent : baseEnd_3345797 < baseStart_3345797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345876 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 5]
def baseStart_3345876 : Nat := 118140960795 + 3345876 * 2 ^ 59
def prefixEnd_3345876 : Nat := 4983230072969 + 3 ^ 40 * 3345876 * 2
def baseEnd_3345876 : Nat := 381787244076190328547245

theorem tailTrace_3345876 : CollatzResearch.WordTrace tailWord_3345876 prefixEnd_3345876 381787244076190328547245 := by
  unfold tailWord_3345876
  simp only [CollatzResearch.WordTrace]
  refine ⟨61017061613235078486016741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81356082150980104648022321 61017061613235078486016741)
  ·
    refine ⟨11440699052481577216128139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61017061613235078486016741 11440699052481577216128139)
    ·
      refine ⟨17161048578722365824192209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11440699052481577216128139 17161048578722365824192209)
      ·
        refine ⟨12870786434041774368144157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17161048578722365824192209 12870786434041774368144157)
        ·
          refine ⟨4826544912765665388054059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12870786434041774368144157 4826544912765665388054059)
          ·
            refine ⟨7239817369148498082081089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826544912765665388054059 7239817369148498082081089)
            ·
              refine ⟨5429863026861373561560817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7239817369148498082081089 5429863026861373561560817)
              ·
                refine ⟨4072397270146030171170613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5429863026861373561560817 4072397270146030171170613)
                ·
                  refine ⟨381787244076190328547245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4072397270146030171170613 381787244076190328547245)
                  ·
                    rfl

theorem cell22_3345876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_3345876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345876 prefixEnd_3345876 := by exact prefixLift 3345876
  have htrace : WordTrace (prefixWord ++ tailWord_3345876) baseStart_3345876 baseEnd_3345876 := by
    simpa [prefixWord, tailWord_3345876, baseEnd_3345876] using wordTrace_append hprefix tailTrace_3345876
  have hstable : (prefixWord ++ tailWord_3345876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345876).length < 2 ^ (prefixWord ++ tailWord_3345876).sum := by decide
  have hdescent : baseEnd_3345876 < baseStart_3345876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345887 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 6]
def baseStart_3345887 : Nat := 118140960795 + 3345887 * 2 ^ 59
def prefixEnd_3345887 : Nat := 4983230072969 + 3 ^ 40 * 3345887 * 2
def baseEnd_3345887 : Nat := 381788499251123541205567

theorem tailTrace_3345887 : CollatzResearch.WordTrace tailWord_3345887 prefixEnd_3345887 381788499251123541205567 := by
  unfold tailWord_3345887
  simp only [CollatzResearch.WordTrace]
  refine ⟨122034524429430305850683915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81356349619620203900455943 122034524429430305850683915)
  ·
    refine ⟨183051786644145458776025873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122034524429430305850683915 183051786644145458776025873)
    ·
      refine ⟨137288839983109094082019405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183051786644145458776025873 137288839983109094082019405)
      ·
        refine ⟨51483314993665910280757277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137288839983109094082019405 51483314993665910280757277)
        ·
          refine ⟨19306243122624716355283979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51483314993665910280757277 19306243122624716355283979)
          ·
            refine ⟨28959364683937074532925969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19306243122624716355283979 28959364683937074532925969)
            ·
              refine ⟨21719523512952805899694477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28959364683937074532925969 21719523512952805899694477)
              ·
                refine ⟨8144821317357302212385429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21719523512952805899694477 8144821317357302212385429)
                ·
                  refine ⟨381788499251123541205567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8144821317357302212385429 381788499251123541205567)
                  ·
                    rfl

theorem cell22_3345887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 6].length) (baseStart_3345887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345887 prefixEnd_3345887 := by exact prefixLift 3345887
  have htrace : WordTrace (prefixWord ++ tailWord_3345887) baseStart_3345887 baseEnd_3345887 := by
    simpa [prefixWord, tailWord_3345887, baseEnd_3345887] using wordTrace_append hprefix tailTrace_3345887
  have hstable : (prefixWord ++ tailWord_3345887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345887).length < 2 ^ (prefixWord ++ tailWord_3345887).sum := by decide
  have hdescent : baseEnd_3345887 < baseStart_3345887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345953 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 2, 3]
def baseStart_3345953 : Nat := 118140960795 + 3345953 * 2 ^ 59
def prefixEnd_3345953 : Nat := 4983230072969 + 3 ^ 40 * 3345953 * 2
def baseEnd_3345953 : Nat := 1145388090902168451466499

theorem tailTrace_3345953 : CollatzResearch.WordTrace tailWord_3345953 prefixEnd_3345953 1145388090902168451466499 := by
  unfold tailWord_3345953
  simp only [CollatzResearch.WordTrace]
  refine ⟨122036931647191199122586513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81357954431460799415057675 122036931647191199122586513)
  ·
    refine ⟨91527698735393399341939885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122036931647191199122586513 91527698735393399341939885)
    ·
      refine ⟨34322887025772524753227457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91527698735393399341939885 34322887025772524753227457)
      ·
        refine ⟨25742165269329393564920593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34322887025772524753227457 25742165269329393564920593)
        ·
          refine ⟨19306623951997045173690445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25742165269329393564920593 19306623951997045173690445)
          ·
            refine ⟨7239983981998891940133917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19306623951997045173690445 7239983981998891940133917)
            ·
              refine ⟨2714993993249584477550219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7239983981998891940133917 2714993993249584477550219)
              ·
                refine ⟨4072490989874376716325329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714993993249584477550219 4072490989874376716325329)
                ·
                  refine ⟨3054368242405782537243997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4072490989874376716325329 3054368242405782537243997)
                  ·
                    refine ⟨1145388090902168451466499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3054368242405782537243997 1145388090902168451466499)
                    ·
                      rfl

theorem cell22_3345953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_3345953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345953 prefixEnd_3345953 := by exact prefixLift 3345953
  have htrace : WordTrace (prefixWord ++ tailWord_3345953) baseStart_3345953 baseEnd_3345953 := by
    simpa [prefixWord, tailWord_3345953, baseEnd_3345953] using wordTrace_append hprefix tailTrace_3345953
  have hstable : (prefixWord ++ tailWord_3345953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345953).length < 2 ^ (prefixWord ++ tailWord_3345953).sum := by decide
  have hdescent : baseEnd_3345953 < baseStart_3345953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345966 : List Nat := [4, 1, 3, 1, 2, 1, 4, 6]
def baseStart_3345966 : Nat := 118140960795 + 3345966 * 2 ^ 59
def prefixEnd_3345966 : Nat := 4983230072969 + 3 ^ 40 * 3345966 * 2
def baseEnd_3345966 : Nat := 127265837896426750099051

theorem tailTrace_3345966 : CollatzResearch.WordTrace tailWord_3345966 prefixEnd_3345966 127265837896426750099051 := by
  unfold tailWord_3345966
  simp only [CollatzResearch.WordTrace]
  refine ⟨15254675724518012792851219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81358270530762734895206501 15254675724518012792851219)
  ·
    refine ⟨22882013586777019189276829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15254675724518012792851219 22882013586777019189276829)
    ·
      refine ⟨8580755095041382195978811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22882013586777019189276829 8580755095041382195978811)
      ·
        refine ⟨12871132642562073293968217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8580755095041382195978811 12871132642562073293968217)
        ·
          refine ⟨9653349481921554970476163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12871132642562073293968217 9653349481921554970476163)
          ·
            refine ⟨14480024222882332455714245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9653349481921554970476163 14480024222882332455714245)
            ·
              refine ⟨2715004541790437335446421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14480024222882332455714245 2715004541790437335446421)
              ·
                refine ⟨127265837896426750099051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2715004541790437335446421 127265837896426750099051)
                ·
                  rfl

theorem cell22_3345966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_3345966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345966 prefixEnd_3345966 := by exact prefixLift 3345966
  have htrace : WordTrace (prefixWord ++ tailWord_3345966) baseStart_3345966 baseEnd_3345966 := by
    simpa [prefixWord, tailWord_3345966, baseEnd_3345966] using wordTrace_append hprefix tailTrace_3345966
  have hstable : (prefixWord ++ tailWord_3345966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345966).length < 2 ^ (prefixWord ++ tailWord_3345966).sum := by decide
  have hdescent : baseEnd_3345966 < baseStart_3345966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3345994 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_3345994 : Nat := 118140960795 + 3345994 * 2 ^ 59
def prefixEnd_3345994 : Nat := 4983230072969 + 3 ^ 40 * 3345994 * 2
def baseEnd_3345994 : Nat := 381800708680019337063791

theorem tailTrace_3345994 : CollatzResearch.WordTrace tailWord_3345994 prefixEnd_3345994 381800708680019337063791 := by
  unfold tailWord_3345994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30509606760010665781207259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81358951360028442083219357 30509606760010665781207259)
  ·
    refine ⟨45764410140015998671810889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30509606760010665781207259 45764410140015998671810889)
    ·
      refine ⟨34323307605011999003858167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45764410140015998671810889 34323307605011999003858167)
      ·
        refine ⟨51484961407517998505787251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34323307605011999003858167 51484961407517998505787251)
        ·
          refine ⟨77227442111276997758680877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51484961407517998505787251 77227442111276997758680877)
          ·
            refine ⟨28960290791728874159505329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77227442111276997758680877 28960290791728874159505329)
            ·
              refine ⟨21720218093796655619628997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28960290791728874159505329 21720218093796655619628997)
              ·
                refine ⟨4072540892586872928680437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21720218093796655619628997 4072540892586872928680437)
                ·
                  refine ⟨381800708680019337063791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4072540892586872928680437 381800708680019337063791)
                  ·
                    rfl

theorem cell22_3345994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_3345994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3345994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3345994 prefixEnd_3345994 := by exact prefixLift 3345994
  have htrace : WordTrace (prefixWord ++ tailWord_3345994) baseStart_3345994 baseEnd_3345994 := by
    simpa [prefixWord, tailWord_3345994, baseEnd_3345994] using wordTrace_append hprefix tailTrace_3345994
  have hstable : (prefixWord ++ tailWord_3345994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3345994).length < 2 ^ (prefixWord ++ tailWord_3345994).sum := by decide
  have hdescent : baseEnd_3345994 < baseStart_3345994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3345994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346069 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3346069 : Nat := 118140960795 + 3346069 * 2 ^ 59
def prefixEnd_3346069 : Nat := 4983230072969 + 3 ^ 40 * 3346069 * 2
def baseEnd_3346069 : Nat := 1145427800072782815566143

theorem tailTrace_3346069 : CollatzResearch.WordTrace tailWord_3346069 prefixEnd_3346069 1145427800072782815566143 := by
  unfold tailWord_3346069
  simp only [CollatzResearch.WordTrace]
  refine ⟨122041162514770950933809261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81360775009847300622539507 122041162514770950933809261)
  ·
    refine ⟨45765435943039106600178473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122041162514770950933809261 45765435943039106600178473)
    ·
      refine ⟨34324076957279329950133855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45765435943039106600178473 34324076957279329950133855)
      ·
        refine ⟨51486115435918994925200783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34324076957279329950133855 51486115435918994925200783)
        ·
          refine ⟨77229173153878492387801175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51486115435918994925200783 77229173153878492387801175)
          ·
            refine ⟨115843759730817738581701763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77229173153878492387801175 115843759730817738581701763)
            ·
              refine ⟨173765639596226607872552645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115843759730817738581701763 173765639596226607872552645)
              ·
                refine ⟨32581057424292488976103621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173765639596226607872552645 32581057424292488976103621)
                ·
                  refine ⟨6108948267054841683019429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32581057424292488976103621 6108948267054841683019429)
                  ·
                    refine ⟨1145427800072782815566143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6108948267054841683019429 1145427800072782815566143)
                    ·
                      rfl

theorem cell22_3346069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3346069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346069 prefixEnd_3346069 := by exact prefixLift 3346069
  have htrace : WordTrace (prefixWord ++ tailWord_3346069) baseStart_3346069 baseEnd_3346069 := by
    simpa [prefixWord, tailWord_3346069, baseEnd_3346069] using wordTrace_append hprefix tailTrace_3346069
  have hstable : (prefixWord ++ tailWord_3346069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346069).length < 2 ^ (prefixWord ++ tailWord_3346069).sum := by decide
  have hdescent : baseEnd_3346069 < baseStart_3346069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346071 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 1, 5]
def baseStart_3346071 : Nat := 118140960795 + 3346071 * 2 ^ 59
def prefixEnd_3346071 : Nat := 4983230072969 + 3 ^ 40 * 3346071 * 2
def baseEnd_3346071 : Nat := 1145428484713655477016137

theorem tailTrace_3346071 : CollatzResearch.WordTrace tailWord_3346071 prefixEnd_3346071 1145428484713655477016137 := by
  unfold tailWord_3346071
  simp only [CollatzResearch.WordTrace]
  refine ⟨122041235460763705275382067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81360823640509136850254711 122041235460763705275382067)
  ·
    refine ⟨183061853191145557913073101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122041235460763705275382067 183061853191145557913073101)
    ·
      refine ⟨68648194946679584217402413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183061853191145557913073101 68648194946679584217402413)
      ·
        refine ⟨25743073105004844081525905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68648194946679584217402413 25743073105004844081525905)
        ·
          refine ⟨19307304828753633061144429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25743073105004844081525905 19307304828753633061144429)
          ·
            refine ⟨7240239310782612397929161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19307304828753633061144429 7240239310782612397929161)
            ·
              refine ⟨5430179483086959298446871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7240239310782612397929161 5430179483086959298446871)
              ·
                refine ⟨8145269224630438947670307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430179483086959298446871 8145269224630438947670307)
                ·
                  refine ⟨12217903836945658421505461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8145269224630438947670307 12217903836945658421505461)
                  ·
                    refine ⟨1145428484713655477016137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12217903836945658421505461 1145428484713655477016137)
                    ·
                      rfl

theorem cell22_3346071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_3346071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346071 prefixEnd_3346071 := by exact prefixLift 3346071
  have htrace : WordTrace (prefixWord ++ tailWord_3346071) baseStart_3346071 baseEnd_3346071 := by
    simpa [prefixWord, tailWord_3346071, baseEnd_3346071] using wordTrace_append hprefix tailTrace_3346071
  have hstable : (prefixWord ++ tailWord_3346071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346071).length < 2 ^ (prefixWord ++ tailWord_3346071).sum := by decide
  have hdescent : baseEnd_3346071 < baseStart_3346071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346101 : List Nat := [1, 3, 3, 3, 2, 1, 9]
def baseStart_3346101 : Nat := 118140960795 + 3346101 * 2 ^ 59
def prefixEnd_3346101 : Nat := 4983230072969 + 3 ^ 40 * 3346101 * 2
def baseEnd_3346101 : Nat := 42423657567657236991335

theorem tailTrace_3346101 : CollatzResearch.WordTrace tailWord_3346101 prefixEnd_3346101 42423657567657236991335 := by
  unfold tailWord_3346101
  simp only [CollatzResearch.WordTrace]
  refine ⟨122042329650655020398974157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81361553100436680265982771 122042329650655020398974157)
  ·
    refine ⟨45765873618995632649615309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122042329650655020398974157 45765873618995632649615309)
    ·
      refine ⟨17162202607123362243605741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45765873618995632649615309 17162202607123362243605741)
      ·
        refine ⟨6435825977671260841352153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17162202607123362243605741 6435825977671260841352153)
        ·
          refine ⟨4826869483253445631014115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6435825977671260841352153 4826869483253445631014115)
          ·
            refine ⟨7240304224880168446521173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826869483253445631014115 7240304224880168446521173)
            ·
              refine ⟨42423657567657236991335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7240304224880168446521173 42423657567657236991335)
              ·
                rfl

theorem cell22_3346101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 9].length) (baseStart_3346101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346101 prefixEnd_3346101 := by exact prefixLift 3346101
  have htrace : WordTrace (prefixWord ++ tailWord_3346101) baseStart_3346101 baseEnd_3346101 := by
    simpa [prefixWord, tailWord_3346101, baseEnd_3346101] using wordTrace_append hprefix tailTrace_3346101
  have hstable : (prefixWord ++ tailWord_3346101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346101).length < 2 ^ (prefixWord ++ tailWord_3346101).sum := by decide
  have hdescent : baseEnd_3346101 < baseStart_3346101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346144 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_3346144 : Nat := 118140960795 + 3346144 * 2 ^ 59
def prefixEnd_3346144 : Nat := 4983230072969 + 3 ^ 40 * 3346144 * 2
def baseEnd_3346144 : Nat := 1145453474105507619940913

theorem tailTrace_3346144 : CollatzResearch.WordTrace tailWord_3346144 prefixEnd_3346144 1145453474105507619940913 := by
  unfold tailWord_3346144
  simp only [CollatzResearch.WordTrace]
  refine ⟨61021948994749619371394743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81362598659666159161859657 61021948994749619371394743)
  ·
    refine ⟨91532923492124429057092115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61021948994749619371394743 91532923492124429057092115)
    ·
      refine ⟨137299385238186643585638173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91532923492124429057092115 137299385238186643585638173)
      ·
        refine ⟨51487269464319991344614315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137299385238186643585638173 51487269464319991344614315)
        ·
          refine ⟨77230904196479987016921473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51487269464319991344614315 77230904196479987016921473)
          ·
            refine ⟨57923178147359990262691105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77230904196479987016921473 57923178147359990262691105)
            ·
              refine ⟨43442383610519992697018329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57923178147359990262691105 43442383610519992697018329)
              ·
                refine ⟨32581787707889994522763747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43442383610519992697018329 32581787707889994522763747)
                ·
                  refine ⟨48872681561834991784145621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32581787707889994522763747 48872681561834991784145621)
                  ·
                    refine ⟨1145453474105507619940913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48872681561834991784145621 1145453474105507619940913)
                    ·
                      rfl

theorem cell22_3346144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_3346144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346144 prefixEnd_3346144 := by exact prefixLift 3346144
  have htrace : WordTrace (prefixWord ++ tailWord_3346144) baseStart_3346144 baseEnd_3346144 := by
    simpa [prefixWord, tailWord_3346144, baseEnd_3346144] using wordTrace_append hprefix tailTrace_3346144
  have hstable : (prefixWord ++ tailWord_3346144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346144).length < 2 ^ (prefixWord ++ tailWord_3346144).sum := by decide
  have hdescent : baseEnd_3346144 < baseStart_3346144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346180 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 5]
def baseStart_3346180 : Nat := 118140960795 + 3346180 * 2 ^ 59
def prefixEnd_3346180 : Nat := 4983230072969 + 3 ^ 40 * 3346180 * 2
def baseEnd_3346180 : Nat := 381821932547071842013601

theorem tailTrace_3346180 : CollatzResearch.WordTrace tailWord_3346180 prefixEnd_3346180 381821932547071842013601 := by
  unfold tailWord_3346180
  simp only [CollatzResearch.WordTrace]
  refine ⟨61022605508684408445549997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81363474011579211260733329 61022605508684408445549997)
  ·
    refine ⟨22883477065756653167081249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61022605508684408445549997 22883477065756653167081249)
    ·
      refine ⟨17162607799317489875310937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22883477065756653167081249 17162607799317489875310937)
      ·
        refine ⟨12871955849488117406483203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17162607799317489875310937 12871955849488117406483203)
        ·
          refine ⟨19307933774232176109724805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12871955849488117406483203 19307933774232176109724805)
          ·
            refine ⟨3620237582668533020573401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19307933774232176109724805 3620237582668533020573401)
            ·
              refine ⟨2715178187001399765430051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3620237582668533020573401 2715178187001399765430051)
              ·
                refine ⟨4072767280502099648145077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715178187001399765430051 4072767280502099648145077)
                ·
                  refine ⟨381821932547071842013601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4072767280502099648145077 381821932547071842013601)
                  ·
                    rfl

theorem cell22_3346180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_3346180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346180 prefixEnd_3346180 := by exact prefixLift 3346180
  have htrace : WordTrace (prefixWord ++ tailWord_3346180) baseStart_3346180 baseEnd_3346180 := by
    simpa [prefixWord, tailWord_3346180, baseEnd_3346180] using wordTrace_append hprefix tailTrace_3346180
  have hstable : (prefixWord ++ tailWord_3346180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346180).length < 2 ^ (prefixWord ++ tailWord_3346180).sum := by decide
  have hdescent : baseEnd_3346180 < baseStart_3346180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346208 : List Nat := [2, 1, 1, 5, 1, 1, 2, 5, 4]
def baseStart_3346208 : Nat := 118140960795 + 3346208 * 2 ^ 59
def prefixEnd_3346208 : Nat := 4983230072969 + 3 ^ 40 * 3346208 * 2
def baseEnd_3346208 : Nat := 381825127537810928780239

theorem tailTrace_3346208 : CollatzResearch.WordTrace tailWord_3346208 prefixEnd_3346208 381825127537810928780239 := by
  unfold tailWord_3346208
  simp only [CollatzResearch.WordTrace]
  refine ⟨61023116130633688836559639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81364154840844918448746185 61023116130633688836559639)
  ·
    refine ⟨91534674195950533254839459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61023116130633688836559639 91534674195950533254839459)
    ·
      refine ⟨137302011293925799882259189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91534674195950533254839459 137302011293925799882259189)
      ·
        refine ⟨12872063558805543738961799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137302011293925799882259189 12872063558805543738961799)
        ·
          refine ⟨19308095338208315608442699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12872063558805543738961799 19308095338208315608442699)
          ·
            refine ⟨28962143007312473412664049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19308095338208315608442699 28962143007312473412664049)
            ·
              refine ⟨21721607255484355059498037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28962143007312473412664049 21721607255484355059498037)
              ·
                refine ⟨2036400680201658286827941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21721607255484355059498037 2036400680201658286827941)
                ·
                  refine ⟨381825127537810928780239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036400680201658286827941 381825127537810928780239)
                  ·
                    rfl

theorem cell22_3346208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 4].length) (baseStart_3346208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346208 prefixEnd_3346208 := by exact prefixLift 3346208
  have htrace : WordTrace (prefixWord ++ tailWord_3346208) baseStart_3346208 baseEnd_3346208 := by
    simpa [prefixWord, tailWord_3346208, baseEnd_3346208] using wordTrace_append hprefix tailTrace_3346208
  have hstable : (prefixWord ++ tailWord_3346208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346208).length < 2 ^ (prefixWord ++ tailWord_3346208).sum := by decide
  have hdescent : baseEnd_3346208 < baseStart_3346208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346210 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_3346210 : Nat := 118140960795 + 3346210 * 2 ^ 59
def prefixEnd_3346210 : Nat := 4983230072969 + 3 ^ 40 * 3346210 * 2
def baseEnd_3346210 : Nat := 1145476067254305447790711

theorem tailTrace_3346210 : CollatzResearch.WordTrace tailWord_3346210 prefixEnd_3346210 1145476067254305447790711 := by
  unfold tailWord_3346210
  simp only [CollatzResearch.WordTrace]
  refine ⟨30511576301815033003673021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81364203471506754676461389 30511576301815033003673021)
  ·
    refine ⟨11441841113180637376377383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30511576301815033003673021 11441841113180637376377383)
    ·
      refine ⟨17162761669770956064566075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11441841113180637376377383 17162761669770956064566075)
      ·
        refine ⟨25744142504656434096849113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17162761669770956064566075 25744142504656434096849113)
        ·
          refine ⟨19308106878492325572636835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25744142504656434096849113 19308106878492325572636835)
          ·
            refine ⟨28962160317738488358955253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19308106878492325572636835 28962160317738488358955253)
            ·
              refine ⟨2715202529787983283652055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28962160317738488358955253 2715202529787983283652055)
              ·
                refine ⟨4072803794681974925478083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715202529787983283652055 4072803794681974925478083)
                ·
                  refine ⟨6109205692022962388217125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4072803794681974925478083 6109205692022962388217125)
                  ·
                    refine ⟨1145476067254305447790711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6109205692022962388217125 1145476067254305447790711)
                    ·
                      rfl

theorem cell22_3346210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_3346210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346210 prefixEnd_3346210 := by exact prefixLift 3346210
  have htrace : WordTrace (prefixWord ++ tailWord_3346210) baseStart_3346210 baseEnd_3346210 := by
    simpa [prefixWord, tailWord_3346210, baseEnd_3346210] using wordTrace_append hprefix tailTrace_3346210
  have hstable : (prefixWord ++ tailWord_3346210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346210).length < 2 ^ (prefixWord ++ tailWord_3346210).sum := by decide
  have hdescent : baseEnd_3346210 < baseStart_3346210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346225 : List Nat := [1, 2, 2, 3, 2, 2, 4, 2, 4]
def baseStart_3346225 : Nat := 118140960795 + 3346225 * 2 ^ 59
def prefixEnd_3346225 : Nat := 4983230072969 + 3 ^ 40 * 3346225 * 2
def baseEnd_3346225 : Nat := 381827067353616802888555

theorem tailTrace_3346225 : CollatzResearch.WordTrace tailWord_3346225 prefixEnd_3346225 381827067353616802888555 := by
  unfold tailWord_3346225
  simp only [CollatzResearch.WordTrace]
  refine ⟨122046852302205789576488129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81364568201470526384325419 122046852302205789576488129)
  ·
    refine ⟨91535139226654342182366097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122046852302205789576488129 91535139226654342182366097)
    ·
      refine ⟨68651354419990756636774573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91535139226654342182366097 68651354419990756636774573)
      ·
        refine ⟨25744257907496533738790465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68651354419990756636774573 25744257907496533738790465)
        ·
          refine ⟨19308193430622400304092849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25744257907496533738790465 19308193430622400304092849)
          ·
            refine ⟨14481145072966800228069637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19308193430622400304092849 14481145072966800228069637)
            ·
              refine ⟨2715214701181275042763057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14481145072966800228069637 2715214701181275042763057)
              ·
                refine ⟨2036411025885956282072293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2715214701181275042763057 2036411025885956282072293)
                ·
                  refine ⟨381827067353616802888555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036411025885956282072293 381827067353616802888555)
                  ·
                    rfl

theorem cell22_3346225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 4].length) (baseStart_3346225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346225 prefixEnd_3346225 := by exact prefixLift 3346225
  have htrace : WordTrace (prefixWord ++ tailWord_3346225) baseStart_3346225 baseEnd_3346225 := by
    simpa [prefixWord, tailWord_3346225, baseEnd_3346225] using wordTrace_append hprefix tailTrace_3346225
  have hstable : (prefixWord ++ tailWord_3346225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346225).length < 2 ^ (prefixWord ++ tailWord_3346225).sum := by decide
  have hdescent : baseEnd_3346225 < baseStart_3346225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346236 : List Nat := [2, 2, 2, 2, 1, 1, 5, 7]
def baseStart_3346236 : Nat := 118140960795 + 3346236 * 2 ^ 59
def prefixEnd_3346236 : Nat := 4983230072969 + 3 ^ 40 * 3346236 * 2
def baseEnd_3346236 : Nat := 127276107509516671848959

theorem tailTrace_3346236 : CollatzResearch.WordTrace tailWord_3346236 prefixEnd_3346236 127276107509516671848959 := by
  unfold tailWord_3346236
  simp only [CollatzResearch.WordTrace]
  refine ⟨61023626752582969227569281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81364835670110625636759041 61023626752582969227569281)
  ·
    refine ⟨45767720064437226920676961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61023626752582969227569281 45767720064437226920676961)
    ·
      refine ⟨34325790048327920190507721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45767720064437226920676961 34325790048327920190507721)
      ·
        refine ⟨25744342536245940142880791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34325790048327920190507721 25744342536245940142880791)
        ·
          refine ⟨38616513804368910214321187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25744342536245940142880791 38616513804368910214321187)
          ·
            refine ⟨57924770706553365321481781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38616513804368910214321187 57924770706553365321481781)
            ·
              refine ⟨5430447253739377998888917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57924770706553365321481781 5430447253739377998888917)
              ·
                refine ⟨127276107509516671848959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5430447253739377998888917 127276107509516671848959)
                ·
                  rfl

theorem cell22_3346236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 7].length) (baseStart_3346236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346236 prefixEnd_3346236 := by exact prefixLift 3346236
  have htrace : WordTrace (prefixWord ++ tailWord_3346236) baseStart_3346236 baseEnd_3346236 := by
    simpa [prefixWord, tailWord_3346236, baseEnd_3346236] using wordTrace_append hprefix tailTrace_3346236
  have hstable : (prefixWord ++ tailWord_3346236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346236).length < 2 ^ (prefixWord ++ tailWord_3346236).sum := by decide
  have hdescent : baseEnd_3346236 < baseStart_3346236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346302 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_3346302 : Nat := 118140960795 + 3346302 * 2 ^ 59
def prefixEnd_3346302 : Nat := 4983230072969 + 3 ^ 40 * 3346302 * 2
def baseEnd_3346302 : Nat := 1145507560734447874490429

theorem tailTrace_3346302 : CollatzResearch.WordTrace tailWord_3346302 prefixEnd_3346302 1145507560734447874490429 := by
  unfold tailWord_3346302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15256207590365853965880145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81366440481951221151360773 15256207590365853965880145)
  ·
    refine ⟨11442155692774390474410109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15256207590365853965880145 11442155692774390474410109)
    ·
      refine ⟨4290808384790396427903791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11442155692774390474410109 4290808384790396427903791)
      ·
        refine ⟨6436212577185594641855687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290808384790396427903791 6436212577185594641855687)
        ·
          refine ⟨9654318865778391962783531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6436212577185594641855687 9654318865778391962783531)
          ·
            refine ⟨14481478298667587944175297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9654318865778391962783531 14481478298667587944175297)
            ·
              refine ⟨10861108724000690958131473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14481478298667587944175297 10861108724000690958131473)
              ·
                refine ⟨8145831543000518218598605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10861108724000690958131473 8145831543000518218598605)
                ·
                  refine ⟨3054686828625194331974477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8145831543000518218598605 3054686828625194331974477)
                  ·
                    refine ⟨1145507560734447874490429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3054686828625194331974477 1145507560734447874490429)
                    ·
                      rfl

theorem cell22_3346302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_3346302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346302 prefixEnd_3346302 := by exact prefixLift 3346302
  have htrace : WordTrace (prefixWord ++ tailWord_3346302) baseStart_3346302 baseEnd_3346302 := by
    simpa [prefixWord, tailWord_3346302, baseEnd_3346302] using wordTrace_append hprefix tailTrace_3346302
  have hstable : (prefixWord ++ tailWord_3346302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346302).length < 2 ^ (prefixWord ++ tailWord_3346302).sum := by decide
  have hdescent : baseEnd_3346302 < baseStart_3346302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346394 : List Nat := [3, 1, 1, 2, 5, 2, 2, 2, 4]
def baseStart_3346394 : Nat := 118140960795 + 3346394 * 2 ^ 59
def prefixEnd_3346394 : Nat := 4983230072969 + 3 ^ 40 * 3346394 * 2
def baseEnd_3346394 : Nat := 381846351404863433730049

theorem tailTrace_3346394 : CollatzResearch.WordTrace tailWord_3346394 prefixEnd_3346394 381846351404863433730049 := by
  unfold tailWord_3346394
  simp only [CollatzResearch.WordTrace]
  refine ⟨30513254059648382859847559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81368677492395687626260157 30513254059648382859847559)
  ·
    refine ⟨45769881089472574289771339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30513254059648382859847559 45769881089472574289771339)
    ·
      refine ⟨68654821634208861434657009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45769881089472574289771339 68654821634208861434657009)
      ·
        refine ⟨51491116225656646075992757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68654821634208861434657009 51491116225656646075992757)
        ·
          refine ⟨4827292146155310569624321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51491116225656646075992757 4827292146155310569624321)
          ·
            refine ⟨3620469109616482927218241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4827292146155310569624321 3620469109616482927218241)
            ·
              refine ⟨2715351832212362195413681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3620469109616482927218241 2715351832212362195413681)
              ·
                refine ⟨2036513874159271646560261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2715351832212362195413681 2036513874159271646560261)
                ·
                  refine ⟨381846351404863433730049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036513874159271646560261 381846351404863433730049)
                  ·
                    rfl

theorem cell22_3346394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_3346394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346394 prefixEnd_3346394 := by exact prefixLift 3346394
  have htrace : WordTrace (prefixWord ++ tailWord_3346394) baseStart_3346394 baseEnd_3346394 := by
    simpa [prefixWord, tailWord_3346394, baseEnd_3346394] using wordTrace_append hprefix tailTrace_3346394
  have hstable : (prefixWord ++ tailWord_3346394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346394).length < 2 ^ (prefixWord ++ tailWord_3346394).sum := by decide
  have hdescent : baseEnd_3346394 < baseStart_3346394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346422 : List Nat := [5, 1, 1, 1, 4, 1, 3, 6]
def baseStart_3346422 : Nat := 118140960795 + 3346422 * 2 ^ 59
def prefixEnd_3346422 : Nat := 4983230072969 + 3 ^ 40 * 3346422 * 2
def baseEnd_3346422 : Nat := 127283182131867506832229

theorem tailTrace_3346422 : CollatzResearch.WordTrace tailWord_3346422 prefixEnd_3346422 127283182131867506832229 := by
  unfold tailWord_3346422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628377342655755763838095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81369358321661394814273013 7628377342655755763838095)
  ·
    refine ⟨11442566013983633645757143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7628377342655755763838095 11442566013983633645757143)
    ·
      refine ⟨17163849020975450468635715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11442566013983633645757143 17163849020975450468635715)
      ·
        refine ⟨25745773531463175702953573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17163849020975450468635715 25745773531463175702953573)
        ·
          refine ⟨4827332537149345444303795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25745773531463175702953573 4827332537149345444303795)
          ·
            refine ⟨7240998805724018166455693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827332537149345444303795 7240998805724018166455693)
            ·
              refine ⟨2715374552146506812420885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7240998805724018166455693 2715374552146506812420885)
              ·
                refine ⟨127283182131867506832229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2715374552146506812420885 127283182131867506832229)
                ·
                  rfl

theorem cell22_3346422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_3346422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346422 prefixEnd_3346422 := by exact prefixLift 3346422
  have htrace : WordTrace (prefixWord ++ tailWord_3346422) baseStart_3346422 baseEnd_3346422 := by
    simpa [prefixWord, tailWord_3346422, baseEnd_3346422] using wordTrace_append hprefix tailTrace_3346422
  have hstable : (prefixWord ++ tailWord_3346422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346422).length < 2 ^ (prefixWord ++ tailWord_3346422).sum := by decide
  have hdescent : baseEnd_3346422 < baseStart_3346422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346433 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 7]
def baseStart_3346433 : Nat := 118140960795 + 3346433 * 2 ^ 59
def prefixEnd_3346433 : Nat := 4983230072969 + 3 ^ 40 * 3346433 * 2
def baseEnd_3346433 : Nat := 381850801570535733155009

theorem tailTrace_3346433 : CollatzResearch.WordTrace tailWord_3346433 prefixEnd_3346433 381850801570535733155009 := by
  unfold tailWord_3346433
  simp only [CollatzResearch.WordTrace]
  refine ⟨122054438685452241100059953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81369625790301494066706635 122054438685452241100059953)
  ·
    refine ⟨91540829014089180825044965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122054438685452241100059953 91540829014089180825044965)
    ·
      refine ⟨17163905440141721404695931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91540829014089180825044965 17163905440141721404695931)
      ·
        refine ⟨25745858160212582107043897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17163905440141721404695931 25745858160212582107043897)
        ·
          refine ⟨19309393620159436580282923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25745858160212582107043897 19309393620159436580282923)
          ·
            refine ⟨28964090430239154870424385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19309393620159436580282923 28964090430239154870424385)
            ·
              refine ⟨21723067822679366152818289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28964090430239154870424385 21723067822679366152818289)
              ·
                refine ⟨16292300867009524614613717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21723067822679366152818289 16292300867009524614613717)
                ·
                  refine ⟨381850801570535733155009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16292300867009524614613717 381850801570535733155009)
                  ·
                    rfl

theorem cell22_3346433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_3346433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346433 prefixEnd_3346433 := by exact prefixLift 3346433
  have htrace : WordTrace (prefixWord ++ tailWord_3346433) baseStart_3346433 baseEnd_3346433 := by
    simpa [prefixWord, tailWord_3346433, baseEnd_3346433] using wordTrace_append hprefix tailTrace_3346433
  have hstable : (prefixWord ++ tailWord_3346433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346433).length < 2 ^ (prefixWord ++ tailWord_3346433).sum := by decide
  have hdescent : baseEnd_3346433 < baseStart_3346433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346437 : List Nat := [1, 3, 1, 1, 2, 4, 1, 5, 1, 3]
def baseStart_3346437 : Nat := 118140960795 + 3346437 * 2 ^ 59
def prefixEnd_3346437 : Nat := 4983230072969 + 3 ^ 40 * 3346437 * 2
def baseEnd_3346437 : Nat := 1145553773993352522365015

theorem tailTrace_3346437 : CollatzResearch.WordTrace tailWord_3346437 prefixEnd_3346437 1145553773993352522365015 := by
  unfold tailWord_3346437
  simp only [CollatzResearch.WordTrace]
  refine ⟨122054584577437749783205565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81369723051625166522137043 122054584577437749783205565)
  ·
    refine ⟨45770469216539156168702087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122054584577437749783205565 45770469216539156168702087)
    ·
      refine ⟨68655703824808734253053131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45770469216539156168702087 68655703824808734253053131)
      ·
        refine ⟨102983555737213101379579697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68655703824808734253053131 102983555737213101379579697)
        ·
          refine ⟨77237666802909826034684773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102983555737213101379579697 77237666802909826034684773)
          ·
            refine ⟨14482062525545592381503395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77237666802909826034684773 14482062525545592381503395)
            ·
              refine ⟨21723093788318388572255093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14482062525545592381503395 21723093788318388572255093)
              ·
                refine ⟨2036540042654848928648915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21723093788318388572255093 2036540042654848928648915)
                ·
                  refine ⟨3054810063982273392973373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036540042654848928648915 3054810063982273392973373)
                  ·
                    refine ⟨1145553773993352522365015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3054810063982273392973373 1145553773993352522365015)
                    ·
                      rfl

theorem cell22_3346437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_3346437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346437 prefixEnd_3346437 := by exact prefixLift 3346437
  have htrace : WordTrace (prefixWord ++ tailWord_3346437) baseStart_3346437 baseEnd_3346437 := by
    simpa [prefixWord, tailWord_3346437, baseEnd_3346437] using wordTrace_append hprefix tailTrace_3346437
  have hstable : (prefixWord ++ tailWord_3346437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346437).length < 2 ^ (prefixWord ++ tailWord_3346437).sum := by decide
  have hdescent : baseEnd_3346437 < baseStart_3346437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346480 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 1, 4]
def baseStart_3346480 : Nat := 118140960795 + 3346480 * 2 ^ 59
def prefixEnd_3346480 : Nat := 4983230072969 + 3 ^ 40 * 3346480 * 2
def baseEnd_3346480 : Nat := 1145568493772114743539883

theorem tailTrace_3346480 : CollatzResearch.WordTrace tailWord_3346480 prefixEnd_3346480 1145568493772114743539883 := by
  unfold tailWord_3346480
  simp only [CollatzResearch.WordTrace]
  refine ⟨61028076458140984063510447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81370768610854645418013929 61028076458140984063510447)
  ·
    refine ⟨91542114687211476095265671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61028076458140984063510447 91542114687211476095265671)
    ·
      refine ⟨137313172030817214142898507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91542114687211476095265671 137313172030817214142898507)
      ·
        refine ⟨205969758046225821214347761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137313172030817214142898507 205969758046225821214347761)
        ·
          refine ⟨154477318534669365910760821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205969758046225821214347761 154477318534669365910760821)
          ·
            refine ⟨14482248612625253054133827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154477318534669365910760821 14482248612625253054133827)
            ·
              refine ⟨21723372918937879581200741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14482248612625253054133827 21723372918937879581200741)
              ·
                refine ⟨4073132422300852421475139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21723372918937879581200741 4073132422300852421475139)
                ·
                  refine ⟨6109698633451278632212709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4073132422300852421475139 6109698633451278632212709)
                  ·
                    refine ⟨1145568493772114743539883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6109698633451278632212709 1145568493772114743539883)
                    ·
                      rfl

theorem cell22_3346480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_3346480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346480 prefixEnd_3346480 := by exact prefixLift 3346480
  have htrace : WordTrace (prefixWord ++ tailWord_3346480) baseStart_3346480 baseEnd_3346480 := by
    simpa [prefixWord, tailWord_3346480, baseEnd_3346480] using wordTrace_append hprefix tailTrace_3346480
  have hstable : (prefixWord ++ tailWord_3346480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346480).length < 2 ^ (prefixWord ++ tailWord_3346480).sum := by decide
  have hdescent : baseEnd_3346480 < baseStart_3346480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346497 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3346497 : Nat := 118140960795 + 3346497 * 2 ^ 59
def prefixEnd_3346497 : Nat := 4983230072969 + 3 ^ 40 * 3346497 * 2
def baseEnd_3346497 : Nat := 1145574313219532365864831

theorem tailTrace_3346497 : CollatzResearch.WordTrace tailWord_3346497 prefixEnd_3346497 1145574313219532365864831 := by
  unfold tailWord_3346497
  simp only [CollatzResearch.WordTrace]
  refine ⟨122056772957220380030389745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81371181971480253353593163 122056772957220380030389745)
  ·
    refine ⟨91542579717915285022792309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122056772957220380030389745 91542579717915285022792309)
    ·
      refine ⟨8582116848554557970886779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91542579717915285022792309 8582116848554557970886779)
      ·
        refine ⟨12873175272831836956330169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8582116848554557970886779 12873175272831836956330169)
        ·
          refine ⟨9654881454623877717247627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12873175272831836956330169 9654881454623877717247627)
          ·
            refine ⟨14482322181935816575871441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9654881454623877717247627 14482322181935816575871441)
            ·
              refine ⟨10861741636451862431903581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14482322181935816575871441 10861741636451862431903581)
              ·
                refine ⟨4073153113669448411963843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10861741636451862431903581 4073153113669448411963843)
                ·
                  refine ⟨6109729670504172617945765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4073153113669448411963843 6109729670504172617945765)
                  ·
                    refine ⟨1145574313219532365864831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6109729670504172617945765 1145574313219532365864831)
                    ·
                      rfl

theorem cell22_3346497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3346497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346497 prefixEnd_3346497 := by exact prefixLift 3346497
  have htrace : WordTrace (prefixWord ++ tailWord_3346497) baseStart_3346497 baseEnd_3346497 := by
    simpa [prefixWord, tailWord_3346497, baseEnd_3346497] using wordTrace_append hprefix tailTrace_3346497
  have hstable : (prefixWord ++ tailWord_3346497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346497).length < 2 ^ (prefixWord ++ tailWord_3346497).sum := by decide
  have hdescent : baseEnd_3346497 < baseStart_3346497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346542 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_3346542 : Nat := 118140960795 + 3346542 * 2 ^ 59
def prefixEnd_3346542 : Nat := 4983230072969 + 3 ^ 40 * 3346542 * 2
def baseEnd_3346542 : Nat := 1145589717639167248489693

theorem tailTrace_3346542 : CollatzResearch.WordTrace tailWord_3346542 prefixEnd_3346542 1145589717639167248489693 := by
  unfold tailWord_3346542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15257301780257169089472235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81372276161371568477185253 15257301780257169089472235)
  ·
    refine ⟨22885952670385753634208353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15257301780257169089472235 22885952670385753634208353)
    ·
      refine ⟨17164464502789315225656265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22885952670385753634208353 17164464502789315225656265)
      ·
        refine ⟨12873348377091986419242199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17164464502789315225656265 12873348377091986419242199)
        ·
          refine ⟨19310022565637979628863299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12873348377091986419242199 19310022565637979628863299)
          ·
            refine ⟨28965033848456969443294949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19310022565637979628863299 28965033848456969443294949)
            ·
              refine ⟨5430943846585681770617803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28965033848456969443294949 5430943846585681770617803)
              ·
                refine ⟨8146415769878522655926705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430943846585681770617803 8146415769878522655926705)
                ·
                  refine ⟨6109811827408891991945029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8146415769878522655926705 6109811827408891991945029)
                  ·
                    refine ⟨1145589717639167248489693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6109811827408891991945029 1145589717639167248489693)
                    ·
                      rfl

theorem cell22_3346542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_3346542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346542 prefixEnd_3346542 := by exact prefixLift 3346542
  have htrace : WordTrace (prefixWord ++ tailWord_3346542) baseStart_3346542 baseEnd_3346542 := by
    simpa [prefixWord, tailWord_3346542, baseEnd_3346542] using wordTrace_append hprefix tailTrace_3346542
  have hstable : (prefixWord ++ tailWord_3346542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346542).length < 2 ^ (prefixWord ++ tailWord_3346542).sum := by decide
  have hdescent : baseEnd_3346542 < baseStart_3346542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346570 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_3346570 : Nat := 118140960795 + 3346570 * 2 ^ 59
def prefixEnd_3346570 : Nat := 4983230072969 + 3 ^ 40 * 3346570 * 2
def baseEnd_3346570 : Nat := 1145599302611384508789607

theorem tailTrace_3346570 : CollatzResearch.WordTrace tailWord_3346570 prefixEnd_3346570 1145599302611384508789607 := by
  unfold tailWord_3346570
  simp only [CollatzResearch.WordTrace]
  refine ⟨30514858871488978374449291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81372956990637275665198109 30514858871488978374449291)
  ·
    refine ⟨45772288307233467561673937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30514858871488978374449291 45772288307233467561673937)
    ·
      refine ⟨34329216230425100671255453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45772288307233467561673937 34329216230425100671255453)
      ·
        refine ⟨12873456086409412751720795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34329216230425100671255453 12873456086409412751720795)
        ·
          refine ⟨19310184129614119127581193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12873456086409412751720795 19310184129614119127581193)
          ·
            refine ⟨14482638097210589345685895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19310184129614119127581193 14482638097210589345685895)
            ·
              refine ⟨21723957145815884018528843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14482638097210589345685895 21723957145815884018528843)
              ·
                refine ⟨32585935718723826027793265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21723957145815884018528843 32585935718723826027793265)
                ·
                  refine ⟨24439451789042869520844949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32585935718723826027793265 24439451789042869520844949)
                  ·
                    refine ⟨1145599302611384508789607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24439451789042869520844949 1145599302611384508789607)
                    ·
                      rfl

theorem cell22_3346570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_3346570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346570 prefixEnd_3346570 := by exact prefixLift 3346570
  have htrace : WordTrace (prefixWord ++ tailWord_3346570) baseStart_3346570 baseEnd_3346570 := by
    simpa [prefixWord, tailWord_3346570, baseEnd_3346570] using wordTrace_append hprefix tailTrace_3346570
  have hstable : (prefixWord ++ tailWord_3346570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346570).length < 2 ^ (prefixWord ++ tailWord_3346570).sum := by decide
  have hdescent : baseEnd_3346570 < baseStart_3346570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346574 : List Nat := [4, 1, 1, 3, 4, 1, 1, 7]
def baseStart_3346574 : Nat := 118140960795 + 3346574 * 2 ^ 59
def prefixEnd_3346574 : Nat := 4983230072969 + 3 ^ 40 * 3346574 * 2
def baseEnd_3346574 : Nat := 127288963543681092409955

theorem tailTrace_3346574 : CollatzResearch.WordTrace tailWord_3346574 prefixEnd_3346574 127288963543681092409955 := by
  unfold tailWord_3346574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15257447672242677772617847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81373054251960948120628517 15257447672242677772617847)
  ·
    refine ⟨22886171508364016658926771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15257447672242677772617847 22886171508364016658926771)
    ·
      refine ⟨34329257262546024988390157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22886171508364016658926771 34329257262546024988390157)
      ·
        refine ⟨12873471473454759370646309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34329257262546024988390157 12873471473454759370646309)
        ·
          refine ⟨2413775901272767381996183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12873471473454759370646309 2413775901272767381996183)
          ·
            refine ⟨3620663851909151072994275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413775901272767381996183 3620663851909151072994275)
            ·
              refine ⟨5430995777863726609491413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620663851909151072994275 5430995777863726609491413)
              ·
                refine ⟨127288963543681092409955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5430995777863726609491413 127288963543681092409955)
                ·
                  rfl

theorem cell22_3346574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_3346574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346574 prefixEnd_3346574 := by exact prefixLift 3346574
  have htrace : WordTrace (prefixWord ++ tailWord_3346574) baseStart_3346574 baseEnd_3346574 := by
    simpa [prefixWord, tailWord_3346574, baseEnd_3346574] using wordTrace_append hprefix tailTrace_3346574
  have hstable : (prefixWord ++ tailWord_3346574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346574).length < 2 ^ (prefixWord ++ tailWord_3346574).sum := by decide
  have hdescent : baseEnd_3346574 < baseStart_3346574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346612 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3346612 : Nat := 118140960795 + 3346612 * 2 ^ 59
def prefixEnd_3346612 : Nat := 4983230072969 + 3 ^ 40 * 3346612 * 2
def baseEnd_3346612 : Nat := 1145613680069710399239479

theorem tailTrace_3346612 : CollatzResearch.WordTrace tailWord_3346612 prefixEnd_3346612 1145613680069710399239479 := by
  unfold tailWord_3346612
  simp only [CollatzResearch.WordTrace]
  refine ⟨61030483675901877335413045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81373978234535836447217393 61030483675901877335413045)
  ·
    refine ⟨5721607844615801000194973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61030483675901877335413045 5721607844615801000194973)
    ·
      refine ⟨2145602941730925375073115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5721607844615801000194973 2145602941730925375073115)
      ·
        refine ⟨3218404412596388062609673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145602941730925375073115 3218404412596388062609673)
        ·
          refine ⟨2413803309447291046957255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3218404412596388062609673 2413803309447291046957255)
          ·
            refine ⟨3620704964170936570435883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413803309447291046957255 3620704964170936570435883)
            ·
              refine ⟨5431057446256404855653825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620704964170936570435883 5431057446256404855653825)
              ·
                refine ⟨4073293084692303641740369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5431057446256404855653825 4073293084692303641740369)
                ·
                  refine ⟨3054969813519227731305277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4073293084692303641740369 3054969813519227731305277)
                  ·
                    refine ⟨1145613680069710399239479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3054969813519227731305277 1145613680069710399239479)
                    ·
                      rfl

theorem cell22_3346612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3346612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346612 prefixEnd_3346612 := by exact prefixLift 3346612
  have htrace : WordTrace (prefixWord ++ tailWord_3346612) baseStart_3346612 baseEnd_3346612 := by
    simpa [prefixWord, tailWord_3346612, baseEnd_3346612] using wordTrace_append hprefix tailTrace_3346612
  have hstable : (prefixWord ++ tailWord_3346612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346612).length < 2 ^ (prefixWord ++ tailWord_3346612).sum := by decide
  have hdescent : baseEnd_3346612 < baseStart_3346612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346636 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 5]
def baseStart_3346636 : Nat := 118140960795 + 3346636 * 2 ^ 59
def prefixEnd_3346636 : Nat := 4983230072969 + 3 ^ 40 * 3346636 * 2
def baseEnd_3346636 : Nat := 381873965253394112213135

theorem tailTrace_3346636 : CollatzResearch.WordTrace tailWord_3346636 prefixEnd_3346636 381873965253394112213135 := by
  unfold tailWord_3346636
  simp only [CollatzResearch.WordTrace]
  refine ⟨61030921351858403384849881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81374561802477871179799841 61030921351858403384849881)
  ·
    refine ⟨45773191013893802538637411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61030921351858403384849881 45773191013893802538637411)
    ·
      refine ⟨68659786520840703807956117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45773191013893802538637411 68659786520840703807956117)
      ·
        refine ⟨3218427493164407990997943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68659786520840703807956117 3218427493164407990997943)
        ·
          refine ⟨4827641239746611986496915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3218427493164407990997943 4827641239746611986496915)
          ·
            refine ⟨7241461859619917979745373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827641239746611986496915 7241461859619917979745373)
            ·
              refine ⟨2715548197357469242404515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7241461859619917979745373 2715548197357469242404515)
              ·
                refine ⟨4073322296036203863606773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715548197357469242404515 4073322296036203863606773)
                ·
                  refine ⟨381873965253394112213135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4073322296036203863606773 381873965253394112213135)
                  ·
                    rfl

theorem cell22_3346636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_3346636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346636 prefixEnd_3346636 := by exact prefixLift 3346636
  have htrace : WordTrace (prefixWord ++ tailWord_3346636) baseStart_3346636 baseEnd_3346636 := by
    simpa [prefixWord, tailWord_3346636, baseEnd_3346636] using wordTrace_append hprefix tailTrace_3346636
  have hstable : (prefixWord ++ tailWord_3346636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346636).length < 2 ^ (prefixWord ++ tailWord_3346636).sum := by decide
  have hdescent : baseEnd_3346636 < baseStart_3346636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346664 : List Nat := [2, 1, 4, 1, 2, 2, 3, 3, 4]
def baseStart_3346664 : Nat := 118140960795 + 3346664 * 2 ^ 59
def prefixEnd_3346664 : Nat := 4983230072969 + 3 ^ 40 * 3346664 * 2
def baseEnd_3346664 : Nat := 381877160244133198979773

theorem tailTrace_3346664 : CollatzResearch.WordTrace tailWord_3346664 prefixEnd_3346664 381877160244133198979773 := by
  unfold tailWord_3346664
  simp only [CollatzResearch.WordTrace]
  refine ⟨61031431973807683775859523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81375242631743578367812697 61031431973807683775859523)
  ·
    refine ⟨91547147960711525663789285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61031431973807683775859523 91547147960711525663789285)
    ·
      refine ⟨17165090242633411061960491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91547147960711525663789285 17165090242633411061960491)
      ·
        refine ⟨25747635363950116592940737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17165090242633411061960491 25747635363950116592940737)
        ·
          refine ⟨19310726522962587444705553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25747635363950116592940737 19310726522962587444705553)
          ·
            refine ⟨14483044892221940583529165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19310726522962587444705553 14483044892221940583529165)
            ·
              refine ⟨5431141834583227718823437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14483044892221940583529165 5431141834583227718823437)
              ·
                refine ⟨2036678187968710394558789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5431141834583227718823437 2036678187968710394558789)
                ·
                  refine ⟨381877160244133198979773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036678187968710394558789 381877160244133198979773)
                  ·
                    rfl

theorem cell22_3346664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 4].length) (baseStart_3346664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346664 prefixEnd_3346664 := by exact prefixLift 3346664
  have htrace : WordTrace (prefixWord ++ tailWord_3346664) baseStart_3346664 baseEnd_3346664 := by
    simpa [prefixWord, tailWord_3346664, baseEnd_3346664] using wordTrace_append hprefix tailTrace_3346664
  have hstable : (prefixWord ++ tailWord_3346664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346664).length < 2 ^ (prefixWord ++ tailWord_3346664).sum := by decide
  have hdescent : baseEnd_3346664 < baseStart_3346664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346696 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 2, 3]
def baseStart_3346696 : Nat := 118140960795 + 3346696 * 2 ^ 59
def prefixEnd_3346696 : Nat := 4983230072969 + 3 ^ 40 * 3346696 * 2
def baseEnd_3346696 : Nat := 1145642434986362180139221

theorem tailTrace_3346696 : CollatzResearch.WordTrace tailWord_3346696 prefixEnd_3346696 1145642434986362180139221 := by
  unfold tailWord_3346696
  simp only [CollatzResearch.WordTrace]
  refine ⟨61032015541749718508441971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81376020722332958011255961 61032015541749718508441971)
  ·
    refine ⟨91548023312624577762662957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61032015541749718508441971 91548023312624577762662957)
    ·
      refine ⟨34330508742234216660998609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91548023312624577762662957 34330508742234216660998609)
      ·
        refine ⟨25747881556675662495748957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34330508742234216660998609 25747881556675662495748957)
        ·
          refine ⟨9655455583753373435905859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25747881556675662495748957 9655455583753373435905859)
          ·
            refine ⟨14483183375630060153858789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9655455583753373435905859 14483183375630060153858789)
            ·
              refine ⟨2715596882930636278848523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14483183375630060153858789 2715596882930636278848523)
              ·
                refine ⟨4073395324395954418272785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715596882930636278848523 4073395324395954418272785)
                ·
                  refine ⟨3055046493296965813704589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4073395324395954418272785 3055046493296965813704589)
                  ·
                    refine ⟨1145642434986362180139221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055046493296965813704589 1145642434986362180139221)
                    ·
                      rfl

theorem cell22_3346696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_3346696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346696 prefixEnd_3346696 := by exact prefixLift 3346696
  have htrace : WordTrace (prefixWord ++ tailWord_3346696) baseStart_3346696 baseEnd_3346696 := by
    simpa [prefixWord, tailWord_3346696, baseEnd_3346696] using wordTrace_append hprefix tailTrace_3346696
  have hstable : (prefixWord ++ tailWord_3346696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346696).length < 2 ^ (prefixWord ++ tailWord_3346696).sum := by decide
  have hdescent : baseEnd_3346696 < baseStart_3346696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346707 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 3, 3]
def baseStart_3346707 : Nat := 118140960795 + 3346707 * 2 ^ 59
def prefixEnd_3346707 : Nat := 4983230072969 + 3 ^ 40 * 3346707 * 2
def baseEnd_3346707 : Nat := 1145646200511161818114187

theorem tailTrace_3346707 : CollatzResearch.WordTrace tailWord_3346707 prefixEnd_3346707 1145646200511161818114187 := by
  unfold tailWord_3346707
  simp only [CollatzResearch.WordTrace]
  refine ⟨122064432286459585895534375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81376288190973057263689583 122064432286459585895534375)
  ·
    refine ⟨183096648429689378843301563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122064432286459585895534375 183096648429689378843301563)
    ·
      refine ⟨274644972644534068264952345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183096648429689378843301563 274644972644534068264952345)
      ·
        refine ⟨205983729483400551198714259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274644972644534068264952345 205983729483400551198714259)
        ·
          refine ⟨308975594225100826798071389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205983729483400551198714259 308975594225100826798071389)
          ·
            refine ⟨115865847834412810049276771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308975594225100826798071389 115865847834412810049276771)
            ·
              refine ⟨173798771751619215073915157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115865847834412810049276771 173798771751619215073915157)
              ·
                refine ⟨8146817425857150706589773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173798771751619215073915157 8146817425857150706589773)
                ·
                  refine ⟨3055056534696431514971165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8146817425857150706589773 3055056534696431514971165)
                  ·
                    refine ⟨1145646200511161818114187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055056534696431514971165 1145646200511161818114187)
                    ·
                      rfl

theorem cell22_3346707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 3].length) (baseStart_3346707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346707 prefixEnd_3346707 := by exact prefixLift 3346707
  have htrace : WordTrace (prefixWord ++ tailWord_3346707) baseStart_3346707 baseEnd_3346707 := by
    simpa [prefixWord, tailWord_3346707, baseEnd_3346707] using wordTrace_append hprefix tailTrace_3346707
  have hstable : (prefixWord ++ tailWord_3346707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346707).length < 2 ^ (prefixWord ++ tailWord_3346707).sum := by decide
  have hdescent : baseEnd_3346707 < baseStart_3346707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346741 : List Nat := [1, 3, 3, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3346741 : Nat := 118140960795 + 3346741 * 2 ^ 59
def prefixEnd_3346741 : Nat := 4983230072969 + 3 ^ 40 * 3346741 * 2
def baseEnd_3346741 : Nat := 1145657839405997062764083

theorem tailTrace_3346741 : CollatzResearch.WordTrace tailWord_3346741 prefixEnd_3346741 1145657839405997062764083 := by
  unfold tailWord_3346741
  simp only [CollatzResearch.WordTrace]
  refine ⟨122065672368336409702272077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81377114912224273134848051 122065672368336409702272077)
  ·
    refine ⟨45774627138126153638352029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122065672368336409702272077 45774627138126153638352029)
    ·
      refine ⟨17165485176797307614382011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45774627138126153638352029 17165485176797307614382011)
      ·
        refine ⟨25748227765195961421573017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17165485176797307614382011 25748227765195961421573017)
        ·
          refine ⟨19311170823896971066179763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25748227765195961421573017 19311170823896971066179763)
          ·
            refine ⟨28966756235845456599269645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19311170823896971066179763 28966756235845456599269645)
            ·
              refine ⟨10862533588442046224726117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28966756235845456599269645 10862533588442046224726117)
              ·
                refine ⟨2036725047832883667136147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10862533588442046224726117 2036725047832883667136147)
                ·
                  refine ⟨3055087571749325500704221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036725047832883667136147 3055087571749325500704221)
                  ·
                    refine ⟨1145657839405997062764083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055087571749325500704221 1145657839405997062764083)
                    ·
                      rfl

theorem cell22_3346741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3346741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346741 prefixEnd_3346741 := by exact prefixLift 3346741
  have htrace : WordTrace (prefixWord ++ tailWord_3346741) baseStart_3346741 baseEnd_3346741 := by
    simpa [prefixWord, tailWord_3346741, baseEnd_3346741] using wordTrace_append hprefix tailTrace_3346741
  have hstable : (prefixWord ++ tailWord_3346741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346741).length < 2 ^ (prefixWord ++ tailWord_3346741).sum := by decide
  have hdescent : baseEnd_3346741 < baseStart_3346741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346812 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_3346812 : Nat := 118140960795 + 3346812 * 2 ^ 59
def prefixEnd_3346812 : Nat := 4983230072969 + 3 ^ 40 * 3346812 * 2
def baseEnd_3346812 : Nat := 1145682144156976544238865

theorem tailTrace_3346812 : CollatzResearch.WordTrace tailWord_3346812 prefixEnd_3346812 1145682144156976544238865 := by
  unfold tailWord_3346812
  simp only [CollatzResearch.WordTrace]
  refine ⟨61034130975539594414053345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81378841300719459218737793 61034130975539594414053345)
  ·
    refine ⟨45775598231654695810540009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61034130975539594414053345 45775598231654695810540009)
    ·
      refine ⟨34331698673741021857905007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45775598231654695810540009 34331698673741021857905007)
      ·
        refine ⟨51497548010611532786857511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34331698673741021857905007 51497548010611532786857511)
        ·
          refine ⟨77246322015917299180286267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51497548010611532786857511 77246322015917299180286267)
          ·
            refine ⟨115869483023875948770429401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77246322015917299180286267 115869483023875948770429401)
            ·
              refine ⟨86902112267906961577822051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115869483023875948770429401 86902112267906961577822051)
              ·
                refine ⟨130353168401860442366733077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86902112267906961577822051 130353168401860442366733077)
                ·
                  refine ⟨6110304768837208235940613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130353168401860442366733077 6110304768837208235940613)
                  ·
                    refine ⟨1145682144156976544238865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6110304768837208235940613 1145682144156976544238865)
                    ·
                      rfl

theorem cell22_3346812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_3346812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346812 prefixEnd_3346812 := by exact prefixLift 3346812
  have htrace : WordTrace (prefixWord ++ tailWord_3346812) baseStart_3346812 baseEnd_3346812 := by
    simpa [prefixWord, tailWord_3346812, baseEnd_3346812] using wordTrace_append hprefix tailTrace_3346812
  have hstable : (prefixWord ++ tailWord_3346812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346812).length < 2 ^ (prefixWord ++ tailWord_3346812).sum := by decide
  have hdescent : baseEnd_3346812 < baseStart_3346812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346827 : List Nat := [1, 1, 1, 1, 4, 5, 1, 8]
def baseStart_3346827 : Nat := 118140960795 + 3346827 * 2 ^ 59
def prefixEnd_3346827 : Nat := 4983230072969 + 3 ^ 40 * 3346827 * 2
def baseEnd_3346827 : Nat := 127298586551502389457091

theorem tailTrace_3346827 : CollatzResearch.WordTrace tailWord_3346827 prefixEnd_3346827 127298586551502389457091 := by
  unfold tailWord_3346827
  simp only [CollatzResearch.WordTrace]
  refine ⟨122068809046024846389902735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81379206030683230926601823 122068809046024846389902735)
  ·
    refine ⟨183103213569037269584854103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122068809046024846389902735 183103213569037269584854103)
    ·
      refine ⟨274654820353555904377281155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183103213569037269584854103 274654820353555904377281155)
      ·
        refine ⟨411982230530333856565921733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274654820353555904377281155 411982230530333856565921733)
        ·
          refine ⟨77246668224437598106110325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 411982230530333856565921733 77246668224437598106110325)
          ·
            refine ⟨7241875146041024822447843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77246668224437598106110325 7241875146041024822447843)
            ·
              refine ⟨10862812719061537233671765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7241875146041024822447843 10862812719061537233671765)
              ·
                refine ⟨127298586551502389457091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10862812719061537233671765 127298586551502389457091)
                ·
                  rfl

theorem cell22_3346827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 8].length) (baseStart_3346827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346827 prefixEnd_3346827 := by exact prefixLift 3346827
  have htrace : WordTrace (prefixWord ++ tailWord_3346827) baseStart_3346827 baseEnd_3346827 := by
    simpa [prefixWord, tailWord_3346827, baseEnd_3346827] using wordTrace_append hprefix tailTrace_3346827
  have hstable : (prefixWord ++ tailWord_3346827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346827).length < 2 ^ (prefixWord ++ tailWord_3346827).sum := by decide
  have hdescent : baseEnd_3346827 < baseStart_3346827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346846 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3346846 : Nat := 118140960795 + 3346846 * 2 ^ 59
def prefixEnd_3346846 : Nat := 4983230072969 + 3 ^ 40 * 3346846 * 2
def baseEnd_3346846 : Nat := 1145693783051811788888761

theorem tailTrace_3346846 : CollatzResearch.WordTrace tailWord_3346846 prefixEnd_3346846 1145693783051811788888761 := by
  unfold tailWord_3346846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15258687754119501579355549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81379668021970675089896261 15258687754119501579355549)
  ·
    refine ⟨5722007907794813092258331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15258687754119501579355549 5722007907794813092258331)
    ·
      refine ⟨8583011861692219638387497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5722007907794813092258331 8583011861692219638387497)
      ·
        refine ⟨6437258896269164728790623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8583011861692219638387497 6437258896269164728790623)
        ·
          refine ⟨9655888344403747093185935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6437258896269164728790623 9655888344403747093185935)
          ·
            refine ⟨14483832516605620639778903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9655888344403747093185935 14483832516605620639778903)
            ·
              refine ⟨21725748774908430959668355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14483832516605620639778903 21725748774908430959668355)
              ·
                refine ⟨32588623162362646439502533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21725748774908430959668355 32588623162362646439502533)
                ·
                  refine ⟨6110366842942996207406725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32588623162362646439502533 6110366842942996207406725)
                  ·
                    refine ⟨1145693783051811788888761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6110366842942996207406725 1145693783051811788888761)
                    ·
                      rfl

theorem cell22_3346846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3346846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346846 prefixEnd_3346846 := by exact prefixLift 3346846
  have htrace : WordTrace (prefixWord ++ tailWord_3346846) baseStart_3346846 baseEnd_3346846 := by
    simpa [prefixWord, tailWord_3346846, baseEnd_3346846] using wordTrace_append hprefix tailTrace_3346846
  have hstable : (prefixWord ++ tailWord_3346846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346846).length < 2 ^ (prefixWord ++ tailWord_3346846).sum := by decide
  have hdescent : baseEnd_3346846 < baseStart_3346846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346861 : List Nat := [1, 5, 2, 2, 2, 1, 2, 7]
def baseStart_3346861 : Nat := 118140960795 + 3346861 * 2 ^ 59
def prefixEnd_3346861 : Nat := 4983230072969 + 3 ^ 40 * 3346861 * 2
def baseEnd_3346861 : Nat := 127299879762039638862635

theorem tailTrace_3346861 : CollatzResearch.WordTrace tailWord_3346861 prefixEnd_3346861 127299879762039638862635 := by
  unfold tailWord_3346861
  simp only [CollatzResearch.WordTrace]
  refine ⟨122070049127901670196640437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81380032751934446797760291 122070049127901670196640437)
  ·
    refine ⟨11444067105740781580935041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122070049127901670196640437 11444067105740781580935041)
    ·
      refine ⟨8583050329305586185701281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11444067105740781580935041 8583050329305586185701281)
      ·
        refine ⟨6437287746979189639275961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8583050329305586185701281 6437287746979189639275961)
        ·
          refine ⟨4827965810234392229456971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6437287746979189639275961 4827965810234392229456971)
          ·
            refine ⟨7241948715351588344185457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827965810234392229456971 7241948715351588344185457)
            ·
              refine ⟨5431461536513691258139093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7241948715351588344185457 5431461536513691258139093)
              ·
                refine ⟨127299879762039638862635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5431461536513691258139093 127299879762039638862635)
                ·
                  rfl

theorem cell22_3346861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 7].length) (baseStart_3346861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346861 prefixEnd_3346861 := by exact prefixLift 3346861
  have htrace : WordTrace (prefixWord ++ tailWord_3346861) baseStart_3346861 baseEnd_3346861 := by
    simpa [prefixWord, tailWord_3346861, baseEnd_3346861] using wordTrace_append hprefix tailTrace_3346861
  have hstable : (prefixWord ++ tailWord_3346861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346861).length < 2 ^ (prefixWord ++ tailWord_3346861).sum := by decide
  have hdescent : baseEnd_3346861 < baseStart_3346861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346919 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3346919 : Nat := 118140960795 + 3346919 * 2 ^ 59
def prefixEnd_3346919 : Nat := 4983230072969 + 3 ^ 40 * 3346919 * 2
def baseEnd_3346919 : Nat := 1145718772443663931813537

theorem tailTrace_3346919 : CollatzResearch.WordTrace tailWord_3346919 prefixEnd_3346919 1145718772443663931813537 := by
  unfold tailWord_3346919
  simp only [CollatzResearch.WordTrace]
  refine ⟨122072164561691546102251811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81381443041127697401501207 122072164561691546102251811)
  ·
    refine ⟨183108246842537319153377717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122072164561691546102251811 183108246842537319153377717)
    ·
      refine ⟨17166398141487873670629161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183108246842537319153377717 17166398141487873670629161)
      ·
        refine ⟨12874798606115905252971871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17166398141487873670629161 12874798606115905252971871)
        ·
          refine ⟨19312197909173857879457807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12874798606115905252971871 19312197909173857879457807)
          ·
            refine ⟨28968296863760786819186711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19312197909173857879457807 28968296863760786819186711)
            ·
              refine ⟨43452445295641180228780067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28968296863760786819186711 43452445295641180228780067)
              ·
                refine ⟨65178667943461770343170101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43452445295641180228780067 65178667943461770343170101)
                ·
                  refine ⟨6110500119699540969672197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65178667943461770343170101 6110500119699540969672197)
                  ·
                    refine ⟨1145718772443663931813537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6110500119699540969672197 1145718772443663931813537)
                    ·
                      rfl

theorem cell22_3346919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3346919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346919 prefixEnd_3346919 := by exact prefixLift 3346919
  have htrace : WordTrace (prefixWord ++ tailWord_3346919) baseStart_3346919 baseEnd_3346919 := by
    simpa [prefixWord, tailWord_3346919, baseEnd_3346919] using wordTrace_append hprefix tailTrace_3346919
  have hstable : (prefixWord ++ tailWord_3346919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346919).length < 2 ^ (prefixWord ++ tailWord_3346919).sum := by decide
  have hdescent : baseEnd_3346919 < baseStart_3346919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346949 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_3346949 : Nat := 118140960795 + 3346949 * 2 ^ 59
def prefixEnd_3346949 : Nat := 4983230072969 + 3 ^ 40 * 3346949 * 2
def baseEnd_3346949 : Nat := 1145729042056753853563445

theorem tailTrace_3346949 : CollatzResearch.WordTrace tailWord_3346949 prefixEnd_3346949 1145729042056753853563445 := by
  unfold tailWord_3346949
  simp only [CollatzResearch.WordTrace]
  refine ⟨122073258751582861225843901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81382172501055240817229267 122073258751582861225843901)
  ·
    refine ⟨45777472031843572959691463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122073258751582861225843901 45777472031843572959691463)
    ·
      refine ⟨68666208047765359439537195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45777472031843572959691463 68666208047765359439537195)
      ·
        refine ⟨102999312071648039159305793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68666208047765359439537195 102999312071648039159305793)
        ·
          refine ⟨77249484053736029369479345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102999312071648039159305793 77249484053736029369479345)
          ·
            refine ⟨57937113040302022027109509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77249484053736029369479345 57937113040302022027109509)
            ·
              refine ⟨10863208695056629130083033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57937113040302022027109509 10863208695056629130083033)
              ·
                refine ⟨8147406521292471847562275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10863208695056629130083033 8147406521292471847562275)
                ·
                  refine ⟨12221109781938707771343413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8147406521292471847562275 12221109781938707771343413)
                  ·
                    refine ⟨1145729042056753853563445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12221109781938707771343413 1145729042056753853563445)
                    ·
                      rfl

theorem cell22_3346949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_3346949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3346949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3346949 prefixEnd_3346949 := by exact prefixLift 3346949
  have htrace : WordTrace (prefixWord ++ tailWord_3346949) baseStart_3346949 baseEnd_3346949 := by
    simpa [prefixWord, tailWord_3346949, baseEnd_3346949] using wordTrace_append hprefix tailTrace_3346949
  have hstable : (prefixWord ++ tailWord_3346949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346949).length < 2 ^ (prefixWord ++ tailWord_3346949).sum := by decide
  have hdescent : baseEnd_3346949 < baseStart_3346949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347028 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_3347028 : Nat := 118140960795 + 3347028 * 2 ^ 59
def prefixEnd_3347028 : Nat := 4983230072969 + 3 ^ 40 * 3347028 * 2
def baseEnd_3347028 : Nat := 1145756085371223980838203

theorem tailTrace_3347028 : CollatzResearch.WordTrace tailWord_3347028 prefixEnd_3347028 1145756085371223980838203 := by
  unfold tailWord_3347028
  simp only [CollatzResearch.WordTrace]
  refine ⟨61038070059148328858984869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81384093412197771811979825 61038070059148328858984869)
  ·
    refine ⟨11444638136090311661059663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61038070059148328858984869 11444638136090311661059663)
    ·
      refine ⟨17166957204135467491589495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11444638136090311661059663 17166957204135467491589495)
      ·
        refine ⟨25750435806203201237384243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17166957204135467491589495 25750435806203201237384243)
        ·
          refine ⟨38625653709304801856076365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25750435806203201237384243 38625653709304801856076365)
          ·
            refine ⟨14484620140989300696028637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38625653709304801856076365 14484620140989300696028637)
            ·
              refine ⟨5431732552870987761010739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14484620140989300696028637 5431732552870987761010739)
              ·
                refine ⟨8147598829306481641516109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5431732552870987761010739 8147598829306481641516109)
                ·
                  refine ⟨3055349560989930615568541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8147598829306481641516109 3055349560989930615568541)
                  ·
                    refine ⟨1145756085371223980838203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055349560989930615568541 1145756085371223980838203)
                    ·
                      rfl

theorem cell22_3347028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_3347028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347028 prefixEnd_3347028 := by exact prefixLift 3347028
  have htrace : WordTrace (prefixWord ++ tailWord_3347028) baseStart_3347028 baseEnd_3347028 := by
    simpa [prefixWord, tailWord_3347028, baseEnd_3347028] using wordTrace_append hprefix tailTrace_3347028
  have hstable : (prefixWord ++ tailWord_3347028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347028).length < 2 ^ (prefixWord ++ tailWord_3347028).sum := by decide
  have hdescent : baseEnd_3347028 < baseStart_3347028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347039 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 2, 5]
def baseStart_3347039 : Nat := 118140960795 + 3347039 * 2 ^ 59
def prefixEnd_3347039 : Nat := 4983230072969 + 3 ^ 40 * 3347039 * 2
def baseEnd_3347039 : Nat := 1145759850896023618813169

theorem tailTrace_3347039 : CollatzResearch.WordTrace tailWord_3347039 prefixEnd_3347039 1145759850896023618813169 := by
  unfold tailWord_3347039
  simp only [CollatzResearch.WordTrace]
  refine ⟨122076541321256806596620171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81384360880837871064413447 122076541321256806596620171)
  ·
    refine ⟨183114811981885209894930257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122076541321256806596620171 183114811981885209894930257)
    ·
      refine ⟨137336108986413907421197693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183114811981885209894930257 137336108986413907421197693)
      ·
        refine ⟨51501040869905215282949135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137336108986413907421197693 51501040869905215282949135)
        ·
          refine ⟨77251561304857822924423703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51501040869905215282949135 77251561304857822924423703)
          ·
            refine ⟨115877341957286734386635555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77251561304857822924423703 115877341957286734386635555)
            ·
              refine ⟨173816012935930101579953333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115877341957286734386635555 173816012935930101579953333)
              ·
                refine ⟨16295251212743447023120625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173816012935930101579953333 16295251212743447023120625)
                ·
                  refine ⟨12221438409557585267340469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16295251212743447023120625 12221438409557585267340469)
                  ·
                    refine ⟨1145759850896023618813169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12221438409557585267340469 1145759850896023618813169)
                    ·
                      rfl

theorem cell22_3347039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_3347039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347039 prefixEnd_3347039 := by exact prefixLift 3347039
  have htrace : WordTrace (prefixWord ++ tailWord_3347039) baseStart_3347039 baseEnd_3347039 := by
    simpa [prefixWord, tailWord_3347039, baseEnd_3347039] using wordTrace_append hprefix tailTrace_3347039
  have hstable : (prefixWord ++ tailWord_3347039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347039).length < 2 ^ (prefixWord ++ tailWord_3347039).sum := by decide
  have hdescent : baseEnd_3347039 < baseStart_3347039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347041 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 5]
def baseStart_3347041 : Nat := 118140960795 + 3347041 * 2 ^ 59
def prefixEnd_3347041 : Nat := 4983230072969 + 3 ^ 40 * 3347041 * 2
def baseEnd_3347041 : Nat := 381920178512298760087721

theorem tailTrace_3347041 : CollatzResearch.WordTrace tailWord_3347041 prefixEnd_3347041 381920178512298760087721 := by
  unfold tailWord_3347041
  simp only [CollatzResearch.WordTrace]
  refine ⟨122076614267249560938192977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81384409511499707292128651 122076614267249560938192977)
  ·
    refine ⟨91557460700437170703644733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122076614267249560938192977 91557460700437170703644733)
    ·
      refine ⟨34334047762663939013866775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91557460700437170703644733 34334047762663939013866775)
      ·
        refine ⟨51501071643995908520800163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34334047762663939013866775 51501071643995908520800163)
        ·
          refine ⟨77251607465993862781200245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51501071643995908520800163 77251607465993862781200245)
          ·
            refine ⟨7242338199936924635737523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77251607465993862781200245 7242338199936924635737523)
            ·
              refine ⟨10863507299905386953606285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7242338199936924635737523 10863507299905386953606285)
              ·
                refine ⟨4073815237464520107602357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10863507299905386953606285 4073815237464520107602357)
                ·
                  refine ⟨381920178512298760087721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4073815237464520107602357 381920178512298760087721)
                  ·
                    rfl

theorem cell22_3347041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_3347041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347041 prefixEnd_3347041 := by exact prefixLift 3347041
  have htrace : WordTrace (prefixWord ++ tailWord_3347041) baseStart_3347041 baseEnd_3347041 := by
    simpa [prefixWord, tailWord_3347041, baseEnd_3347041] using wordTrace_append hprefix tailTrace_3347041
  have hstable : (prefixWord ++ tailWord_3347041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347041).length < 2 ^ (prefixWord ++ tailWord_3347041).sum := by decide
  have hdescent : baseEnd_3347041 < baseStart_3347041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347086 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_3347086 : Nat := 118140960795 + 3347086 * 2 ^ 59
def prefixEnd_3347086 : Nat := 4983230072969 + 3 ^ 40 * 3347086 * 2
def baseEnd_3347086 : Nat := 381925313318843720962675

theorem tailTrace_3347086 : CollatzResearch.WordTrace tailWord_3347086 prefixEnd_3347086 381925313318843720962675 := by
  unfold tailWord_3347086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15259781944010816702947639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81385503701391022415720741 15259781944010816702947639)
  ·
    refine ⟨22889672916016225054421459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15259781944010816702947639 22889672916016225054421459)
    ·
      refine ⟨34334509374024337581632189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22889672916016225054421459 34334509374024337581632189)
      ·
        refine ⟨12875441015259126593112071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34334509374024337581632189 12875441015259126593112071)
        ·
          refine ⟨19313161522888689889668107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12875441015259126593112071 19313161522888689889668107)
          ·
            refine ⟨28969742284333034834502161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19313161522888689889668107 28969742284333034834502161)
            ·
              refine ⟨21727306713249776125876621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28969742284333034834502161 21727306713249776125876621)
              ·
                refine ⟨8147740017468666047203733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21727306713249776125876621 8147740017468666047203733)
                ·
                  refine ⟨381925313318843720962675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8147740017468666047203733 381925313318843720962675)
                  ·
                    rfl

theorem cell22_3347086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_3347086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347086 prefixEnd_3347086 := by exact prefixLift 3347086
  have htrace : WordTrace (prefixWord ++ tailWord_3347086) baseStart_3347086 baseEnd_3347086 := by
    simpa [prefixWord, tailWord_3347086, baseEnd_3347086] using wordTrace_append hprefix tailTrace_3347086
  have hstable : (prefixWord ++ tailWord_3347086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347086).length < 2 ^ (prefixWord ++ tailWord_3347086).sum := by decide
  have hdescent : baseEnd_3347086 < baseStart_3347086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347101 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_3347101 : Nat := 118140960795 + 3347101 * 2 ^ 59
def prefixEnd_3347101 : Nat := 4983230072969 + 3 ^ 40 * 3347101 * 2
def baseEnd_3347101 : Nat := 1145781074763076123762979

theorem tailTrace_3347101 : CollatzResearch.WordTrace tailWord_3347101 prefixEnd_3347101 1145781074763076123762979 := by
  unfold tailWord_3347101
  simp only [CollatzResearch.WordTrace]
  refine ⟨122078802647032191185377157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81385868431354794123584771 122078802647032191185377157)
  ·
    refine ⟨22889775496318535847258217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122078802647032191185377157 22889775496318535847258217)
    ·
      refine ⟨17167331622238901885443663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22889775496318535847258217 17167331622238901885443663)
      ·
        refine ⟨25750997433358352828165495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17167331622238901885443663 25750997433358352828165495)
        ·
          refine ⟨38626496150037529242248243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25750997433358352828165495 38626496150037529242248243)
          ·
            refine ⟨57939744225056293863372365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38626496150037529242248243 57939744225056293863372365)
            ·
              refine ⟨21727404084396110198764637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57939744225056293863372365 21727404084396110198764637)
              ·
                refine ⟨8147776531648541324536739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21727404084396110198764637 8147776531648541324536739)
                ·
                  refine ⟨12221664797472811986805109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8147776531648541324536739 12221664797472811986805109)
                  ·
                    refine ⟨1145781074763076123762979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12221664797472811986805109 1145781074763076123762979)
                    ·
                      rfl

theorem cell22_3347101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_3347101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347101 prefixEnd_3347101 := by exact prefixLift 3347101
  have htrace : WordTrace (prefixWord ++ tailWord_3347101) baseStart_3347101 baseEnd_3347101 := by
    simpa [prefixWord, tailWord_3347101, baseEnd_3347101] using wordTrace_append hprefix tailTrace_3347101
  have hstable : (prefixWord ++ tailWord_3347101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347101).length < 2 ^ (prefixWord ++ tailWord_3347101).sum := by decide
  have hdescent : baseEnd_3347101 < baseStart_3347101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347135 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 2, 3]
def baseStart_3347135 : Nat := 118140960795 + 3347135 * 2 ^ 59
def prefixEnd_3347135 : Nat := 4983230072969 + 3 ^ 40 * 3347135 * 2
def baseEnd_3347135 : Nat := 1145792713657911368412875

theorem tailTrace_3347135 : CollatzResearch.WordTrace tailWord_3347135 prefixEnd_3347135 1145792713657911368412875 := by
  unfold tailWord_3347135
  simp only [CollatzResearch.WordTrace]
  refine ⟨122080042728909014992114859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81386695152606009994743239 122080042728909014992114859)
  ·
    refine ⟨183120064093363522488172289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122080042728909014992114859 183120064093363522488172289)
    ·
      refine ⟨137340048070022641866129217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183120064093363522488172289 137340048070022641866129217)
      ·
        refine ⟨103005036052516981399596913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137340048070022641866129217 103005036052516981399596913)
        ·
          refine ⟨77253777039387736049697685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103005036052516981399596913 77253777039387736049697685)
          ·
            refine ⟨3621270798721300127329579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77253777039387736049697685 3621270798721300127329579)
            ·
              refine ⟨5431906198081950190994369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3621270798721300127329579 5431906198081950190994369)
              ·
                refine ⟨4073929648561462643245777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5431906198081950190994369 4073929648561462643245777)
                ·
                  refine ⟨3055447236421096982434333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4073929648561462643245777 3055447236421096982434333)
                  ·
                    refine ⟨1145792713657911368412875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055447236421096982434333 1145792713657911368412875)
                    ·
                      rfl

theorem cell22_3347135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 3].length) (baseStart_3347135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347135 prefixEnd_3347135 := by exact prefixLift 3347135
  have htrace : WordTrace (prefixWord ++ tailWord_3347135) baseStart_3347135 baseEnd_3347135 := by
    simpa [prefixWord, tailWord_3347135, baseEnd_3347135] using wordTrace_append hprefix tailTrace_3347135
  have hstable : (prefixWord ++ tailWord_3347135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347135).length < 2 ^ (prefixWord ++ tailWord_3347135).sum := by decide
  have hdescent : baseEnd_3347135 < baseStart_3347135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347197 : List Nat := [1, 4, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_3347197 : Nat := 118140960795 + 3347197 * 2 ^ 59
def prefixEnd_3347197 : Nat := 4983230072969 + 3 ^ 40 * 3347197 * 2
def baseEnd_3347197 : Nat := 1145813937524963873362685

theorem tailTrace_3347197 : CollatzResearch.WordTrace tailWord_3347197 prefixEnd_3347197 1145813937524963873362685 := by
  unfold tailWord_3347197
  simp only [CollatzResearch.WordTrace]
  refine ⟨122082304054684399580871845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81388202703122933053914563 122082304054684399580871845)
  ·
    refine ⟨22890432010253324921413471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122082304054684399580871845 22890432010253324921413471)
    ·
      refine ⟨34335648015379987382120207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22890432010253324921413471 34335648015379987382120207)
      ·
        refine ⟨51503472023069981073180311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34335648015379987382120207 51503472023069981073180311)
        ·
          refine ⟨77255208034604971609770467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51503472023069981073180311 77255208034604971609770467)
          ·
            refine ⟨115882812051907457414655701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77255208034604971609770467 115882812051907457414655701)
            ·
              refine ⟨2716003407466581033155993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 115882812051907457414655701 2716003407466581033155993)
              ·
                refine ⟨2037002555599935774866995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716003407466581033155993 2037002555599935774866995)
                ·
                  refine ⟨3055503833399903662300493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037002555599935774866995 3055503833399903662300493)
                  ·
                    refine ⟨1145813937524963873362685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055503833399903662300493 1145813937524963873362685)
                    ·
                      rfl

theorem cell22_3347197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_3347197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347197 prefixEnd_3347197 := by exact prefixLift 3347197
  have htrace : WordTrace (prefixWord ++ tailWord_3347197) baseStart_3347197 baseEnd_3347197 := by
    simpa [prefixWord, tailWord_3347197, baseEnd_3347197] using wordTrace_append hprefix tailTrace_3347197
  have hstable : (prefixWord ++ tailWord_3347197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347197).length < 2 ^ (prefixWord ++ tailWord_3347197).sum := by decide
  have hdescent : baseEnd_3347197 < baseStart_3347197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347221 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 8]
def baseStart_3347221 : Nat := 118140960795 + 3347221 * 2 ^ 59
def prefixEnd_3347221 : Nat := 4983230072969 + 3 ^ 40 * 3347221 * 2
def baseEnd_3347221 : Nat := 381940717738478603587537

theorem tailTrace_3347221 : CollatzResearch.WordTrace tailWord_3347221 prefixEnd_3347221 381940717738478603587537 := by
  unfold tailWord_3347221
  simp only [CollatzResearch.WordTrace]
  refine ⟨122083179406597451679745517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81388786271064967786497011 122083179406597451679745517)
  ·
    refine ⟨45781192277474044379904569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122083179406597451679745517 45781192277474044379904569)
    ·
      refine ⟨34335894208105533284928427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45781192277474044379904569 34335894208105533284928427)
      ·
        refine ⟨51503841312158299927392641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34335894208105533284928427 51503841312158299927392641)
        ·
          refine ⟨38627880984118724945544481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51503841312158299927392641 38627880984118724945544481)
          ·
            refine ⟨28970910738089043709158361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38627880984118724945544481 28970910738089043709158361)
            ·
              refine ⟨21728183053566782781868771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28970910738089043709158361 21728183053566782781868771)
              ·
                refine ⟨32592274580350174172803157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21728183053566782781868771 32592274580350174172803157)
                ·
                  refine ⟨381940717738478603587537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32592274580350174172803157 381940717738478603587537)
                  ·
                    rfl

theorem cell22_3347221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_3347221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347221 prefixEnd_3347221 := by exact prefixLift 3347221
  have htrace : WordTrace (prefixWord ++ tailWord_3347221) baseStart_3347221 baseEnd_3347221 := by
    simpa [prefixWord, tailWord_3347221, baseEnd_3347221] using wordTrace_append hprefix tailTrace_3347221
  have hstable : (prefixWord ++ tailWord_3347221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347221).length < 2 ^ (prefixWord ++ tailWord_3347221).sum := by decide
  have hdescent : baseEnd_3347221 < baseStart_3347221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347349 : List Nat := [1, 3, 2, 1, 1, 6, 1, 3, 1, 3]
def baseStart_3347349 : Nat := 118140960795 + 3347349 * 2 ^ 59
def prefixEnd_3347349 : Nat := 4983230072969 + 3 ^ 40 * 3347349 * 2
def baseEnd_3347349 : Nat := 1145865970231286143562219

theorem tailTrace_3347349 : CollatzResearch.WordTrace tailWord_3347349 prefixEnd_3347349 1145865970231286143562219 := by
  unfold tailWord_3347349
  simp only [CollatzResearch.WordTrace]
  refine ⟨122087847950133729540405101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81391898633422486360270067 122087847950133729540405101)
  ·
    refine ⟨45782942981300148577651913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122087847950133729540405101 45782942981300148577651913)
    ·
      refine ⟨34337207235975111433238935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45782942981300148577651913 34337207235975111433238935)
      ·
        refine ⟨51505810853962667149858403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34337207235975111433238935 51505810853962667149858403)
        ·
          refine ⟨77258716280944000724787605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51505810853962667149858403 77258716280944000724787605)
          ·
            refine ⟨3621502325669250033974419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77258716280944000724787605 3621502325669250033974419)
            ·
              refine ⟨5432253488503875050961629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3621502325669250033974419 5432253488503875050961629)
              ·
                refine ⟨2037095058188953144110611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5432253488503875050961629 2037095058188953144110611)
                ·
                  refine ⟨3055642587283429716165917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037095058188953144110611 3055642587283429716165917)
                  ·
                    refine ⟨1145865970231286143562219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055642587283429716165917 1145865970231286143562219)
                    ·
                      rfl

theorem cell22_3347349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_3347349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347349 prefixEnd_3347349 := by exact prefixLift 3347349
  have htrace : WordTrace (prefixWord ++ tailWord_3347349) baseStart_3347349 baseEnd_3347349 := by
    simpa [prefixWord, tailWord_3347349, baseEnd_3347349] using wordTrace_append hprefix tailTrace_3347349
  have hstable : (prefixWord ++ tailWord_3347349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347349).length < 2 ^ (prefixWord ++ tailWord_3347349).sum := by decide
  have hdescent : baseEnd_3347349 < baseStart_3347349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347392 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 1, 4]
def baseStart_3347392 : Nat := 118140960795 + 3347392 * 2 ^ 59
def prefixEnd_3347392 : Nat := 4983230072969 + 3 ^ 40 * 3347392 * 2
def baseEnd_3347392 : Nat := 1145880690010048364737087

theorem tailTrace_3347392 : CollatzResearch.WordTrace tailWord_3347392 prefixEnd_3347392 1145880690010048364737087 := by
  unfold tailWord_3347392
  simp only [CollatzResearch.WordTrace]
  refine ⟨61044708144488973942110215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81392944192651965256146953 61044708144488973942110215)
  ·
    refine ⟨91567062216733460913165323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61044708144488973942110215 91567062216733460913165323)
    ·
      refine ⟨137350593325100191369747985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91567062216733460913165323 137350593325100191369747985)
      ·
        refine ⟨103012944993825143527310989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137350593325100191369747985 103012944993825143527310989)
        ·
          refine ⟨38629854372684428822741621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103012944993825143527310989 38629854372684428822741621)
          ·
            refine ⟨3621548847439165202132027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38629854372684428822741621 3621548847439165202132027)
            ·
              refine ⟨5432323271158747803198041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3621548847439165202132027 5432323271158747803198041)
              ·
                refine ⟨4074242453369060852398531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5432323271158747803198041 4074242453369060852398531)
                ·
                  refine ⟨6111363680053591278597797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074242453369060852398531 6111363680053591278597797)
                  ·
                    refine ⟨1145880690010048364737087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6111363680053591278597797 1145880690010048364737087)
                    ·
                      rfl

theorem cell22_3347392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 4].length) (baseStart_3347392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347392 prefixEnd_3347392 := by exact prefixLift 3347392
  have htrace : WordTrace (prefixWord ++ tailWord_3347392) baseStart_3347392 baseEnd_3347392 := by
    simpa [prefixWord, tailWord_3347392, baseEnd_3347392] using wordTrace_append hprefix tailTrace_3347392
  have hstable : (prefixWord ++ tailWord_3347392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347392).length < 2 ^ (prefixWord ++ tailWord_3347392).sum := by decide
  have hdescent : baseEnd_3347392 < baseStart_3347392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347418 : List Nat := [3, 1, 1, 2, 4, 11]
def baseStart_3347418 : Nat := 118140960795 + 3347418 * 2 ^ 59
def prefixEnd_3347418 : Nat := 4983230072969 + 3 ^ 40 * 3347418 * 2
def baseEnd_3347418 : Nat := 14146785065943123007247

theorem tailTrace_3347418 : CollatzResearch.WordTrace tailWord_3347418 prefixEnd_3347418 14146785065943123007247 := by
  unfold tailWord_3347418
  simp only [CollatzResearch.WordTrace]
  refine ⟨30522591146720938581166727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81393576391255836216444605 30522591146720938581166727)
  ·
    refine ⟨45783886720081407871750091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30522591146720938581166727 45783886720081407871750091)
    ·
      refine ⟨68675830080122111807625137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45783886720081407871750091 68675830080122111807625137)
      ·
        refine ⟨51506872560091583855718853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68675830080122111807625137 51506872560091583855718853)
        ·
          refine ⟨9657538605017171972947285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51506872560091583855718853 9657538605017171972947285)
          ·
            refine ⟨14146785065943123007247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9657538605017171972947285 14146785065943123007247)
            ·
              rfl

theorem cell22_3347418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 11].length) (baseStart_3347418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347418 prefixEnd_3347418 := by exact prefixLift 3347418
  have htrace : WordTrace (prefixWord ++ tailWord_3347418) baseStart_3347418 baseEnd_3347418 := by
    simpa [prefixWord, tailWord_3347418, baseEnd_3347418] using wordTrace_append hprefix tailTrace_3347418
  have hstable : (prefixWord ++ tailWord_3347418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347418).length < 2 ^ (prefixWord ++ tailWord_3347418).sum := by decide
  have hdescent : baseEnd_3347418 < baseStart_3347418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347448 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_3347448 : Nat := 118140960795 + 3347448 * 2 ^ 59
def prefixEnd_3347448 : Nat := 4983230072969 + 3 ^ 40 * 3347448 * 2
def baseEnd_3347448 : Nat := 1145899859954482885336915

theorem tailTrace_3347448 : CollatzResearch.WordTrace tailWord_3347448 prefixEnd_3347448 1145899859954482885336915 := by
  unfold tailWord_3347448
  simp only [CollatzResearch.WordTrace]
  refine ⟨61045729388387534724129499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81394305851183379632172665 61045729388387534724129499)
  ·
    refine ⟨91568594082581302086194249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61045729388387534724129499 91568594082581302086194249)
    ·
      refine ⟨68676445561935976564645687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91568594082581302086194249 68676445561935976564645687)
      ·
        refine ⟨103014668342903964846968531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68676445561935976564645687 103014668342903964846968531)
        ·
          refine ⟨154522002514355947270452797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103014668342903964846968531 154522002514355947270452797)
          ·
            refine ⟨57945750942883480226419799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154522002514355947270452797 57945750942883480226419799)
            ·
              refine ⟨86918626414325220339629699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57945750942883480226419799 86918626414325220339629699)
              ·
                refine ⟨130377939621487830509444549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86918626414325220339629699 130377939621487830509444549)
                ·
                  refine ⟨24445863679028968220520853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130377939621487830509444549 24445863679028968220520853)
                  ·
                    refine ⟨1145899859954482885336915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24445863679028968220520853 1145899859954482885336915)
                    ·
                      rfl

theorem cell22_3347448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_3347448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347448 prefixEnd_3347448 := by exact prefixLift 3347448
  have htrace : WordTrace (prefixWord ++ tailWord_3347448) baseStart_3347448 baseEnd_3347448 := by
    simpa [prefixWord, tailWord_3347448, baseEnd_3347448] using wordTrace_append hprefix tailTrace_3347448
  have hstable : (prefixWord ++ tailWord_3347448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347448).length < 2 ^ (prefixWord ++ tailWord_3347448).sum := by decide
  have hdescent : baseEnd_3347448 < baseStart_3347448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347480 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 7]
def baseStart_3347480 : Nat := 118140960795 + 3347480 * 2 ^ 59
def prefixEnd_3347480 : Nat := 4983230072969 + 3 ^ 40 * 3347480 * 2
def baseEnd_3347480 : Nat := 381970271402815156178939

theorem tailTrace_3347480 : CollatzResearch.WordTrace tailWord_3347480 prefixEnd_3347480 381970271402815156178939 := by
  unfold tailWord_3347480
  simp only [CollatzResearch.WordTrace]
  refine ⟨61046312956329569456711947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81395083941772759275615929 61046312956329569456711947)
  ·
    refine ⟨91569469434494354185067921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61046312956329569456711947 91569469434494354185067921)
    ·
      refine ⟨68677102075870765638800941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91569469434494354185067921 68677102075870765638800941)
      ·
        refine ⟨25753913278451537114550353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68677102075870765638800941 25753913278451537114550353)
        ·
          refine ⟨19315434958838652835912765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25753913278451537114550353 19315434958838652835912765)
          ·
            refine ⟨7243288109564494813467287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19315434958838652835912765 7243288109564494813467287)
            ·
              refine ⟨10864932164346742220200931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243288109564494813467287 10864932164346742220200931)
              ·
                refine ⟨16297398246520113330301397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10864932164346742220200931 16297398246520113330301397)
                ·
                  refine ⟨381970271402815156178939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16297398246520113330301397 381970271402815156178939)
                  ·
                    rfl

theorem cell22_3347480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_3347480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347480 prefixEnd_3347480 := by exact prefixLift 3347480
  have htrace : WordTrace (prefixWord ++ tailWord_3347480) baseStart_3347480 baseEnd_3347480 := by
    simpa [prefixWord, tailWord_3347480, baseEnd_3347480] using wordTrace_append hprefix tailTrace_3347480
  have hstable : (prefixWord ++ tailWord_3347480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347480).length < 2 ^ (prefixWord ++ tailWord_3347480).sum := by decide
  have hdescent : baseEnd_3347480 < baseStart_3347480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347484 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 3, 3]
def baseStart_3347484 : Nat := 118140960795 + 3347484 * 2 ^ 59
def prefixEnd_3347484 : Nat := 4983230072969 + 3 ^ 40 * 3347484 * 2
def baseEnd_3347484 : Nat := 1145912183490190791436805

theorem tailTrace_3347484 : CollatzResearch.WordTrace tailWord_3347484 prefixEnd_3347484 1145912183490190791436805 := by
  unfold tailWord_3347484
  simp only [CollatzResearch.WordTrace]
  refine ⟨61046385902322323798284753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81395181203096431731046337 61046385902322323798284753)
  ·
    refine ⟨45784789426741742848713565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61046385902322323798284753 45784789426741742848713565)
    ·
      refine ⟨17169296035028153568267587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45784789426741742848713565 17169296035028153568267587)
      ·
        refine ⟨25753944052542230352401381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17169296035028153568267587 25753944052542230352401381)
        ·
          refine ⟨4828864509851668191075259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25753944052542230352401381 4828864509851668191075259)
          ·
            refine ⟨7243296764777502286612889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828864509851668191075259 7243296764777502286612889)
            ·
              refine ⟨5432472573583126714959667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7243296764777502286612889 5432472573583126714959667)
              ·
                refine ⟨8148708860374690072439501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5432472573583126714959667 8148708860374690072439501)
                ·
                  refine ⟨3055765822640508777164813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8148708860374690072439501 3055765822640508777164813)
                  ·
                    refine ⟨1145912183490190791436805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055765822640508777164813 1145912183490190791436805)
                    ·
                      rfl

theorem cell22_3347484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_3347484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347484 prefixEnd_3347484 := by exact prefixLift 3347484
  have htrace : WordTrace (prefixWord ++ tailWord_3347484) baseStart_3347484 baseEnd_3347484 := by
    simpa [prefixWord, tailWord_3347484, baseEnd_3347484] using wordTrace_append hprefix tailTrace_3347484
  have hstable : (prefixWord ++ tailWord_3347484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347484).length < 2 ^ (prefixWord ++ tailWord_3347484).sum := by decide
  have hdescent : baseEnd_3347484 < baseStart_3347484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347518 : List Nat := [4, 2, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_3347518 : Nat := 118140960795 + 3347518 * 2 ^ 59
def prefixEnd_3347518 : Nat := 4983230072969 + 3 ^ 40 * 3347518 * 2
def baseEnd_3347518 : Nat := 1145923822385026036086701

theorem tailTrace_3347518 : CollatzResearch.WordTrace tailWord_3347518 prefixEnd_3347518 1145923822385026036086701 := by
  unfold tailWord_3347518
  simp only [CollatzResearch.WordTrace]
  refine ⟨15261751485815183925413401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81396007924347647602204805 15261751485815183925413401)
  ·
    refine ⟨11446313614361387944060051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15261751485815183925413401 11446313614361387944060051)
    ·
      refine ⟨17169470421542081916090077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11446313614361387944060051 17169470421542081916090077)
      ·
        refine ⟨6438551408078280718533779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17169470421542081916090077 6438551408078280718533779)
        ·
          refine ⟨9657827112117421077800669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6438551408078280718533779 9657827112117421077800669)
          ·
            refine ⟨3621685167044032904175251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9657827112117421077800669 3621685167044032904175251)
            ·
              refine ⟨5432527750566049356262877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3621685167044032904175251 5432527750566049356262877)
              ·
                refine ⟨2037197906462268508598579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5432527750566049356262877 2037197906462268508598579)
                ·
                  refine ⟨3055796859693402762897869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037197906462268508598579 3055796859693402762897869)
                  ·
                    refine ⟨1145923822385026036086701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055796859693402762897869 1145923822385026036086701)
                    ·
                      rfl

theorem cell22_3347518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_3347518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347518 prefixEnd_3347518 := by exact prefixLift 3347518
  have htrace : WordTrace (prefixWord ++ tailWord_3347518) baseStart_3347518 baseEnd_3347518 := by
    simpa [prefixWord, tailWord_3347518, baseEnd_3347518] using wordTrace_append hprefix tailTrace_3347518
  have hstable : (prefixWord ++ tailWord_3347518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347518).length < 2 ^ (prefixWord ++ tailWord_3347518).sum := by decide
  have hdescent : baseEnd_3347518 < baseStart_3347518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347527 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 1, 4]
def baseStart_3347527 : Nat := 118140960795 + 3347527 * 2 ^ 59
def prefixEnd_3347527 : Nat := 4983230072969 + 3 ^ 40 * 3347527 * 2
def baseEnd_3347527 : Nat := 1145926903268953012611673

theorem tailTrace_3347527 : CollatzResearch.WordTrace tailWord_3347527 prefixEnd_3347527 1145926903268953012611673 := by
  unfold tailWord_3347527
  simp only [CollatzResearch.WordTrace]
  refine ⟨122094340143488865940384835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81396226762325910626923223 122094340143488865940384835)
  ·
    refine ⟨183141510215233298910577253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122094340143488865940384835 183141510215233298910577253)
    ·
      refine ⟨34339033165356243545733235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183141510215233298910577253 34339033165356243545733235)
      ·
        refine ⟨51508549748034365318599853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34339033165356243545733235 51508549748034365318599853)
        ·
          refine ⟨19315706155512886994474945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51508549748034365318599853 19315706155512886994474945)
          ·
            refine ⟨14486779616634665245856209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19315706155512886994474945 14486779616634665245856209)
            ·
              refine ⟨10865084712475998934392157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14486779616634665245856209 10865084712475998934392157)
              ·
                refine ⟨4074406767178499600397059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10865084712475998934392157 4074406767178499600397059)
                ·
                  refine ⟨6111610150767749400595589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074406767178499600397059 6111610150767749400595589)
                  ·
                    refine ⟨1145926903268953012611673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6111610150767749400595589 1145926903268953012611673)
                    ·
                      rfl

theorem cell22_3347527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_3347527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347527 prefixEnd_3347527 := by exact prefixLift 3347527
  have htrace : WordTrace (prefixWord ++ tailWord_3347527) baseStart_3347527 baseEnd_3347527 := by
    simpa [prefixWord, tailWord_3347527, baseEnd_3347527] using wordTrace_append hprefix tailTrace_3347527
  have hstable : (prefixWord ++ tailWord_3347527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347527).length < 2 ^ (prefixWord ++ tailWord_3347527).sum := by decide
  have hdescent : baseEnd_3347527 < baseStart_3347527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347555 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 6, 4]
def baseStart_3347555 : Nat := 118140960795 + 3347555 * 2 ^ 59
def prefixEnd_3347555 : Nat := 4983230072969 + 3 ^ 40 * 3347555 * 2
def baseEnd_3347555 : Nat := 1145936488241170272911587

theorem tailTrace_3347555 : CollatzResearch.WordTrace tailWord_3347555 prefixEnd_3347555 1145936488241170272911587 := by
  unfold tailWord_3347555
  simp only [CollatzResearch.WordTrace]
  refine ⟨122095361387387426722404119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81396907591591617814936079 122095361387387426722404119)
  ·
    refine ⟨183143042081081140083606179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122095361387387426722404119 183143042081081140083606179)
    ·
      refine ⟨274714563121621710125409269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183143042081081140083606179 274714563121621710125409269)
      ·
        refine ⟨25754490292652035324257119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 274714563121621710125409269 25754490292652035324257119)
        ·
          refine ⟨38631735438978052986385679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25754490292652035324257119 38631735438978052986385679)
          ·
            refine ⟨57947603158467079479578519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38631735438978052986385679 57947603158467079479578519)
            ·
              refine ⟨86921404737700619219367779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57947603158467079479578519 86921404737700619219367779)
              ·
                refine ⟨130382107106550928829051669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86921404737700619219367779 130382107106550928829051669)
                ·
                  refine ⟨6111661270619574788861797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130382107106550928829051669 6111661270619574788861797)
                  ·
                    refine ⟨1145936488241170272911587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6111661270619574788861797 1145936488241170272911587)
                    ·
                      rfl

theorem cell22_3347555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 4].length) (baseStart_3347555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347555 prefixEnd_3347555 := by exact prefixLift 3347555
  have htrace : WordTrace (prefixWord ++ tailWord_3347555) baseStart_3347555 baseEnd_3347555 := by
    simpa [prefixWord, tailWord_3347555, baseEnd_3347555] using wordTrace_append hprefix tailTrace_3347555
  have hstable : (prefixWord ++ tailWord_3347555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347555).length < 2 ^ (prefixWord ++ tailWord_3347555).sum := by decide
  have hdescent : baseEnd_3347555 < baseStart_3347555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347570 : List Nat := [3, 2, 1, 2, 2, 1, 1, 10]
def baseStart_3347570 : Nat := 118140960795 + 3347570 * 2 ^ 59
def prefixEnd_3347570 : Nat := 4983230072969 + 3 ^ 40 * 3347570 * 2
def baseEnd_3347570 : Nat := 127326847005301692642949

theorem tailTrace_3347570 : CollatzResearch.WordTrace tailWord_3347570 prefixEnd_3347570 127326847005301692642949 := by
  unfold tailWord_3347570
  simp only [CollatzResearch.WordTrace]
  refine ⟨30523977120583271071050041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81397272321555389522800109 30523977120583271071050041)
  ·
    refine ⟨22892982840437453303287531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30523977120583271071050041 22892982840437453303287531)
    ·
      refine ⟨34339474260656179954931297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22892982840437453303287531 34339474260656179954931297)
      ·
        refine ⟨25754605695492134966198473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34339474260656179954931297 25754605695492134966198473)
        ·
          refine ⟨19315954271619101224648855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25754605695492134966198473 19315954271619101224648855)
          ·
            refine ⟨28973931407428651836973283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19315954271619101224648855 28973931407428651836973283)
            ·
              refine ⟨43460897111142977755459925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28973931407428651836973283 43460897111142977755459925)
              ·
                refine ⟨127326847005301692642949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43460897111142977755459925 127326847005301692642949)
                ·
                  rfl

theorem cell22_3347570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_3347570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347570 prefixEnd_3347570 := by exact prefixLift 3347570
  have htrace : WordTrace (prefixWord ++ tailWord_3347570) baseStart_3347570 baseEnd_3347570 := by
    simpa [prefixWord, tailWord_3347570, baseEnd_3347570] using wordTrace_append hprefix tailTrace_3347570
  have hstable : (prefixWord ++ tailWord_3347570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347570).length < 2 ^ (prefixWord ++ tailWord_3347570).sum := by decide
  have hdescent : baseEnd_3347570 < baseStart_3347570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347649 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 7]
def baseStart_3347649 : Nat := 118140960795 + 3347649 * 2 ^ 59
def prefixEnd_3347649 : Nat := 4983230072969 + 3 ^ 40 * 3347649 * 2
def baseEnd_3347649 : Nat := 381989555454061787020433

theorem tailTrace_3347649 : CollatzResearch.WordTrace tailWord_3347649 prefixEnd_3347649 381989555454061787020433 := by
  unfold tailWord_3347649
  simp only [CollatzResearch.WordTrace]
  refine ⟨122098789849046880776326001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81399193232697920517550667 122098789849046880776326001)
  ·
    refine ⟨91574092386785160582244501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122098789849046880776326001 91574092386785160582244501)
    ·
      refine ⟨4292535580630554402292711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91574092386785160582244501 4292535580630554402292711)
      ·
        refine ⟨6438803370945831603439067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4292535580630554402292711 6438803370945831603439067)
        ·
          refine ⟨9658205056418747405158601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6438803370945831603439067 9658205056418747405158601)
          ·
            refine ⟨7243653792314060553868951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9658205056418747405158601 7243653792314060553868951)
            ·
              refine ⟨10865480688471090830803427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243653792314060553868951 10865480688471090830803427)
              ·
                refine ⟨16298221032706636246205141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10865480688471090830803427 16298221032706636246205141)
                ·
                  refine ⟨381989555454061787020433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16298221032706636246205141 381989555454061787020433)
                  ·
                    rfl

theorem cell22_3347649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_3347649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347649 prefixEnd_3347649 := by exact prefixLift 3347649
  have htrace : WordTrace (prefixWord ++ tailWord_3347649) baseStart_3347649 baseEnd_3347649 := by
    simpa [prefixWord, tailWord_3347649, baseEnd_3347649] using wordTrace_append hprefix tailTrace_3347649
  have hstable : (prefixWord ++ tailWord_3347649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347649).length < 2 ^ (prefixWord ++ tailWord_3347649).sum := by decide
  have hdescent : baseEnd_3347649 < baseStart_3347649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347711 : List Nat := [1, 1, 2, 2, 1, 6, 3, 2, 4]
def baseStart_3347711 : Nat := 118140960795 + 3347711 * 2 ^ 59
def prefixEnd_3347711 : Nat := 4983230072969 + 3 ^ 40 * 3347711 * 2
def baseEnd_3347711 : Nat := 381996630076412622003703

theorem tailTrace_3347711 : CollatzResearch.WordTrace tailWord_3347711 prefixEnd_3347711 381996630076412622003703 := by
  unfold tailWord_3347711
  simp only [CollatzResearch.WordTrace]
  refine ⟨122101051174822265365082987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81400700783214843576721991 122101051174822265365082987)
  ·
    refine ⟨183151576762233398047624481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122101051174822265365082987 183151576762233398047624481)
    ·
      refine ⟨137363682571675048535718361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183151576762233398047624481 137363682571675048535718361)
      ·
        refine ⟨103022761928756286401788771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137363682571675048535718361 103022761928756286401788771)
        ·
          refine ⟨154534142893134429602683157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103022761928756286401788771 154534142893134429602683157)
          ·
            refine ⟨7243787948115676387625773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154534142893134429602683157 7243787948115676387625773)
            ·
              refine ⟨2716420480543378645359665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7243787948115676387625773 2716420480543378645359665)
              ·
                refine ⟨2037315360407533984019749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716420480543378645359665 2037315360407533984019749)
                ·
                  refine ⟨381996630076412622003703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2037315360407533984019749 381996630076412622003703)
                  ·
                    rfl

theorem cell22_3347711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 4].length) (baseStart_3347711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347711 prefixEnd_3347711 := by exact prefixLift 3347711
  have htrace : WordTrace (prefixWord ++ tailWord_3347711) baseStart_3347711 baseEnd_3347711 := by
    simpa [prefixWord, tailWord_3347711, baseEnd_3347711] using wordTrace_append hprefix tailTrace_3347711
  have hstable : (prefixWord ++ tailWord_3347711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347711).length < 2 ^ (prefixWord ++ tailWord_3347711).sum := by decide
  have hdescent : baseEnd_3347711 < baseStart_3347711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347726 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_3347726 : Nat := 118140960795 + 3347726 * 2 ^ 59
def prefixEnd_3347726 : Nat := 4983230072969 + 3 ^ 40 * 3347726 * 2
def baseEnd_3347726 : Nat := 1145995025035782826886063

theorem tailTrace_3347726 : CollatzResearch.WordTrace tailWord_3347726 prefixEnd_3347726 1145995025035782826886063 := by
  unfold tailWord_3347726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15262699783720990365859879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81401065513178615284586021 15262699783720990365859879)
  ·
    refine ⟨22894049675581485548789819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15262699783720990365859879 22894049675581485548789819)
    ·
      refine ⟨34341074513372228323184729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22894049675581485548789819 34341074513372228323184729)
      ·
        refine ⟨25755805885029171242388547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34341074513372228323184729 25755805885029171242388547)
        ·
          refine ⟨38633708827543756863582821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25755805885029171242388547 38633708827543756863582821)
          ·
            refine ⟨7243820405164454411921779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38633708827543756863582821 7243820405164454411921779)
            ·
              refine ⟨10865730607746681617882669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243820405164454411921779 10865730607746681617882669)
              ·
                refine ⟨4074648977905005606706001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10865730607746681617882669 4074648977905005606706001)
                ·
                  refine ⟨3055986733428754205029501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4074648977905005606706001 3055986733428754205029501)
                  ·
                    refine ⟨1145995025035782826886063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3055986733428754205029501 1145995025035782826886063)
                    ·
                      rfl

theorem cell22_3347726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_3347726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347726 prefixEnd_3347726 := by exact prefixLift 3347726
  have htrace : WordTrace (prefixWord ++ tailWord_3347726) baseStart_3347726 baseEnd_3347726 := by
    simpa [prefixWord, tailWord_3347726, baseEnd_3347726] using wordTrace_append hprefix tailTrace_3347726
  have hstable : (prefixWord ++ tailWord_3347726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347726).length < 2 ^ (prefixWord ++ tailWord_3347726).sum := by decide
  have hdescent : baseEnd_3347726 < baseStart_3347726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347730 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3347730 : Nat := 118140960795 + 3347730 * 2 ^ 59
def prefixEnd_3347730 : Nat := 4983230072969 + 3 ^ 40 * 3347730 * 2
def baseEnd_3347730 : Nat := 1145996394317528149786051

theorem tailTrace_3347730 : CollatzResearch.WordTrace tailWord_3347730 prefixEnd_3347730 1145996394317528149786051 := by
  unfold tailWord_3347730
  simp only [CollatzResearch.WordTrace]
  refine ⟨30525436040438357902506161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81401162774502287740016429 30525436040438357902506161)
  ·
    refine ⟨22894077030328768426879621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30525436040438357902506161 22894077030328768426879621)
    ·
      refine ⟨4292639443186644080039929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22894077030328768426879621 4292639443186644080039929)
      ·
        refine ⟨3219479582389983060029947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4292639443186644080039929 3219479582389983060029947)
        ·
          refine ⟨4829219373584974590044921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3219479582389983060029947 4829219373584974590044921)
          ·
            refine ⟨3621914530188730942533691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4829219373584974590044921 3621914530188730942533691)
            ·
              refine ⟨5432871795283096413800537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3621914530188730942533691 5432871795283096413800537)
              ·
                refine ⟨4074653846462322310350403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5432871795283096413800537 4074653846462322310350403)
                ·
                  refine ⟨6111980769693483465525605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074653846462322310350403 6111980769693483465525605)
                  ·
                    refine ⟨1145996394317528149786051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6111980769693483465525605 1145996394317528149786051)
                    ·
                      rfl

theorem cell22_3347730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3347730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347730 prefixEnd_3347730 := by exact prefixLift 3347730
  have htrace : WordTrace (prefixWord ++ tailWord_3347730) baseStart_3347730 baseEnd_3347730 := by
    simpa [prefixWord, tailWord_3347730, baseEnd_3347730] using wordTrace_append hprefix tailTrace_3347730
  have hstable : (prefixWord ++ tailWord_3347730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347730).length < 2 ^ (prefixWord ++ tailWord_3347730).sum := by decide
  have hdescent : baseEnd_3347730 < baseStart_3347730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347741 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_3347741 : Nat := 118140960795 + 3347741 * 2 ^ 59
def prefixEnd_3347741 : Nat := 4983230072969 + 3 ^ 40 * 3347741 * 2
def baseEnd_3347741 : Nat := 1146000159842327787761017

theorem tailTrace_3347741 : CollatzResearch.WordTrace tailWord_3347741 prefixEnd_3347741 1146000159842327787761017 := by
  unfold tailWord_3347741
  simp only [CollatzResearch.WordTrace]
  refine ⟨122102145364713580488675077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81401430243142386992450051 122102145364713580488675077)
  ·
    refine ⟨22894152255883796341626577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122102145364713580488675077 22894152255883796341626577)
    ·
      refine ⟨17170614191912847256219933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22894152255883796341626577 17170614191912847256219933)
      ·
        refine ⟨6438980321967317721082475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17170614191912847256219933 6438980321967317721082475)
        ·
          refine ⟨9658470482950976581623713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6438980321967317721082475 9658470482950976581623713)
          ·
            refine ⟨7243852862213232436217785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9658470482950976581623713 7243852862213232436217785)
            ·
              refine ⟨5432889646659924327163339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7243852862213232436217785 5432889646659924327163339)
              ·
                refine ⟨8149334469989886490745009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5432889646659924327163339 8149334469989886490745009)
                ·
                  refine ⟨6112000852492414868058757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8149334469989886490745009 6112000852492414868058757)
                  ·
                    refine ⟨1146000159842327787761017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6112000852492414868058757 1146000159842327787761017)
                    ·
                      rfl

theorem cell22_3347741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_3347741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347741 prefixEnd_3347741 := by exact prefixLift 3347741
  have htrace : WordTrace (prefixWord ++ tailWord_3347741) baseStart_3347741 baseEnd_3347741 := by
    simpa [prefixWord, tailWord_3347741, baseEnd_3347741] using wordTrace_append hprefix tailTrace_3347741
  have hstable : (prefixWord ++ tailWord_3347741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347741).length < 2 ^ (prefixWord ++ tailWord_3347741).sum := by decide
  have hdescent : baseEnd_3347741 < baseStart_3347741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347773 : List Nat := [1, 4, 1, 5, 2, 1, 1, 7]
def baseStart_3347773 : Nat := 118140960795 + 3347773 * 2 ^ 59
def prefixEnd_3347773 : Nat := 4983230072969 + 3 ^ 40 * 3347773 * 2
def baseEnd_3347773 : Nat := 127334568232921152328991

theorem tailTrace_3347773 : CollatzResearch.WordTrace tailWord_3347773 prefixEnd_3347773 127334568232921152328991 := by
  unfold tailWord_3347773
  simp only [CollatzResearch.WordTrace]
  refine ⟨122103312500597649953839973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81402208333731766635893315 122103312500597649953839973)
  ·
    refine ⟨22894371093862059366344995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122103312500597649953839973 22894371093862059366344995)
    ·
      refine ⟨34341556640793089049517493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22894371093862059366344995 34341556640793089049517493)
      ·
        refine ⟨3219520935074352098392265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34341556640793089049517493 3219520935074352098392265)
        ·
          refine ⟨2414640701305764073794199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3219520935074352098392265 2414640701305764073794199)
          ·
            refine ⟨3621961051958646110691299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414640701305764073794199 3621961051958646110691299)
            ·
              refine ⟨5432941577937969166036949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3621961051958646110691299 5432941577937969166036949)
              ·
                refine ⟨127334568232921152328991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5432941577937969166036949 127334568232921152328991)
                ·
                  rfl

theorem cell22_3347773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 7].length) (baseStart_3347773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347773 prefixEnd_3347773 := by exact prefixLift 3347773
  have htrace : WordTrace (prefixWord ++ tailWord_3347773) baseStart_3347773 baseEnd_3347773 := by
    simpa [prefixWord, tailWord_3347773, baseEnd_3347773] using wordTrace_append hprefix tailTrace_3347773
  have hstable : (prefixWord ++ tailWord_3347773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347773).length < 2 ^ (prefixWord ++ tailWord_3347773).sum := by decide
  have hdescent : baseEnd_3347773 < baseStart_3347773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347818 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 5]
def baseStart_3347818 : Nat := 118140960795 + 3347818 * 2 ^ 59
def prefixEnd_3347818 : Nat := 4983230072969 + 3 ^ 40 * 3347818 * 2
def baseEnd_3347818 : Nat := 382008839505308417861927

theorem tailTrace_3347818 : CollatzResearch.WordTrace tailWord_3347818 prefixEnd_3347818 382008839505308417861927 := by
  unfold tailWord_3347818
  simp only [CollatzResearch.WordTrace]
  refine ⟨30526238446358655659807027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81403302523623081759485405 30526238446358655659807027)
  ·
    refine ⟨45789357669537983489710541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30526238446358655659807027 45789357669537983489710541)
    ·
      refine ⟨17171009126076743808641453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45789357669537983489710541 17171009126076743808641453)
      ·
        refine ⟨6439128422278778928240545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17171009126076743808641453 6439128422278778928240545)
        ·
          refine ⟨4829346316709084196180409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6439128422278778928240545 4829346316709084196180409)
          ·
            refine ⟨3622009737531813147135307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4829346316709084196180409 3622009737531813147135307)
            ·
              refine ⟨5433014606297719720702961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3622009737531813147135307 5433014606297719720702961)
              ·
                refine ⟨4074760954723289790527221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5433014606297719720702961 4074760954723289790527221)
                ·
                  refine ⟨382008839505308417861927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4074760954723289790527221 382008839505308417861927)
                  ·
                    rfl

theorem cell22_3347818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_3347818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347818 prefixEnd_3347818 := by exact prefixLift 3347818
  have htrace : WordTrace (prefixWord ++ tailWord_3347818) baseStart_3347818 baseEnd_3347818 := by
    simpa [prefixWord, tailWord_3347818, baseEnd_3347818] using wordTrace_append hprefix tailTrace_3347818
  have hstable : (prefixWord ++ tailWord_3347818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347818).length < 2 ^ (prefixWord ++ tailWord_3347818).sum := by decide
  have hdescent : baseEnd_3347818 < baseStart_3347818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347857 : List Nat := [1, 2, 2, 1, 1, 1, 2, 12]
def baseStart_3347857 : Nat := 118140960795 + 3347857 * 2 ^ 59
def prefixEnd_3347857 : Nat := 4983230072969 + 3 ^ 40 * 3347857 * 2
def baseEnd_3347857 : Nat := 127337763223660239095629

theorem tailTrace_3347857 : CollatzResearch.WordTrace tailWord_3347857 prefixEnd_3347857 127337763223660239095629 := by
  unfold tailWord_3347857
  simp only [CollatzResearch.WordTrace]
  refine ⟨122106376232293332299897825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81404250821528888199931883 122106376232293332299897825)
  ·
    refine ⟨91579782174219999224923369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122106376232293332299897825 91579782174219999224923369)
    ·
      refine ⟨68684836630664999418692527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91579782174219999224923369 68684836630664999418692527)
      ·
        refine ⟨103027254945997499128038791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68684836630664999418692527 103027254945997499128038791)
        ·
          refine ⟨154540882418996248692058187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103027254945997499128038791 154540882418996248692058187)
          ·
            refine ⟨231811323628494373038087281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154540882418996248692058187 231811323628494373038087281)
            ·
              refine ⟨173858492721370779778565461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231811323628494373038087281 173858492721370779778565461)
              ·
                refine ⟨127337763223660239095629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 173858492721370779778565461 127337763223660239095629)
                ·
                  rfl

theorem cell22_3347857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 12].length) (baseStart_3347857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347857 prefixEnd_3347857 := by exact prefixLift 3347857
  have htrace : WordTrace (prefixWord ++ tailWord_3347857) baseStart_3347857 baseEnd_3347857 := by
    simpa [prefixWord, tailWord_3347857, baseEnd_3347857] using wordTrace_append hprefix tailTrace_3347857
  have hstable : (prefixWord ++ tailWord_3347857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347857).length < 2 ^ (prefixWord ++ tailWord_3347857).sum := by decide
  have hdescent : baseEnd_3347857 < baseStart_3347857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347874 : List Nat := [3, 3, 1, 2, 1, 2, 10]
def baseStart_3347874 : Nat := 118140960795 + 3347874 * 2 ^ 59
def prefixEnd_3347874 : Nat := 4983230072969 + 3 ^ 40 * 3347874 * 2
def baseEnd_3347874 : Nat := 42446136609642954599467

theorem tailTrace_3347874 : CollatzResearch.WordTrace tailWord_3347874 prefixEnd_3347874 42446136609642954599467 := by
  unfold tailWord_3347874
  simp only [CollatzResearch.WordTrace]
  refine ⟨30526749068307936050816669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81404664182154496135511117 30526749068307936050816669)
  ·
    refine ⟨11447530900615476019056251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30526749068307936050816669 11447530900615476019056251)
    ·
      refine ⟨17171296350923214028584377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11447530900615476019056251 17171296350923214028584377)
      ·
        refine ⟨12878472263192410521438283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17171296350923214028584377 12878472263192410521438283)
        ·
          refine ⟨19317708394788615782157425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12878472263192410521438283 19317708394788615782157425)
          ·
            refine ⟨14488281296091461836618069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19317708394788615782157425 14488281296091461836618069)
            ·
              refine ⟨42446136609642954599467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14488281296091461836618069 42446136609642954599467)
              ·
                rfl

theorem cell22_3347874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 10].length) (baseStart_3347874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347874 prefixEnd_3347874 := by exact prefixLift 3347874
  have htrace : WordTrace (prefixWord ++ tailWord_3347874) baseStart_3347874 baseEnd_3347874 := by
    simpa [prefixWord, tailWord_3347874, baseEnd_3347874] using wordTrace_append hprefix tailTrace_3347874
  have hstable : (prefixWord ++ tailWord_3347874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347874).length < 2 ^ (prefixWord ++ tailWord_3347874).sum := by decide
  have hdescent : baseEnd_3347874 < baseStart_3347874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347880 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 6]
def baseStart_3347880 : Nat := 118140960795 + 3347880 * 2 ^ 59
def prefixEnd_3347880 : Nat := 4983230072969 + 3 ^ 40 * 3347880 * 2
def baseEnd_3347880 : Nat := 382015914127659252845197

theorem tailTrace_3347880 : CollatzResearch.WordTrace tailWord_3347880 prefixEnd_3347880 382015914127659252845197 := by
  unfold tailWord_3347880
  simp only [CollatzResearch.WordTrace]
  refine ⟨61053607555605003613992547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81404810074140004818656729 61053607555605003613992547)
  ·
    refine ⟨91580411333407505420988821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61053607555605003613992547 91580411333407505420988821)
    ·
      refine ⟨4292831781253476816608851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91580411333407505420988821 4292831781253476816608851)
      ·
        refine ⟨6439247671880215224913277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4292831781253476816608851 6439247671880215224913277)
        ·
          refine ⟨2414717876955080709342479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6439247671880215224913277 2414717876955080709342479)
          ·
            refine ⟨3622076815432621064013719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414717876955080709342479 3622076815432621064013719)
            ·
              refine ⟨5433115223148931596020579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3622076815432621064013719 5433115223148931596020579)
              ·
                refine ⟨8149672834723397394030869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5433115223148931596020579 8149672834723397394030869)
                ·
                  refine ⟨382015914127659252845197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8149672834723397394030869 382015914127659252845197)
                  ·
                    rfl

theorem cell22_3347880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 6].length) (baseStart_3347880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347880 prefixEnd_3347880 := by exact prefixLift 3347880
  have htrace : WordTrace (prefixWord ++ tailWord_3347880) baseStart_3347880 baseEnd_3347880 := by
    simpa [prefixWord, tailWord_3347880, baseEnd_3347880] using wordTrace_append hprefix tailTrace_3347880
  have hstable : (prefixWord ++ tailWord_3347880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347880).length < 2 ^ (prefixWord ++ tailWord_3347880).sum := by decide
  have hdescent : baseEnd_3347880 < baseStart_3347880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347964 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 8]
def baseStart_3347964 : Nat := 118140960795 + 3347964 * 2 ^ 59
def prefixEnd_3347964 : Nat := 4983230072969 + 3 ^ 40 * 3347964 * 2
def baseEnd_3347964 : Nat := 382025499099876513145111

theorem tailTrace_3347964 : CollatzResearch.WordTrace tailWord_3347964 prefixEnd_3347964 382025499099876513145111 := by
  unfold tailWord_3347964
  simp only [CollatzResearch.WordTrace]
  refine ⟨61055139421452844787021473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81406852561937126382695297 61055139421452844787021473)
  ·
    refine ⟨45791354566089633590266105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61055139421452844787021473 45791354566089633590266105)
    ·
      refine ⟨34343515924567225192699579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45791354566089633590266105 34343515924567225192699579)
      ·
        refine ⟨51515273886850837789049369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34343515924567225192699579 51515273886850837789049369)
        ·
          refine ⟨38636455415138128341787027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51515273886850837789049369 38636455415138128341787027)
          ·
            refine ⟨57954683122707192512680541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38636455415138128341787027 57954683122707192512680541)
            ·
              refine ⟨21733006171015197192255203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57954683122707192512680541 21733006171015197192255203)
              ·
                refine ⟨32599509256522795788382805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21733006171015197192255203 32599509256522795788382805)
                ·
                  refine ⟨382025499099876513145111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32599509256522795788382805 382025499099876513145111)
                  ·
                    rfl

theorem cell22_3347964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_3347964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3347964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3347964 prefixEnd_3347964 := by exact prefixLift 3347964
  have htrace : WordTrace (prefixWord ++ tailWord_3347964) baseStart_3347964 baseEnd_3347964 := by
    simpa [prefixWord, tailWord_3347964, baseEnd_3347964] using wordTrace_append hprefix tailTrace_3347964
  have hstable : (prefixWord ++ tailWord_3347964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347964).length < 2 ^ (prefixWord ++ tailWord_3347964).sum := by decide
  have hdescent : baseEnd_3347964 < baseStart_3347964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348041 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 5, 3]
def baseStart_3348041 : Nat := 118140960795 + 3348041 * 2 ^ 59
def prefixEnd_3348041 : Nat := 4983230072969 + 3 ^ 40 * 3348041 * 2
def baseEnd_3348041 : Nat := 1146102855973227005260097

theorem tailTrace_3348041 : CollatzResearch.WordTrace tailWord_3348041 prefixEnd_3348041 1146102855973227005260097 := by
  unfold tailWord_3348041
  simp only [CollatzResearch.WordTrace]
  refine ⟨122113087263626731724595977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81408724842417821149730651 122113087263626731724595977)
  ·
    refine ⟨91584815447720048793446983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122113087263626731724595977 91584815447720048793446983)
    ·
      refine ⟨137377223171580073190170475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91584815447720048793446983 137377223171580073190170475)
      ·
        refine ⟨206065834757370109785255713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137377223171580073190170475 206065834757370109785255713)
        ·
          refine ⟨154549376068027582338941785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206065834757370109785255713 154549376068027582338941785)
          ·
            refine ⟨115912032051020686754206339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154549376068027582338941785 115912032051020686754206339)
            ·
              refine ⟨173868048076531030131309509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115912032051020686754206339 173868048076531030131309509)
              ·
                refine ⟨32600259014349568149620533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173868048076531030131309509 32600259014349568149620533)
                ·
                  refine ⟨3056274282595272014026925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32600259014349568149620533 3056274282595272014026925)
                  ·
                    refine ⟨1146102855973227005260097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3056274282595272014026925 1146102855973227005260097)
                    ·
                      rfl

theorem cell22_3348041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 3].length) (baseStart_3348041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348041 prefixEnd_3348041 := by exact prefixLift 3348041
  have htrace : WordTrace (prefixWord ++ tailWord_3348041) baseStart_3348041 baseEnd_3348041 := by
    simpa [prefixWord, tailWord_3348041, baseEnd_3348041] using wordTrace_append hprefix tailTrace_3348041
  have hstable : (prefixWord ++ tailWord_3348041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348041).length < 2 ^ (prefixWord ++ tailWord_3348041).sum := by decide
  have hdescent : baseEnd_3348041 < baseStart_3348041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348045 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3348045 : Nat := 118140960795 + 3348045 * 2 ^ 59
def prefixEnd_3348045 : Nat := 4983230072969 + 3 ^ 40 * 3348045 * 2
def baseEnd_3348045 : Nat := 1146104225254972328160085

theorem tailTrace_3348045 : CollatzResearch.WordTrace tailWord_3348045 prefixEnd_3348045 1146104225254972328160085 := by
  unfold tailWord_3348045
  simp only [CollatzResearch.WordTrace]
  refine ⟨122113233155612240407741589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81408822103741493605161059 122113233155612240407741589)
  ·
    refine ⟨5724057804169323769112887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122113233155612240407741589 5724057804169323769112887)
    ·
      refine ⟨8586086706253985653669331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5724057804169323769112887 8586086706253985653669331)
      ·
        refine ⟨12879130059380978480503997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8586086706253985653669331 12879130059380978480503997)
        ·
          refine ⟨4829673772267866930188999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12879130059380978480503997 4829673772267866930188999)
          ·
            refine ⟨7244510658401800395283499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4829673772267866930188999 7244510658401800395283499)
            ·
              refine ⟨10866765987602700592925249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7244510658401800395283499 10866765987602700592925249)
              ·
                refine ⟨8150074490702025444693937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10866765987602700592925249 8150074490702025444693937)
                ·
                  refine ⟨6112555868026519083520453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8150074490702025444693937 6112555868026519083520453)
                  ·
                    refine ⟨1146104225254972328160085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6112555868026519083520453 1146104225254972328160085)
                    ·
                      rfl

theorem cell22_3348045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3348045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348045 prefixEnd_3348045 := by exact prefixLift 3348045
  have htrace : WordTrace (prefixWord ++ tailWord_3348045) baseStart_3348045 baseEnd_3348045 := by
    simpa [prefixWord, tailWord_3348045, baseEnd_3348045] using wordTrace_append hprefix tailTrace_3348045
  have hstable : (prefixWord ++ tailWord_3348045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348045).length < 2 ^ (prefixWord ++ tailWord_3348045).sum := by decide
  have hdescent : baseEnd_3348045 < baseStart_3348045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348212 : List Nat := [2, 6, 1, 1, 1, 3, 8]
def baseStart_3348212 : Nat := 118140960795 + 3348212 * 2 ^ 59
def prefixEnd_3348212 : Nat := 4983230072969 + 3 ^ 40 * 3348212 * 2
def baseEnd_3348212 : Nat := 42450421954364428119799

theorem tailTrace_3348212 : CollatzResearch.WordTrace tailWord_3348212 prefixEnd_3348212 42450421954364428119799 := by
  unfold tailWord_3348212
  simp only [CollatzResearch.WordTrace]
  refine ⟨61059662073003613964535445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81412882764004818619380593 61059662073003613964535445)
  ·
    refine ⟨2862171659672044404587599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61059662073003613964535445 2862171659672044404587599)
    ·
      refine ⟨4293257489508066606881399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2862171659672044404587599 4293257489508066606881399)
      ·
        refine ⟨6439886234262099910322099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293257489508066606881399 6439886234262099910322099)
        ·
          refine ⟨9659829351393149865483149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6439886234262099910322099 9659829351393149865483149)
          ·
            refine ⟨3622436006772431199556181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9659829351393149865483149 3622436006772431199556181)
            ·
              refine ⟨42450421954364428119799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3622436006772431199556181 42450421954364428119799)
              ·
                rfl

theorem cell22_3348212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 8].length) (baseStart_3348212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348212 prefixEnd_3348212 := by exact prefixLift 3348212
  have htrace : WordTrace (prefixWord ++ tailWord_3348212) baseStart_3348212 baseEnd_3348212 := by
    simpa [prefixWord, tailWord_3348212, baseEnd_3348212] using wordTrace_append hprefix tailTrace_3348212
  have hstable : (prefixWord ++ tailWord_3348212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348212).length < 2 ^ (prefixWord ++ tailWord_3348212).sum := by decide
  have hdescent : baseEnd_3348212 < baseStart_3348212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348238 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3348238 : Nat := 118140960795 + 3348238 * 2 ^ 59
def prefixEnd_3348238 : Nat := 4983230072969 + 3 ^ 40 * 3348238 * 2
def baseEnd_3348238 : Nat := 1146170293099184158084493

theorem tailTrace_3348238 : CollatzResearch.WordTrace tailWord_3348238 prefixEnd_3348238 1146170293099184158084493 := by
  unfold tailWord_3348238
  simp only [CollatzResearch.WordTrace]
  refine ⟨15265034055489129296189671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81413514962608689579678245 15265034055489129296189671)
  ·
    refine ⟨22897551083233693944284507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15265034055489129296189671 22897551083233693944284507)
    ·
      refine ⟨34346326624850540916426761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22897551083233693944284507 34346326624850540916426761)
      ·
        refine ⟨25759744968637905687320071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34346326624850540916426761 25759744968637905687320071)
        ·
          refine ⟨38639617452956858530980107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25759744968637905687320071 38639617452956858530980107)
          ·
            refine ⟨57959426179435287796470161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38639617452956858530980107 57959426179435287796470161)
            ·
              refine ⟨43469569634576465847352621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57959426179435287796470161 43469569634576465847352621)
              ·
                refine ⟨16301088612966174692757233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43469569634576465847352621 16301088612966174692757233)
                ·
                  refine ⟨12225816459724631019567925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16301088612966174692757233 12225816459724631019567925)
                  ·
                    refine ⟨1146170293099184158084493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12225816459724631019567925 1146170293099184158084493)
                    ·
                      rfl

theorem cell22_3348238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3348238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348238 prefixEnd_3348238 := by exact prefixLift 3348238
  have htrace : WordTrace (prefixWord ++ tailWord_3348238) baseStart_3348238 baseEnd_3348238 := by
    simpa [prefixWord, tailWord_3348238, baseEnd_3348238] using wordTrace_append hprefix tailTrace_3348238
  have hstable : (prefixWord ++ tailWord_3348238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348238).length < 2 ^ (prefixWord ++ tailWord_3348238).sum := by decide
  have hdescent : baseEnd_3348238 < baseStart_3348238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348278 : List Nat := [5, 1, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_3348278 : Nat := 118140960795 + 3348278 * 2 ^ 59
def prefixEnd_3348278 : Nat := 4983230072969 + 3 ^ 40 * 3348278 * 2
def baseEnd_3348278 : Nat := 1146183985916637387084371

theorem tailTrace_3348278 : CollatzResearch.WordTrace tailWord_3348278 prefixEnd_3348278 1146183985916637387084371 := by
  unfold tailWord_3348278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7632608210235507575060843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81414487575845414133982325 7632608210235507575060843)
  ·
    refine ⟨11448912315353261362591265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7632608210235507575060843 11448912315353261362591265)
    ·
      refine ⟨8586684236514946021943449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11448912315353261362591265 8586684236514946021943449)
      ·
        refine ⟨6440013177386209516457587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8586684236514946021943449 6440013177386209516457587)
        ·
          refine ⟨9660019766079314274686381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6440013177386209516457587 9660019766079314274686381)
          ·
            refine ⟨3622507412279742853007393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9660019766079314274686381 3622507412279742853007393)
            ·
              refine ⟨2716880559209807139755545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3622507412279742853007393 2716880559209807139755545)
              ·
                refine ⟨2037660419407355354816659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716880559209807139755545 2037660419407355354816659)
                ·
                  refine ⟨3056490629111033032224989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037660419407355354816659 3056490629111033032224989)
                  ·
                    refine ⟨1146183985916637387084371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3056490629111033032224989 1146183985916637387084371)
                    ·
                      rfl

theorem cell22_3348278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_3348278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348278 prefixEnd_3348278 := by exact prefixLift 3348278
  have htrace : WordTrace (prefixWord ++ tailWord_3348278) baseStart_3348278 baseEnd_3348278 := by
    simpa [prefixWord, tailWord_3348278, baseEnd_3348278] using wordTrace_append hprefix tailTrace_3348278
  have hstable : (prefixWord ++ tailWord_3348278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348278).length < 2 ^ (prefixWord ++ tailWord_3348278).sum := by decide
  have hdescent : baseEnd_3348278 < baseStart_3348278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348298 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_3348298 : Nat := 118140960795 + 3348298 * 2 ^ 59
def prefixEnd_3348298 : Nat := 4983230072969 + 3 ^ 40 * 3348298 * 2
def baseEnd_3348298 : Nat := 1146190832325364001584309

theorem tailTrace_3348298 : CollatzResearch.WordTrace tailWord_3348298 prefixEnd_3348298 1146190832325364001584309 := by
  unfold tailWord_3348298
  simp only [CollatzResearch.WordTrace]
  refine ⟨30530615205923916154175387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81414973882463776411134365 30530615205923916154175387)
  ·
    refine ⟨45795922808885874231263081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30530615205923916154175387 45795922808885874231263081)
    ·
      refine ⟨34346942106664405673447311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45795922808885874231263081 34346942106664405673447311)
      ·
        refine ⟨51520413159996608510170967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34346942106664405673447311 51520413159996608510170967)
        ·
          refine ⟨77280619739994912765256451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51520413159996608510170967 77280619739994912765256451)
          ·
            refine ⟨115920929609992369147884677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77280619739994912765256451 115920929609992369147884677)
            ·
              refine ⟨21735174301873569215228377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115920929609992369147884677 21735174301873569215228377)
              ·
                refine ⟨16301380726405176911421283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21735174301873569215228377 16301380726405176911421283)
                ·
                  refine ⟨24452071089607765367131925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16301380726405176911421283 24452071089607765367131925)
                  ·
                    refine ⟨1146190832325364001584309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24452071089607765367131925 1146190832325364001584309)
                    ·
                      rfl

theorem cell22_3348298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_3348298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348298 prefixEnd_3348298 := by exact prefixLift 3348298
  have htrace : WordTrace (prefixWord ++ tailWord_3348298) baseStart_3348298 baseEnd_3348298 := by
    simpa [prefixWord, tailWord_3348298, baseEnd_3348298] using wordTrace_append hprefix tailTrace_3348298
  have hstable : (prefixWord ++ tailWord_3348298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348298).length < 2 ^ (prefixWord ++ tailWord_3348298).sum := by decide
  have hdescent : baseEnd_3348298 < baseStart_3348298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348334 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3348334 : Nat := 118140960795 + 3348334 * 2 ^ 59
def prefixEnd_3348334 : Nat := 4983230072969 + 3 ^ 40 * 3348334 * 2
def baseEnd_3348334 : Nat := 1146203155861071907684199

theorem tailTrace_3348334 : CollatzResearch.WordTrace tailWord_3348334 prefixEnd_3348334 1146203155861071907684199 := by
  unfold tailWord_3348334
  simp only [CollatzResearch.WordTrace]
  refine ⟨15265471731445655345626507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81415849234376828510008037 15265471731445655345626507)
  ·
    refine ⟨22898207597168483018439761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15265471731445655345626507 22898207597168483018439761)
    ·
      refine ⟨17173655697876362263829821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22898207597168483018439761 17173655697876362263829821)
      ·
        refine ⟨6440120886703635848936183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17173655697876362263829821 6440120886703635848936183)
        ·
          refine ⟨9660181330055453773404275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6440120886703635848936183 9660181330055453773404275)
          ·
            refine ⟨14490271995083180660106413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9660181330055453773404275 14490271995083180660106413)
            ·
              refine ⟨5433851998156192747539905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14490271995083180660106413 5433851998156192747539905)
              ·
                refine ⟨4075388998617144560654929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5433851998156192747539905 4075388998617144560654929)
                ·
                  refine ⟨3056541748962858420491197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4075388998617144560654929 3056541748962858420491197)
                  ·
                    refine ⟨1146203155861071907684199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3056541748962858420491197 1146203155861071907684199)
                    ·
                      rfl

theorem cell22_3348334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3348334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348334 prefixEnd_3348334 := by exact prefixLift 3348334
  have htrace : WordTrace (prefixWord ++ tailWord_3348334) baseStart_3348334 baseEnd_3348334 := by
    simpa [prefixWord, tailWord_3348334, baseEnd_3348334] using wordTrace_append hprefix tailTrace_3348334
  have hstable : (prefixWord ++ tailWord_3348334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348334).length < 2 ^ (prefixWord ++ tailWord_3348334).sum := by decide
  have hdescent : baseEnd_3348334 < baseStart_3348334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348484 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_3348484 : Nat := 118140960795 + 3348484 * 2 ^ 59
def prefixEnd_3348484 : Nat := 4983230072969 + 3 ^ 40 * 3348484 * 2
def baseEnd_3348484 : Nat := 1146254503926521516433739

theorem tailTrace_3348484 : CollatzResearch.WordTrace tailWord_3348484 prefixEnd_3348484 1146254503926521516433739 := by
  unfold tailWord_3348484
  simp only [CollatzResearch.WordTrace]
  refine ⟨61064622400510909191486253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81419496534014545588648337 61064622400510909191486253)
  ·
    refine ⟨22899233400191590946807345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61064622400510909191486253 22899233400191590946807345)
    ·
      refine ⟨17174425050143693210105509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22899233400191590946807345 17174425050143693210105509)
      ·
        refine ⟨3220204696901942476894783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17174425050143693210105509 3220204696901942476894783)
        ·
          refine ⟨4830307045352913715342175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3220204696901942476894783 4830307045352913715342175)
          ·
            refine ⟨7245460568029370573013263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830307045352913715342175 7245460568029370573013263)
            ·
              refine ⟨10868190852044055859519895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7245460568029370573013263 10868190852044055859519895)
              ·
                refine ⟨16302286278066083789279843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10868190852044055859519895 16302286278066083789279843)
                ·
                  refine ⟨24453429417099125683919765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16302286278066083789279843 24453429417099125683919765)
                  ·
                    refine ⟨1146254503926521516433739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24453429417099125683919765 1146254503926521516433739)
                    ·
                      rfl

theorem cell22_3348484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_3348484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348484 prefixEnd_3348484 := by exact prefixLift 3348484
  have htrace : WordTrace (prefixWord ++ tailWord_3348484) baseStart_3348484 baseEnd_3348484 := by
    simpa [prefixWord, tailWord_3348484, baseEnd_3348484] using wordTrace_append hprefix tailTrace_3348484
  have hstable : (prefixWord ++ tailWord_3348484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348484).length < 2 ^ (prefixWord ++ tailWord_3348484).sum := by decide
  have hdescent : baseEnd_3348484 < baseStart_3348484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348503 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 2, 3]
def baseStart_3348503 : Nat := 118140960795 + 3348503 * 2 ^ 59
def prefixEnd_3348503 : Nat := 4983230072969 + 3 ^ 40 * 3348503 * 2
def baseEnd_3348503 : Nat := 1146261008014811800208681

theorem tailTrace_3348503 : CollatzResearch.WordTrace tailWord_3348503 prefixEnd_3348503 1146261008014811800208681 := by
  unfold tailWord_3348503
  simp only [CollatzResearch.WordTrace]
  refine ⟨122129937787952984627914163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81419958525301989751942775 122129937787952984627914163)
  ·
    refine ⟨183194906681929476941871245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122129937787952984627914163 183194906681929476941871245)
    ·
      refine ⟨68698090005723553853201717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183194906681929476941871245 68698090005723553853201717)
      ·
        refine ⟨6440445938036583173737661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68698090005723553853201717 6440445938036583173737661)
        ·
          refine ⟨2415167226763718690151623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6440445938036583173737661 2415167226763718690151623)
          ·
            refine ⟨3622750840145578035227435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415167226763718690151623 3622750840145578035227435)
            ·
              refine ⟨5434126260218367052841153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3622750840145578035227435 5434126260218367052841153)
              ·
                refine ⟨4075594695163775289630865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5434126260218367052841153 4075594695163775289630865)
                ·
                  refine ⟨3056696021372831467223149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4075594695163775289630865 3056696021372831467223149)
                  ·
                    refine ⟨1146261008014811800208681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3056696021372831467223149 1146261008014811800208681)
                    ·
                      rfl

theorem cell22_3348503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_3348503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348503 prefixEnd_3348503 := by exact prefixLift 3348503
  have htrace : WordTrace (prefixWord ++ tailWord_3348503) baseStart_3348503 baseEnd_3348503 := by
    simpa [prefixWord, tailWord_3348503, baseEnd_3348503] using wordTrace_append hprefix tailTrace_3348503
  have hstable : (prefixWord ++ tailWord_3348503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348503).length < 2 ^ (prefixWord ++ tailWord_3348503).sum := by decide
  have hdescent : baseEnd_3348503 < baseStart_3348503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348514 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_3348514 : Nat := 118140960795 + 3348514 * 2 ^ 59
def prefixEnd_3348514 : Nat := 4983230072969 + 3 ^ 40 * 3348514 * 2
def baseEnd_3348514 : Nat := 1146264773539611438183647

theorem tailTrace_3348514 : CollatzResearch.WordTrace tailWord_3348514 prefixEnd_3348514 1146264773539611438183647 := by
  unfold tailWord_3348514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30532584747728283376641149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81420225993942089004376397 30532584747728283376641149)
  ·
    refine ⟨11449719280398106266240431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30532584747728283376641149 11449719280398106266240431)
    ·
      refine ⟨17174578920597159399360647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11449719280398106266240431 17174578920597159399360647)
      ·
        refine ⟨25761868380895739099040971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17174578920597159399360647 25761868380895739099040971)
        ·
          refine ⟨38642802571343608648561457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25761868380895739099040971 38642802571343608648561457)
          ·
            refine ⟨28982101928507706486421093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38642802571343608648561457 28982101928507706486421093)
            ·
              refine ⟨5434144111595194966203955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28982101928507706486421093 5434144111595194966203955)
              ·
                refine ⟨8151216167392792449305933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5434144111595194966203955 8151216167392792449305933)
                ·
                  refine ⟨3056706062772297168489725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8151216167392792449305933 3056706062772297168489725)
                  ·
                    refine ⟨1146264773539611438183647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3056706062772297168489725 1146264773539611438183647)
                    ·
                      rfl

theorem cell22_3348514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_3348514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348514 prefixEnd_3348514 := by exact prefixLift 3348514
  have htrace : WordTrace (prefixWord ++ tailWord_3348514) baseStart_3348514 baseEnd_3348514 := by
    simpa [prefixWord, tailWord_3348514, baseEnd_3348514] using wordTrace_append hprefix tailTrace_3348514
  have hstable : (prefixWord ++ tailWord_3348514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348514).length < 2 ^ (prefixWord ++ tailWord_3348514).sum := by decide
  have hdescent : baseEnd_3348514 < baseStart_3348514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348578 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 5]
def baseStart_3348578 : Nat := 118140960795 + 3348578 * 2 ^ 59
def prefixEnd_3348578 : Nat := 4983230072969 + 3 ^ 40 * 3348578 * 2
def baseEnd_3348578 : Nat := 382095560682512201527817

theorem tailTrace_3348578 : CollatzResearch.WordTrace tailWord_3348578 prefixEnd_3348578 382095560682512201527817 := by
  unfold tailWord_3348578
  simp only [CollatzResearch.WordTrace]
  refine ⟨30533168315670318109223597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81421782175120848291262925 30533168315670318109223597)
  ·
    refine ⟨11449938118376369290958849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30533168315670318109223597 11449938118376369290958849)
    ·
      refine ⟨8587453588782276968219137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11449938118376369290958849 8587453588782276968219137)
      ·
        refine ⟨6440590191586707726164353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8587453588782276968219137 6440590191586707726164353)
        ·
          refine ⟨4830442643690030794623265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6440590191586707726164353 4830442643690030794623265)
          ·
            refine ⟨3622831982767523095967449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4830442643690030794623265 3622831982767523095967449)
            ·
              refine ⟨2717123987075642321975587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3622831982767523095967449 2717123987075642321975587)
              ·
                refine ⟨4075685980613463482963381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717123987075642321975587 4075685980613463482963381)
                ·
                  refine ⟨382095560682512201527817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4075685980613463482963381 382095560682512201527817)
                  ·
                    rfl

theorem cell22_3348578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_3348578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348578 prefixEnd_3348578 := by exact prefixLift 3348578
  have htrace : WordTrace (prefixWord ++ tailWord_3348578) baseStart_3348578 baseEnd_3348578 := by
    simpa [prefixWord, tailWord_3348578, baseEnd_3348578] using wordTrace_append hprefix tailTrace_3348578
  have hstable : (prefixWord ++ tailWord_3348578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348578).length < 2 ^ (prefixWord ++ tailWord_3348578).sum := by decide
  have hdescent : baseEnd_3348578 < baseStart_3348578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348666 : List Nat := [3, 1, 1, 1, 2, 2, 3, 5, 1, 3]
def baseStart_3348666 : Nat := 118140960795 + 3348666 * 2 ^ 59
def prefixEnd_3348666 : Nat := 4983230072969 + 3 ^ 40 * 3348666 * 2
def baseEnd_3348666 : Nat := 1146316806245933708383181

theorem tailTrace_3348666 : CollatzResearch.WordTrace tailWord_3348666 prefixEnd_3348666 1146316806245933708383181 := by
  unfold tailWord_3348666
  simp only [CollatzResearch.WordTrace]
  refine ⟨30533970721590615866524463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81423921924241642310731901 30533970721590615866524463)
  ·
    refine ⟨45800956082385923799786695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30533970721590615866524463 45800956082385923799786695)
    ·
      refine ⟨68701434123578885699680043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45800956082385923799786695 68701434123578885699680043)
      ·
        refine ⟨103052151185368328549520065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68701434123578885699680043 103052151185368328549520065)
        ·
          refine ⟨77289113389026246412140049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103052151185368328549520065 77289113389026246412140049)
          ·
            refine ⟨57966835041769684809105037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77289113389026246412140049 57966835041769684809105037)
            ·
              refine ⟨21737563140663631803414389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57966835041769684809105037 21737563140663631803414389)
              ·
                refine ⟨2037896544437215481570099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21737563140663631803414389 2037896544437215481570099)
                ·
                  refine ⟨3056844816655823222355149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037896544437215481570099 3056844816655823222355149)
                  ·
                    refine ⟨1146316806245933708383181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3056844816655823222355149 1146316806245933708383181)
                    ·
                      rfl

theorem cell22_3348666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_3348666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348666 prefixEnd_3348666 := by exact prefixLift 3348666
  have htrace : WordTrace (prefixWord ++ tailWord_3348666) baseStart_3348666 baseEnd_3348666 := by
    simpa [prefixWord, tailWord_3348666, baseEnd_3348666] using wordTrace_append hprefix tailTrace_3348666
  have hstable : (prefixWord ++ tailWord_3348666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348666).length < 2 ^ (prefixWord ++ tailWord_3348666).sum := by decide
  have hdescent : baseEnd_3348666 < baseStart_3348666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348677 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_3348677 : Nat := 118140960795 + 3348677 * 2 ^ 59
def prefixEnd_3348677 : Nat := 4983230072969 + 3 ^ 40 * 3348677 * 2
def baseEnd_3348677 : Nat := 1146320571770733346358147

theorem tailTrace_3348677 : CollatzResearch.WordTrace tailWord_3348677 prefixEnd_3348677 1146320571770733346358147 := by
  unfold tailWord_3348677
  simp only [CollatzResearch.WordTrace]
  refine ⟨122136284089322612344748285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81424189392881741563165523 122136284089322612344748285)
  ·
    refine ⟨45801106533495979629280607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122136284089322612344748285 45801106533495979629280607)
    ·
      refine ⟨68701659800243969443920911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45801106533495979629280607 68701659800243969443920911)
      ·
        refine ⟨103052489700365954165881367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68701659800243969443920911 103052489700365954165881367)
        ·
          refine ⟨154578734550548931248822051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103052489700365954165881367 154578734550548931248822051)
          ·
            refine ⟨231868101825823396873233077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154578734550548931248822051 231868101825823396873233077)
            ·
              refine ⟨21737634546170943456865601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231868101825823396873233077 21737634546170943456865601)
              ·
                refine ⟨16303225909628207592649201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21737634546170943456865601 16303225909628207592649201)
                ·
                  refine ⟨12227419432221155694486901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16303225909628207592649201 12227419432221155694486901)
                  ·
                    refine ⟨1146320571770733346358147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12227419432221155694486901 1146320571770733346358147)
                    ·
                      rfl

theorem cell22_3348677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_3348677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348677 prefixEnd_3348677 := by exact prefixLift 3348677
  have htrace : WordTrace (prefixWord ++ tailWord_3348677) baseStart_3348677 baseEnd_3348677 := by
    simpa [prefixWord, tailWord_3348677, baseEnd_3348677] using wordTrace_append hprefix tailTrace_3348677
  have hstable : (prefixWord ++ tailWord_3348677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348677).length < 2 ^ (prefixWord ++ tailWord_3348677).sum := by decide
  have hdescent : baseEnd_3348677 < baseStart_3348677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348696 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 5]
def baseStart_3348696 : Nat := 118140960795 + 3348696 * 2 ^ 59
def prefixEnd_3348696 : Nat := 4983230072969 + 3 ^ 40 * 3348696 * 2
def baseEnd_3348696 : Nat := 382109025286341210044363

theorem tailTrace_3348696 : CollatzResearch.WordTrace tailWord_3348696 prefixEnd_3348696 382109025286341210044363 := by
  unfold tailWord_3348696
  simp only [CollatzResearch.WordTrace]
  refine ⟨61068488538126889294844971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81424651384169185726459961 61068488538126889294844971)
  ·
    refine ⟨91602732807190333942267457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61068488538126889294844971 91602732807190333942267457)
    ·
      refine ⟨68702049605392750456700593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91602732807190333942267457 68702049605392750456700593)
      ·
        refine ⟨51526537204044562842525445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68702049605392750456700593 51526537204044562842525445)
        ·
          refine ⟨9661225725758355532973521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51526537204044562842525445 9661225725758355532973521)
          ·
            refine ⟨7245919294318766649730141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9661225725758355532973521 7245919294318766649730141)
            ·
              refine ⟨2717219735369537493648803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7245919294318766649730141 2717219735369537493648803)
              ·
                refine ⟨4075829603054306240473205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717219735369537493648803 4075829603054306240473205)
                ·
                  refine ⟨382109025286341210044363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4075829603054306240473205 382109025286341210044363)
                  ·
                    rfl

theorem cell22_3348696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 5].length) (baseStart_3348696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348696 prefixEnd_3348696 := by exact prefixLift 3348696
  have htrace : WordTrace (prefixWord ++ tailWord_3348696) baseStart_3348696 baseEnd_3348696 := by
    simpa [prefixWord, tailWord_3348696, baseEnd_3348696] using wordTrace_append hprefix tailTrace_3348696
  have hstable : (prefixWord ++ tailWord_3348696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348696).length < 2 ^ (prefixWord ++ tailWord_3348696).sum := by decide
  have hdescent : baseEnd_3348696 < baseStart_3348696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348717 : List Nat := [1, 5, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_3348717 : Nat := 118140960795 + 3348717 * 2 ^ 59
def prefixEnd_3348717 : Nat := 4983230072969 + 3 ^ 40 * 3348717 * 2
def baseEnd_3348717 : Nat := 1146334264588186575358025

theorem tailTrace_3348717 : CollatzResearch.WordTrace tailWord_3348717 prefixEnd_3348717 1146334264588186575358025 := by
  unfold tailWord_3348717
  simp only [CollatzResearch.WordTrace]
  refine ⟨122137743009177699176204405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81425162006118466117469603 122137743009177699176204405)
  ·
    refine ⟨11450413407110409297769163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122137743009177699176204405 11450413407110409297769163)
    ·
      refine ⟨17175620110665613946653745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11450413407110409297769163 17175620110665613946653745)
      ·
        refine ⟨12881715082999210459990309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17175620110665613946653745 12881715082999210459990309)
        ·
          refine ⟨2415321578062351961248183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12881715082999210459990309 2415321578062351961248183)
          ·
            refine ⟨3622982367093527941872275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415321578062351961248183 3622982367093527941872275)
            ·
              refine ⟨5434473550640291912808413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3622982367093527941872275 5434473550640291912808413)
              ·
                refine ⟨2037927581490109467303155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5434473550640291912808413 2037927581490109467303155)
                ·
                  refine ⟨3056891372235164200954733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037927581490109467303155 3056891372235164200954733)
                  ·
                    refine ⟨1146334264588186575358025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3056891372235164200954733 1146334264588186575358025)
                    ·
                      rfl

theorem cell22_3348717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_3348717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348717 prefixEnd_3348717 := by exact prefixLift 3348717
  have htrace : WordTrace (prefixWord ++ tailWord_3348717) baseStart_3348717 baseEnd_3348717 := by
    simpa [prefixWord, tailWord_3348717, baseEnd_3348717] using wordTrace_append hprefix tailTrace_3348717
  have hstable : (prefixWord ++ tailWord_3348717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348717).length < 2 ^ (prefixWord ++ tailWord_3348717).sum := by decide
  have hdescent : baseEnd_3348717 < baseStart_3348717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348726 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_3348726 : Nat := 118140960795 + 3348726 * 2 ^ 59
def prefixEnd_3348726 : Nat := 4983230072969 + 3 ^ 40 * 3348726 * 2
def baseEnd_3348726 : Nat := 1146337345472113551882997

theorem tailTrace_3348726 : CollatzResearch.WordTrace tailWord_3348726 prefixEnd_3348726 1146337345472113551882997 := by
  unfold tailWord_3348726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7633629454134068357080127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81425380844096729142188021 7633629454134068357080127)
  ·
    refine ⟨11450444181201102535620191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7633629454134068357080127 11450444181201102535620191)
    ·
      refine ⟨17175666271801653803430287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11450444181201102535620191 17175666271801653803430287)
      ·
        refine ⟨25763499407702480705145431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17175666271801653803430287 25763499407702480705145431)
        ·
          refine ⟨38645249111553721057718147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25763499407702480705145431 38645249111553721057718147)
          ·
            refine ⟨57967873667330581586577221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38645249111553721057718147 57967873667330581586577221)
            ·
              refine ⟨10868976312624484047483229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57967873667330581586577221 10868976312624484047483229)
              ·
                refine ⟨4075866117234181517806211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10868976312624484047483229 4075866117234181517806211)
                ·
                  refine ⟨6113799175851272276709317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075866117234181517806211 6113799175851272276709317)
                  ·
                    refine ⟨1146337345472113551882997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6113799175851272276709317 1146337345472113551882997)
                    ·
                      rfl

theorem cell22_3348726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_3348726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348726 prefixEnd_3348726 := by exact prefixLift 3348726
  have htrace : WordTrace (prefixWord ++ tailWord_3348726) baseStart_3348726 baseEnd_3348726 := by
    simpa [prefixWord, tailWord_3348726, baseEnd_3348726] using wordTrace_append hprefix tailTrace_3348726
  have hstable : (prefixWord ++ tailWord_3348726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348726).length < 2 ^ (prefixWord ++ tailWord_3348726).sum := by decide
  have hdescent : baseEnd_3348726 < baseStart_3348726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348739 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 4, 3]
def baseStart_3348739 : Nat := 118140960795 + 3348739 * 2 ^ 59
def prefixEnd_3348739 : Nat := 4983230072969 + 3 ^ 40 * 3348739 * 2
def baseEnd_3348739 : Nat := 1146341795637785851307957

theorem tailTrace_3348739 : CollatzResearch.WordTrace tailWord_3348739 prefixEnd_3348739 1146341795637785851307957 := by
  unfold tailWord_3348739
  simp only [CollatzResearch.WordTrace]
  refine ⟨122138545415097996933505271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81425696943398664622336847 122138545415097996933505271)
  ·
    refine ⟨183207818122646995400257907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122138545415097996933505271 183207818122646995400257907)
    ·
      refine ⟨274811727183970493100386861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183207818122646995400257907 274811727183970493100386861)
      ·
        refine ⟨103054397693988934912645073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274811727183970493100386861 103054397693988934912645073)
        ·
          refine ⟨77290798270491701184483805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103054397693988934912645073 77290798270491701184483805)
          ·
            refine ⟨28984049351434387944181427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77290798270491701184483805 28984049351434387944181427)
            ·
              refine ⟨43476074027151581916272141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28984049351434387944181427 43476074027151581916272141)
              ·
                refine ⟨16303527760181843218602053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43476074027151581916272141 16303527760181843218602053)
                ·
                  refine ⟨3056911455034095603487885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16303527760181843218602053 3056911455034095603487885)
                  ·
                    refine ⟨1146341795637785851307957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3056911455034095603487885 1146341795637785851307957)
                    ·
                      rfl

theorem cell22_3348739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 3].length) (baseStart_3348739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348739 prefixEnd_3348739 := by exact prefixLift 3348739
  have htrace : WordTrace (prefixWord ++ tailWord_3348739) baseStart_3348739 baseEnd_3348739 := by
    simpa [prefixWord, tailWord_3348739, baseEnd_3348739] using wordTrace_append hprefix tailTrace_3348739
  have hstable : (prefixWord ++ tailWord_3348739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348739).length < 2 ^ (prefixWord ++ tailWord_3348739).sum := by decide
  have hdescent : baseEnd_3348739 < baseStart_3348739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348784 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 7, 3]
def baseStart_3348784 : Nat := 118140960795 + 3348784 * 2 ^ 59
def prefixEnd_3348784 : Nat := 4983230072969 + 3 ^ 40 * 3348784 * 2
def baseEnd_3348784 : Nat := 1146357200057420733932819

theorem tailTrace_3348784 : CollatzResearch.WordTrace tailWord_3348784 prefixEnd_3348784 1146357200057420733932819 := by
  unfold tailWord_3348784
  simp only [CollatzResearch.WordTrace]
  refine ⟨61070093349967484809446703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81426791133289979745928937 61070093349967484809446703)
  ·
    refine ⟨91605140024951227214170055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61070093349967484809446703 91605140024951227214170055)
    ·
      refine ⟨137407710037426840821255083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91605140024951227214170055 137407710037426840821255083)
      ·
        refine ⟨206111565056140261231882625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137407710037426840821255083 206111565056140261231882625)
        ·
          refine ⟨154583673792105195923911969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206111565056140261231882625 154583673792105195923911969)
          ·
            refine ⟨115937755344078896942933977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154583673792105195923911969 115937755344078896942933977)
            ·
              refine ⟨86953316508059172707200483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115937755344078896942933977 86953316508059172707200483)
              ·
                refine ⟨130429974762088759060800725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86953316508059172707200483 130429974762088759060800725)
                ·
                  refine ⟨3056952533486455290487517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 130429974762088759060800725 3056952533486455290487517)
                  ·
                    refine ⟨1146357200057420733932819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3056952533486455290487517 1146357200057420733932819)
                    ·
                      rfl

theorem cell22_3348784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7, 3].length) (baseStart_3348784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348784 prefixEnd_3348784 := by exact prefixLift 3348784
  have htrace : WordTrace (prefixWord ++ tailWord_3348784) baseStart_3348784 baseEnd_3348784 := by
    simpa [prefixWord, tailWord_3348784, baseEnd_3348784] using wordTrace_append hprefix tailTrace_3348784
  have hstable : (prefixWord ++ tailWord_3348784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348784).length < 2 ^ (prefixWord ++ tailWord_3348784).sum := by decide
  have hdescent : baseEnd_3348784 < baseStart_3348784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348859 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 6]
def baseStart_3348859 : Nat := 118140960795 + 3348859 * 2 ^ 59
def prefixEnd_3348859 : Nat := 4983230072969 + 3 ^ 40 * 3348859 * 2
def baseEnd_3348859 : Nat := 382127624696715179435863

theorem tailTrace_3348859 : CollatzResearch.WordTrace tailWord_3348859 prefixEnd_3348859 382127624696715179435863 := by
  unfold tailWord_3348859
  simp only [CollatzResearch.WordTrace]
  refine ⟨122142922174663257427873631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81428614783108838285249087 122142922174663257427873631)
  ·
    refine ⟨183214383261994886141810447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122142922174663257427873631 183214383261994886141810447)
    ·
      refine ⟨274821574892992329212715671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183214383261994886141810447 274821574892992329212715671)
      ·
        refine ⟨412232362339488493819073507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274821574892992329212715671 412232362339488493819073507)
        ·
          refine ⟨618348543509232740728610261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412232362339488493819073507 618348543509232740728610261)
          ·
            refine ⟨14492543988497642360826803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 618348543509232740728610261 14492543988497642360826803)
            ·
              refine ⟨21738815982746463541240205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14492543988497642360826803 21738815982746463541240205)
              ·
                refine ⟨8152055993529923827965077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21738815982746463541240205 8152055993529923827965077)
                ·
                  refine ⟨382127624696715179435863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8152055993529923827965077 382127624696715179435863)
                  ·
                    rfl

theorem cell22_3348859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 6].length) (baseStart_3348859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348859 prefixEnd_3348859 := by exact prefixLift 3348859
  have htrace : WordTrace (prefixWord ++ tailWord_3348859) baseStart_3348859 baseEnd_3348859 := by
    simpa [prefixWord, tailWord_3348859, baseEnd_3348859] using wordTrace_append hprefix tailTrace_3348859
  have hstable : (prefixWord ++ tailWord_3348859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348859).length < 2 ^ (prefixWord ++ tailWord_3348859).sum := by decide
  have hdescent : baseEnd_3348859 < baseStart_3348859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348878 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_3348878 : Nat := 118140960795 + 3348878 * 2 ^ 59
def prefixEnd_3348878 : Nat := 4983230072969 + 3 ^ 40 * 3348878 * 2
def baseEnd_3348878 : Nat := 1146389378178435822082531

theorem tailTrace_3348878 : CollatzResearch.WordTrace tailWord_3348878 prefixEnd_3348878 1146389378178435822082531 := by
  unfold tailWord_3348878
  simp only [CollatzResearch.WordTrace]
  refine ⟨15267951895199302959101911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81429076774396282448543525 15267951895199302959101911)
  ·
    refine ⟨22901927842798954438652867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15267951895199302959101911 22901927842798954438652867)
    ·
      refine ⟨34352891764198431657979301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22901927842798954438652867 34352891764198431657979301)
      ·
        refine ⟨6441167205787205935871119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34352891764198431657979301 6441167205787205935871119)
        ·
          refine ⟨9661750808680808903806679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441167205787205935871119 9661750808680808903806679)
          ·
            refine ⟨14492626213021213355710019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9661750808680808903806679 14492626213021213355710019)
            ·
              refine ⟨21738939319531820033565029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14492626213021213355710019 21738939319531820033565029)
              ·
                refine ⟨4076051122412216256293443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21738939319531820033565029 4076051122412216256293443)
                ·
                  refine ⟨6114076683618324384440165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076051122412216256293443 6114076683618324384440165)
                  ·
                    refine ⟨1146389378178435822082531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114076683618324384440165 1146389378178435822082531)
                    ·
                      rfl

theorem cell22_3348878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_3348878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348878 prefixEnd_3348878 := by exact prefixLift 3348878
  have htrace : WordTrace (prefixWord ++ tailWord_3348878) baseStart_3348878 baseEnd_3348878 := by
    simpa [prefixWord, tailWord_3348878, baseEnd_3348878] using wordTrace_append hprefix tailTrace_3348878
  have hstable : (prefixWord ++ tailWord_3348878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348878).length < 2 ^ (prefixWord ++ tailWord_3348878).sum := by decide
  have hdescent : baseEnd_3348878 < baseStart_3348878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348889 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_3348889 : Nat := 118140960795 + 3348889 * 2 ^ 59
def prefixEnd_3348889 : Nat := 4983230072969 + 3 ^ 40 * 3348889 * 2
def baseEnd_3348889 : Nat := 1146393143703235460057497

theorem tailTrace_3348889 : CollatzResearch.WordTrace tailWord_3348889 prefixEnd_3348889 1146393143703235460057497 := by
  unfold tailWord_3348889
  simp only [CollatzResearch.WordTrace]
  refine ⟨122144016364554572551465721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81429344243036381700977147 122144016364554572551465721)
  ·
    refine ⟨91608012273415929413599291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122144016364554572551465721 91608012273415929413599291)
    ·
      refine ⟨137412018410123894120398937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91608012273415929413599291 137412018410123894120398937)
      ·
        refine ⟨103059013807592920590299203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137412018410123894120398937 103059013807592920590299203)
        ·
          refine ⟨154588520711389380885448805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103059013807592920590299203 154588520711389380885448805)
          ·
            refine ⟨28985347633385508916021651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154588520711389380885448805 28985347633385508916021651)
            ·
              refine ⟨43478021450078263374032477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28985347633385508916021651 43478021450078263374032477)
              ·
                refine ⟨16304258043779348765262179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43478021450078263374032477 16304258043779348765262179)
                ·
                  refine ⟨24456387065669023147893269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16304258043779348765262179 24456387065669023147893269)
                  ·
                    refine ⟨1146393143703235460057497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24456387065669023147893269 1146393143703235460057497)
                    ·
                      rfl

theorem cell22_3348889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_3348889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348889 prefixEnd_3348889 := by exact prefixLift 3348889
  have htrace : WordTrace (prefixWord ++ tailWord_3348889) baseStart_3348889 baseEnd_3348889 := by
    simpa [prefixWord, tailWord_3348889, baseEnd_3348889] using wordTrace_append hprefix tailTrace_3348889
  have hstable : (prefixWord ++ tailWord_3348889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348889).length < 2 ^ (prefixWord ++ tailWord_3348889).sum := by decide
  have hdescent : baseEnd_3348889 < baseStart_3348889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348921 : List Nat := [1, 2, 1, 4, 3, 2, 2, 7]
def baseStart_3348921 : Nat := 118140960795 + 3348921 * 2 ^ 59
def prefixEnd_3348921 : Nat := 4983230072969 + 3 ^ 40 * 3348921 * 2
def baseEnd_3348921 : Nat := 127378233106355338139711

theorem tailTrace_3348921 : CollatzResearch.WordTrace tailWord_3348921 prefixEnd_3348921 127378233106355338139711 := by
  unfold tailWord_3348921
  simp only [CollatzResearch.WordTrace]
  refine ⟨122145183500438642016630617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81430122333625761344420411 122145183500438642016630617)
  ·
    refine ⟨91608887625328981512472963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122145183500438642016630617 91608887625328981512472963)
    ·
      refine ⟨137413331437993472268709445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91608887625328981512472963 137413331437993472268709445)
      ·
        refine ⟨25764999644623776050383021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137413331437993472268709445 25764999644623776050383021)
        ·
          refine ⟨9661874866733916018893633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25764999644623776050383021 9661874866733916018893633)
          ·
            refine ⟨7246406150050437014170225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9661874866733916018893633 7246406150050437014170225)
            ·
              refine ⟨5434804612537827760627669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7246406150050437014170225 5434804612537827760627669)
              ·
                refine ⟨127378233106355338139711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5434804612537827760627669 127378233106355338139711)
                ·
                  rfl

theorem cell22_3348921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 7].length) (baseStart_3348921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348921 prefixEnd_3348921 := by exact prefixLift 3348921
  have htrace : WordTrace (prefixWord ++ tailWord_3348921) baseStart_3348921 baseEnd_3348921 := by
    simpa [prefixWord, tailWord_3348921, baseEnd_3348921] using wordTrace_append hprefix tailTrace_3348921
  have hstable : (prefixWord ++ tailWord_3348921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348921).length < 2 ^ (prefixWord ++ tailWord_3348921).sum := by decide
  have hdescent : baseEnd_3348921 < baseStart_3348921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348925 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_3348925 : Nat := 118140960795 + 3348925 * 2 ^ 59
def prefixEnd_3348925 : Nat := 4983230072969 + 3 ^ 40 * 3348925 * 2
def baseEnd_3348925 : Nat := 1146405467238943366157387

theorem tailTrace_3348925 : CollatzResearch.WordTrace tailWord_3348925 prefixEnd_3348925 1146405467238943366157387 := by
  unfold tailWord_3348925
  simp only [CollatzResearch.WordTrace]
  refine ⟨122145329392424150699776229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81430219594949433799850819 122145329392424150699776229)
  ·
    refine ⟨22902249261079528256208043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122145329392424150699776229 22902249261079528256208043)
    ·
      refine ⟨34353373891619292384312065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22902249261079528256208043 34353373891619292384312065)
      ·
        refine ⟨25765030418714469288234049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34353373891619292384312065 25765030418714469288234049)
        ·
          refine ⟨19323772814035851966175537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25765030418714469288234049 19323772814035851966175537)
          ·
            refine ⟨14492829610526888974631653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19323772814035851966175537 14492829610526888974631653)
            ·
              refine ⟨2717405551973791682743435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14492829610526888974631653 2717405551973791682743435)
              ·
                refine ⟨4076108327960687524115153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717405551973791682743435 4076108327960687524115153)
                ·
                  refine ⟨3057081245970515643086365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4076108327960687524115153 3057081245970515643086365)
                  ·
                    refine ⟨1146405467238943366157387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3057081245970515643086365 1146405467238943366157387)
                    ·
                      rfl

theorem cell22_3348925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_3348925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348925 prefixEnd_3348925 := by exact prefixLift 3348925
  have htrace : WordTrace (prefixWord ++ tailWord_3348925) baseStart_3348925 baseEnd_3348925 := by
    simpa [prefixWord, tailWord_3348925, baseEnd_3348925] using wordTrace_append hprefix tailTrace_3348925
  have hstable : (prefixWord ++ tailWord_3348925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348925).length < 2 ^ (prefixWord ++ tailWord_3348925).sum := by decide
  have hdescent : baseEnd_3348925 < baseStart_3348925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348929 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3348929 : Nat := 118140960795 + 3348929 * 2 ^ 59
def prefixEnd_3348929 : Nat := 4983230072969 + 3 ^ 40 * 3348929 * 2
def baseEnd_3348929 : Nat := 1146406836520688689057375

theorem tailTrace_3348929 : CollatzResearch.WordTrace tailWord_3348929 prefixEnd_3348929 1146406836520688689057375 := by
  unfold tailWord_3348929
  simp only [CollatzResearch.WordTrace]
  refine ⟨122145475284409659382921841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81430316856273106255281227 122145475284409659382921841)
  ·
    refine ⟨91609106463307244537191381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122145475284409659382921841 91609106463307244537191381)
    ·
      refine ⟨2147088432733763543840423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 91609106463307244537191381 2147088432733763543840423)
      ·
        refine ⟨3220632649100645315760635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147088432733763543840423 3220632649100645315760635)
        ·
          refine ⟨4830948973650967973640953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3220632649100645315760635 4830948973650967973640953)
          ·
            refine ⟨3623211730238225980230715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4830948973650967973640953 3623211730238225980230715)
            ·
              refine ⟨5434817595357338970346073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623211730238225980230715 5434817595357338970346073)
              ·
                refine ⟨4076113196518004227759555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5434817595357338970346073 4076113196518004227759555)
                ·
                  refine ⟨6114169794777006341639333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076113196518004227759555 6114169794777006341639333)
                  ·
                    refine ⟨1146406836520688689057375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114169794777006341639333 1146406836520688689057375)
                    ·
                      rfl

theorem cell22_3348929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3348929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3348929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3348929 prefixEnd_3348929 := by exact prefixLift 3348929
  have htrace : WordTrace (prefixWord ++ tailWord_3348929) baseStart_3348929 baseEnd_3348929 := by
    simpa [prefixWord, tailWord_3348929, baseEnd_3348929] using wordTrace_append hprefix tailTrace_3348929
  have hstable : (prefixWord ++ tailWord_3348929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348929).length < 2 ^ (prefixWord ++ tailWord_3348929).sum := by decide
  have hdescent : baseEnd_3348929 < baseStart_3348929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349013 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_3349013 : Nat := 118140960795 + 3349013 * 2 ^ 59
def prefixEnd_3349013 : Nat := 4983230072969 + 3 ^ 40 * 3349013 * 2
def baseEnd_3349013 : Nat := 1146435591437340469957117

theorem tailTrace_3349013 : CollatzResearch.WordTrace tailWord_3349013 prefixEnd_3349013 1146435591437340469957117 := by
  unfold tailWord_3349013
  simp only [CollatzResearch.WordTrace]
  refine ⟨122148539016105341728979693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81432359344070227819319795 122148539016105341728979693)
  ·
    refine ⟨45805702131039503148367385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122148539016105341728979693 45805702131039503148367385)
    ·
      refine ⟨34354276598279627361275539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45805702131039503148367385 34354276598279627361275539)
      ·
        refine ⟨51531414897419441041913309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34354276598279627361275539 51531414897419441041913309)
        ·
          refine ⟨19324280586532290390717491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51531414897419441041913309 19324280586532290390717491)
          ·
            refine ⟨28986420879798435586076237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19324280586532290390717491 28986420879798435586076237)
            ·
              refine ⟨10869907829924413344778589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28986420879798435586076237 10869907829924413344778589)
              ·
                refine ⟨4076215436221655004291971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10869907829924413344778589 4076215436221655004291971)
                ·
                  refine ⟨6114323154332482506437957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076215436221655004291971 6114323154332482506437957)
                  ·
                    refine ⟨1146435591437340469957117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114323154332482506437957 1146435591437340469957117)
                    ·
                      rfl

theorem cell22_3349013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_3349013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349013 prefixEnd_3349013 := by exact prefixLift 3349013
  have htrace : WordTrace (prefixWord ++ tailWord_3349013) baseStart_3349013 baseEnd_3349013 := by
    simpa [prefixWord, tailWord_3349013, baseEnd_3349013] using wordTrace_append hprefix tailTrace_3349013
  have hstable : (prefixWord ++ tailWord_3349013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349013).length < 2 ^ (prefixWord ++ tailWord_3349013).sum := by decide
  have hdescent : baseEnd_3349013 < baseStart_3349013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349041 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_3349041 : Nat := 118140960795 + 3349041 * 2 ^ 59
def prefixEnd_3349041 : Nat := 4983230072969 + 3 ^ 40 * 3349041 * 2
def baseEnd_3349041 : Nat := 1146445176409557730257031

theorem tailTrace_3349041 : CollatzResearch.WordTrace tailWord_3349041 prefixEnd_3349041 1146445176409557730257031 := by
  unfold tailWord_3349041
  simp only [CollatzResearch.WordTrace]
  refine ⟨122149560260003902510998977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81433040173335935007332651 122149560260003902510998977)
  ·
    refine ⟨91612170195002926883249233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122149560260003902510998977 91612170195002926883249233)
    ·
      refine ⟨68709127646252195162436925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91612170195002926883249233 68709127646252195162436925)
      ·
        refine ⟨25765922867344573185913847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68709127646252195162436925 25765922867344573185913847)
        ·
          refine ⟨38648884301016859778870771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25765922867344573185913847 38648884301016859778870771)
          ·
            refine ⟨57973326451525289668306157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38648884301016859778870771 57973326451525289668306157)
            ·
              refine ⟨21739997419321983625614809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57973326451525289668306157 21739997419321983625614809)
              ·
                refine ⟨16304998064491487719211107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21739997419321983625614809 16304998064491487719211107)
                ·
                  refine ⟨24457497096737231578816661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16304998064491487719211107 24457497096737231578816661)
                  ·
                    refine ⟨1146445176409557730257031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24457497096737231578816661 1146445176409557730257031)
                    ·
                      rfl

theorem cell22_3349041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_3349041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349041 prefixEnd_3349041 := by exact prefixLift 3349041
  have htrace : WordTrace (prefixWord ++ tailWord_3349041) baseStart_3349041 baseEnd_3349041 := by
    simpa [prefixWord, tailWord_3349041, baseEnd_3349041] using wordTrace_append hprefix tailTrace_3349041
  have hstable : (prefixWord ++ tailWord_3349041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349041).length < 2 ^ (prefixWord ++ tailWord_3349041).sum := by decide
  have hdescent : baseEnd_3349041 < baseStart_3349041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349150 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3349150 : Nat := 118140960795 + 3349150 * 2 ^ 59
def prefixEnd_3349150 : Nat := 4983230072969 + 3 ^ 40 * 3349150 * 2
def baseEnd_3349150 : Nat := 1146482489337117779281697

theorem tailTrace_3349150 : CollatzResearch.WordTrace tailWord_3349150 prefixEnd_3349150 1146482489337117779281697 := by
  unfold tailWord_3349150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15269191977076126765839613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81435690544406009417811269 15269191977076126765839613)
  ·
    refine ⟨5725946991403547537189855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15269191977076126765839613 5725946991403547537189855)
    ·
      refine ⟨8588920487105321305784783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5725946991403547537189855 8588920487105321305784783)
      ·
        refine ⟨12883380730657981958677175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588920487105321305784783 12883380730657981958677175)
        ·
          refine ⟨19325071095986972938015763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12883380730657981958677175 19325071095986972938015763)
          ·
            refine ⟨28987606643980459407023645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19325071095986972938015763 28987606643980459407023645)
            ·
              refine ⟨10870352491492672277633867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28987606643980459407023645 10870352491492672277633867)
              ·
                refine ⟨16305528737239008416450801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10870352491492672277633867 16305528737239008416450801)
                ·
                  refine ⟨12229146552929256312338101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16305528737239008416450801 12229146552929256312338101)
                  ·
                    refine ⟨1146482489337117779281697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12229146552929256312338101 1146482489337117779281697)
                    ·
                      rfl

theorem cell22_3349150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3349150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349150 prefixEnd_3349150 := by exact prefixLift 3349150
  have htrace : WordTrace (prefixWord ++ tailWord_3349150) baseStart_3349150 baseEnd_3349150 := by
    simpa [prefixWord, tailWord_3349150, baseEnd_3349150] using wordTrace_append hprefix tailTrace_3349150
  have hstable : (prefixWord ++ tailWord_3349150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349150).length < 2 ^ (prefixWord ++ tailWord_3349150).sum := by decide
  have hdescent : baseEnd_3349150 < baseStart_3349150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349165 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3349165 : Nat := 118140960795 + 3349165 * 2 ^ 59
def prefixEnd_3349165 : Nat := 4983230072969 + 3 ^ 40 * 3349165 * 2
def baseEnd_3349165 : Nat := 1146487624143662740156651

theorem tailTrace_3349165 : CollatzResearch.WordTrace tailWord_3349165 prefixEnd_3349165 1146487624143662740156651 := by
  unfold tailWord_3349165
  simp only [CollatzResearch.WordTrace]
  refine ⟨122154082911554671688512949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81436055274369781125675299 122154082911554671688512949)
  ·
    refine ⟨11451945272958250470798089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122154082911554671688512949 11451945272958250470798089)
    ·
      refine ⟨8588958954718687853098567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11451945272958250470798089 8588958954718687853098567)
      ·
        refine ⟨12883438432078031779647851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588958954718687853098567 12883438432078031779647851)
        ·
          refine ⟨19325157648117047669471777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12883438432078031779647851 19325157648117047669471777)
          ·
            refine ⟨14493868236087785752103833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19325157648117047669471777 14493868236087785752103833)
            ·
              refine ⟨10870401177065839314077875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14493868236087785752103833 10870401177065839314077875)
              ·
                refine ⟨16305601765598758971116813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10870401177065839314077875 16305601765598758971116813)
                ·
                  refine ⟨6114600662099534614168805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16305601765598758971116813 6114600662099534614168805)
                  ·
                    refine ⟨1146487624143662740156651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114600662099534614168805 1146487624143662740156651)
                    ·
                      rfl

theorem cell22_3349165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3349165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349165 prefixEnd_3349165 := by exact prefixLift 3349165
  have htrace : WordTrace (prefixWord ++ tailWord_3349165) baseStart_3349165 baseEnd_3349165 := by
    simpa [prefixWord, tailWord_3349165, baseEnd_3349165] using wordTrace_append hprefix tailTrace_3349165
  have hstable : (prefixWord ++ tailWord_3349165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349165).length < 2 ^ (prefixWord ++ tailWord_3349165).sum := by decide
  have hdescent : baseEnd_3349165 < baseStart_3349165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349178 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_3349178 : Nat := 118140960795 + 3349178 * 2 ^ 59
def prefixEnd_3349178 : Nat := 4983230072969 + 3 ^ 40 * 3349178 * 2
def baseEnd_3349178 : Nat := 1146492074309335039581611

theorem tailTrace_3349178 : CollatzResearch.WordTrace tailWord_3349178 prefixEnd_3349178 1146492074309335039581611 := by
  unfold tailWord_3349178
  simp only [CollatzResearch.WordTrace]
  refine ⟨30538639265126893727184047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81436371373671716605824125 30538639265126893727184047)
  ·
    refine ⟨45807958897690340590776071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30538639265126893727184047 45807958897690340590776071)
    ·
      refine ⟨68711938346535510886164107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45807958897690340590776071 68711938346535510886164107)
      ·
        refine ⟨103067907519803266329246161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68711938346535510886164107 103067907519803266329246161)
        ·
          refine ⟨77300930639852449746934621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103067907519803266329246161 77300930639852449746934621)
          ·
            refine ⟨28987848989944668655100483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77300930639852449746934621 28987848989944668655100483)
            ·
              refine ⟨43481773484917002982650725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28987848989944668655100483 43481773484917002982650725)
              ·
                refine ⟨8152832528421938059247011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43481773484917002982650725 8152832528421938059247011)
                ·
                  refine ⟨12229248792632907088870517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8152832528421938059247011 12229248792632907088870517)
                  ·
                    refine ⟨1146492074309335039581611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12229248792632907088870517 1146492074309335039581611)
                    ·
                      rfl

theorem cell22_3349178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_3349178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349178 prefixEnd_3349178 := by exact prefixLift 3349178
  have htrace : WordTrace (prefixWord ++ tailWord_3349178) baseStart_3349178 baseEnd_3349178 := by
    simpa [prefixWord, tailWord_3349178, baseEnd_3349178] using wordTrace_append hprefix tailTrace_3349178
  have hstable : (prefixWord ++ tailWord_3349178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349178).length < 2 ^ (prefixWord ++ tailWord_3349178).sum := by decide
  have hdescent : baseEnd_3349178 < baseStart_3349178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349212 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3349212 : Nat := 118140960795 + 3349212 * 2 ^ 59
def prefixEnd_3349212 : Nat := 4983230072969 + 3 ^ 40 * 3349212 * 2
def baseEnd_3349212 : Nat := 1146503713204170284231507

theorem tailTrace_3349212 : CollatzResearch.WordTrace tailWord_3349212 prefixEnd_3349212 1146503713204170284231507 := by
  unfold tailWord_3349212
  simp only [CollatzResearch.WordTrace]
  refine ⟨61077898571192199357736945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81437198094922932476982593 61077898571192199357736945)
  ·
    refine ⟨45808423928394149518302709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61077898571192199357736945 45808423928394149518302709)
    ·
      refine ⟨4294539743286951517340879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45808423928394149518302709 4294539743286951517340879)
      ·
        refine ⟨6441809614930427276011319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294539743286951517340879 6441809614930427276011319)
        ·
          refine ⟨9662714422395640914016979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441809614930427276011319 9662714422395640914016979)
          ·
            refine ⟨14494071633593461371025469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9662714422395640914016979 14494071633593461371025469)
            ·
              refine ⟨5435276862597548014134551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14494071633593461371025469 5435276862597548014134551)
              ·
                refine ⟨8152915293896322021201827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435276862597548014134551 8152915293896322021201827)
                ·
                  refine ⟨12229372940844483031802741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8152915293896322021201827 12229372940844483031802741)
                  ·
                    refine ⟨1146503713204170284231507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12229372940844483031802741 1146503713204170284231507)
                    ·
                      rfl

theorem cell22_3349212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3349212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349212 prefixEnd_3349212 := by exact prefixLift 3349212
  have htrace : WordTrace (prefixWord ++ tailWord_3349212) baseStart_3349212 baseEnd_3349212 := by
    simpa [prefixWord, tailWord_3349212, baseEnd_3349212] using wordTrace_append hprefix tailTrace_3349212
  have hstable : (prefixWord ++ tailWord_3349212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349212).length < 2 ^ (prefixWord ++ tailWord_3349212).sum := by decide
  have hdescent : baseEnd_3349212 < baseStart_3349212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349257 : List Nat := [1, 2, 1, 1, 3, 2, 2, 6, 1, 3]
def baseStart_3349257 : Nat := 118140960795 + 3349257 * 2 ^ 59
def prefixEnd_3349257 : Nat := 4983230072969 + 3 ^ 40 * 3349257 * 2
def baseEnd_3349257 : Nat := 1146519117623805166856369

theorem tailTrace_3349257 : CollatzResearch.WordTrace tailWord_3349257 prefixEnd_3349257 1146519117623805166856369 := by
  unfold tailWord_3349257
  simp only [CollatzResearch.WordTrace]
  refine ⟨122157438427221371400862025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81438292284814247600574683 122157438427221371400862025)
  ·
    refine ⟨91618078820416028550646519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122157438427221371400862025 91618078820416028550646519)
    ·
      refine ⟨137427118230624042825969779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91618078820416028550646519 137427118230624042825969779)
      ·
        refine ⟨206140677345936064238954669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137427118230624042825969779 206140677345936064238954669)
        ·
          refine ⟨77302754004726024089608001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206140677345936064238954669 77302754004726024089608001)
          ·
            refine ⟨57977065503544518067206001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77302754004726024089608001 57977065503544518067206001)
            ·
              refine ⟨43482799127658388550404501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57977065503544518067206001 43482799127658388550404501)
              ·
                refine ⟨2038256209108986963300211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43482799127658388550404501 2038256209108986963300211)
                ·
                  refine ⟨3057384313663480444950317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038256209108986963300211 3057384313663480444950317)
                  ·
                    refine ⟨1146519117623805166856369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3057384313663480444950317 1146519117623805166856369)
                    ·
                      rfl

theorem cell22_3349257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 1, 3].length) (baseStart_3349257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349257 prefixEnd_3349257 := by exact prefixLift 3349257
  have htrace : WordTrace (prefixWord ++ tailWord_3349257) baseStart_3349257 baseEnd_3349257 := by
    simpa [prefixWord, tailWord_3349257, baseEnd_3349257] using wordTrace_append hprefix tailTrace_3349257
  have hstable : (prefixWord ++ tailWord_3349257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349257).length < 2 ^ (prefixWord ++ tailWord_3349257).sum := by decide
  have hdescent : baseEnd_3349257 < baseStart_3349257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349332 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 6]
def baseStart_3349332 : Nat := 118140960795 + 3349332 * 2 ^ 59
def prefixEnd_3349332 : Nat := 4983230072969 + 3 ^ 40 * 3349332 * 2
def baseEnd_3349332 : Nat := 382181597218843323743713

theorem tailTrace_3349332 : CollatzResearch.WordTrace tailWord_3349332 prefixEnd_3349332 382181597218843323743713 := by
  unfold tailWord_3349332
  simp only [CollatzResearch.WordTrace]
  refine ⟨61080086950974829604921125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81440115934633106139894833 61080086950974829604921125)
  ·
    refine ⟨11452516303307780550922711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61080086950974829604921125 11452516303307780550922711)
    ·
      refine ⟨17178774454961670826384067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11452516303307780550922711 17178774454961670826384067)
      ·
        refine ⟨25768161682442506239576101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17178774454961670826384067 25768161682442506239576101)
        ·
          refine ⟨4831530315457969919920519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25768161682442506239576101 4831530315457969919920519)
          ·
            refine ⟨7247295473186954879880779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4831530315457969919920519 7247295473186954879880779)
            ·
              refine ⟨10870943209780432319821169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7247295473186954879880779 10870943209780432319821169)
              ·
                refine ⟨8153207407335324239865877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10870943209780432319821169 8153207407335324239865877)
                ·
                  refine ⟨382181597218843323743713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8153207407335324239865877 382181597218843323743713)
                  ·
                    rfl

theorem cell22_3349332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_3349332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349332 prefixEnd_3349332 := by exact prefixLift 3349332
  have htrace : WordTrace (prefixWord ++ tailWord_3349332) baseStart_3349332 baseEnd_3349332 := by
    simpa [prefixWord, tailWord_3349332, baseEnd_3349332] using wordTrace_append hprefix tailTrace_3349332
  have hstable : (prefixWord ++ tailWord_3349332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349332).length < 2 ^ (prefixWord ++ tailWord_3349332).sum := by decide
  have hdescent : baseEnd_3349332 < baseStart_3349332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349345 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 2, 4]
def baseStart_3349345 : Nat := 118140960795 + 3349345 * 2 ^ 59
def prefixEnd_3349345 : Nat := 4983230072969 + 3 ^ 40 * 3349345 * 2
def baseEnd_3349345 : Nat := 1146549241822202270656099

theorem tailTrace_3349345 : CollatzResearch.WordTrace tailWord_3349345 prefixEnd_3349345 1146549241822202270656099 := by
  unfold tailWord_3349345
  simp only [CollatzResearch.WordTrace]
  refine ⟨122160648050902562430065489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81440432033935041620043659 122160648050902562430065489)
  ·
    refine ⟨91620486038176921822549117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122160648050902562430065489 91620486038176921822549117)
    ·
      refine ⟨34357682264316345683455919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91620486038176921822549117 34357682264316345683455919)
      ·
        refine ⟨51536523396474518525183879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34357682264316345683455919 51536523396474518525183879)
        ·
          refine ⟨77304785094711777787775819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51536523396474518525183879 77304785094711777787775819)
          ·
            refine ⟨115957177642067666681663729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77304785094711777787775819 115957177642067666681663729)
            ·
              refine ⟨86967883231550750011247797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115957177642067666681663729 86967883231550750011247797)
              ·
                refine ⟨8153239052957882813554481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86967883231550750011247797 8153239052957882813554481)
                ·
                  refine ⟨6114929289718412110165861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8153239052957882813554481 6114929289718412110165861)
                  ·
                    refine ⟨1146549241822202270656099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114929289718412110165861 1146549241822202270656099)
                    ·
                      rfl

theorem cell22_3349345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_3349345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349345 prefixEnd_3349345 := by exact prefixLift 3349345
  have htrace : WordTrace (prefixWord ++ tailWord_3349345) baseStart_3349345 baseEnd_3349345 := by
    simpa [prefixWord, tailWord_3349345, baseEnd_3349345] using wordTrace_append hprefix tailTrace_3349345
  have hstable : (prefixWord ++ tailWord_3349345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349345).length < 2 ^ (prefixWord ++ tailWord_3349345).sum := by decide
  have hdescent : baseEnd_3349345 < baseStart_3349345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349405 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 9]
def baseStart_3349405 : Nat := 118140960795 + 3349405 * 2 ^ 59
def prefixEnd_3349405 : Nat := 4983230072969 + 3 ^ 40 * 3349405 * 2
def baseEnd_3349405 : Nat := 382189927016127371385305

theorem tailTrace_3349405 : CollatzResearch.WordTrace tailWord_3349405 prefixEnd_3349405 382189927016127371385305 := by
  unfold tailWord_3349405
  simp only [CollatzResearch.WordTrace]
  refine ⟨122162836430685192677249669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81441890953790128451499779 122162836430685192677249669)
  ·
    refine ⟨22905531830753473626984313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122162836430685192677249669 22905531830753473626984313)
    ·
      refine ⟨17179148873065105220238235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22905531830753473626984313 17179148873065105220238235)
      ·
        refine ⟨25768723309597657830357353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17179148873065105220238235 25768723309597657830357353)
        ·
          refine ⟨19326542482198243372768015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25768723309597657830357353 19326542482198243372768015)
          ·
            refine ⟨28989813723297365059152023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19326542482198243372768015 28989813723297365059152023)
            ·
              refine ⟨43484720584946047588728035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28989813723297365059152023 43484720584946047588728035)
              ·
                refine ⟨65227080877419071383092053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43484720584946047588728035 65227080877419071383092053)
                ·
                  refine ⟨382189927016127371385305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65227080877419071383092053 382189927016127371385305)
                  ·
                    rfl

theorem cell22_3349405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_3349405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349405 prefixEnd_3349405 := by exact prefixLift 3349405
  have htrace : WordTrace (prefixWord ++ tailWord_3349405) baseStart_3349405 baseEnd_3349405 := by
    simpa [prefixWord, tailWord_3349405, baseEnd_3349405] using wordTrace_append hprefix tailTrace_3349405
  have hstable : (prefixWord ++ tailWord_3349405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349405).length < 2 ^ (prefixWord ++ tailWord_3349405).sum := by decide
  have hdescent : baseEnd_3349405 < baseStart_3349405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349450 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_3349450 : Nat := 118140960795 + 3349450 * 2 ^ 59
def prefixEnd_3349450 : Nat := 4983230072969 + 3 ^ 40 * 3349450 * 2
def baseEnd_3349450 : Nat := 382195061822672332260259

theorem tailTrace_3349450 : CollatzResearch.WordTrace tailWord_3349450 prefixEnd_3349450 382195061822672332260259 := by
  unfold tailWord_3349450
  simp only [CollatzResearch.WordTrace]
  refine ⟨30541119428880541340659451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81442985143681443575091869 30541119428880541340659451)
  ·
    refine ⟨45811679143320812010989177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30541119428880541340659451 45811679143320812010989177)
    ·
      refine ⟨34358759357490609008241883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45811679143320812010989177 34358759357490609008241883)
      ·
        refine ⟨51538139036235913512362825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34358759357490609008241883 51538139036235913512362825)
        ·
          refine ⟨38653604277176935134272119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51538139036235913512362825 38653604277176935134272119)
          ·
            refine ⟨57980406415765402701408179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38653604277176935134272119 57980406415765402701408179)
            ·
              refine ⟨86970609623648104052112269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57980406415765402701408179 86970609623648104052112269)
              ·
                refine ⟨32613978608868039019542101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86970609623648104052112269 32613978608868039019542101)
                ·
                  refine ⟨382195061822672332260259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32613978608868039019542101 382195061822672332260259)
                  ·
                    rfl

theorem cell22_3349450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_3349450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349450 prefixEnd_3349450 := by exact prefixLift 3349450
  have htrace : WordTrace (prefixWord ++ tailWord_3349450) baseStart_3349450 baseEnd_3349450 := by
    simpa [prefixWord, tailWord_3349450, baseEnd_3349450] using wordTrace_append hprefix tailTrace_3349450
  have hstable : (prefixWord ++ tailWord_3349450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349450).length < 2 ^ (prefixWord ++ tailWord_3349450).sum := by decide
  have hdescent : baseEnd_3349450 < baseStart_3349450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349452 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_3349452 : Nat := 118140960795 + 3349452 * 2 ^ 59
def prefixEnd_3349452 : Nat := 4983230072969 + 3 ^ 40 * 3349452 * 2
def baseEnd_3349452 : Nat := 1146585870108889658230771

theorem tailTrace_3349452 : CollatzResearch.WordTrace tailWord_3349452 prefixEnd_3349452 1146585870108889658230771 := by
  unfold tailWord_3349452
  simp only [CollatzResearch.WordTrace]
  refine ⟨61082275330757459852105305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81443033774343279802807073 61082275330757459852105305)
  ·
    refine ⟨45811706498068094889078979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61082275330757459852105305 45811706498068094889078979)
    ·
      refine ⟨68717559747102142333618469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45811706498068094889078979 68717559747102142333618469)
      ·
        refine ⟨12884542452581651687553463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68717559747102142333618469 12884542452581651687553463)
        ·
          refine ⟨19326813678872477531330195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12884542452581651687553463 19326813678872477531330195)
          ·
            refine ⟨28990220518308716296995293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19326813678872477531330195 28990220518308716296995293)
            ·
              refine ⟨10871332694365768611373235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28990220518308716296995293 10871332694365768611373235)
              ·
                refine ⟨16306999041548652917059853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10871332694365768611373235 16306999041548652917059853)
                ·
                  refine ⟨6115124640580744843897445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16306999041548652917059853 6115124640580744843897445)
                  ·
                    refine ⟨1146585870108889658230771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6115124640580744843897445 1146585870108889658230771)
                    ·
                      rfl

theorem cell22_3349452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_3349452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349452 prefixEnd_3349452 := by exact prefixLift 3349452
  have htrace : WordTrace (prefixWord ++ tailWord_3349452) baseStart_3349452 baseEnd_3349452 := by
    simpa [prefixWord, tailWord_3349452, baseEnd_3349452] using wordTrace_append hprefix tailTrace_3349452
  have hstable : (prefixWord ++ tailWord_3349452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349452).length < 2 ^ (prefixWord ++ tailWord_3349452).sum := by decide
  have hdescent : baseEnd_3349452 < baseStart_3349452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349477 : List Nat := [1, 3, 1, 6, 2, 1, 2, 2, 1, 3]
def baseStart_3349477 : Nat := 118140960795 + 3349477 * 2 ^ 59
def prefixEnd_3349477 : Nat := 4983230072969 + 3 ^ 40 * 3349477 * 2
def baseEnd_3349477 : Nat := 1146594428119797926355695

theorem tailTrace_3349477 : CollatzResearch.WordTrace tailWord_3349477 prefixEnd_3349477 1146594428119797926355695 := by
  unfold tailWord_3349477
  simp only [CollatzResearch.WordTrace]
  refine ⟨122165462486424348973870685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81443641657616232649247123 122165462486424348973870685)
  ·
    refine ⟨45812048432409130865201507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122165462486424348973870685 45812048432409130865201507)
    ·
      refine ⟨68718072648613696297802261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45812048432409130865201507 68718072648613696297802261)
      ·
        refine ⟨3221159655403767013959481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68718072648613696297802261 3221159655403767013959481)
        ·
          refine ⟨2415869741552825260469611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3221159655403767013959481 2415869741552825260469611)
          ·
            refine ⟨3623804612329237890704417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415869741552825260469611 3623804612329237890704417)
            ·
              refine ⟨2717853459246928418028313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3623804612329237890704417 2717853459246928418028313)
              ·
                refine ⟨2038390094435196313521235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2717853459246928418028313 2038390094435196313521235)
                ·
                  refine ⟨3057585141652794470281853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038390094435196313521235 3057585141652794470281853)
                  ·
                    refine ⟨1146594428119797926355695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3057585141652794470281853 1146594428119797926355695)
                    ·
                      rfl

theorem cell22_3349477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_3349477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349477 prefixEnd_3349477 := by exact prefixLift 3349477
  have htrace : WordTrace (prefixWord ++ tailWord_3349477) baseStart_3349477 baseEnd_3349477 := by
    simpa [prefixWord, tailWord_3349477, baseEnd_3349477] using wordTrace_append hprefix tailTrace_3349477
  have hstable : (prefixWord ++ tailWord_3349477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349477).length < 2 ^ (prefixWord ++ tailWord_3349477).sum := by decide
  have hdescent : baseEnd_3349477 < baseStart_3349477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349514 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_3349514 : Nat := 118140960795 + 3349514 * 2 ^ 59
def prefixEnd_3349514 : Nat := 4983230072969 + 3 ^ 40 * 3349514 * 2
def baseEnd_3349514 : Nat := 1146607093975942163180581

theorem tailTrace_3349514 : CollatzResearch.WordTrace tailWord_3349514 prefixEnd_3349514 1146607093975942163180581 := by
  unfold tailWord_3349514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30541702996822576073241899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81444541324860202861978397 30541702996822576073241899)
  ·
    refine ⟨45812554495233864109862849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30541702996822576073241899 45812554495233864109862849)
    ·
      refine ⟨34359415871425398082397137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45812554495233864109862849 34359415871425398082397137)
      ·
        refine ⟨25769561903569048561797853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34359415871425398082397137 25769561903569048561797853)
        ·
          refine ⟨9663585713838393210674195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25769561903569048561797853 9663585713838393210674195)
          ·
            refine ⟨14495378570757589816011293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9663585713838393210674195 14495378570757589816011293)
            ·
              refine ⟨5435766964034096181004235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14495378570757589816011293 5435766964034096181004235)
              ·
                refine ⟨8153650446051144271506353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435766964034096181004235 8153650446051144271506353)
                ·
                  refine ⟨6115237834538358203629765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8153650446051144271506353 6115237834538358203629765)
                  ·
                    refine ⟨1146607093975942163180581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6115237834538358203629765 1146607093975942163180581)
                    ·
                      rfl

theorem cell22_3349514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_3349514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349514 prefixEnd_3349514 := by exact prefixLift 3349514
  have htrace : WordTrace (prefixWord ++ tailWord_3349514) baseStart_3349514 baseEnd_3349514 := by
    simpa [prefixWord, tailWord_3349514, baseEnd_3349514] using wordTrace_append hprefix tailTrace_3349514
  have hstable : (prefixWord ++ tailWord_3349514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349514).length < 2 ^ (prefixWord ++ tailWord_3349514).sum := by decide
  have hdescent : baseEnd_3349514 < baseStart_3349514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349533 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_3349533 : Nat := 118140960795 + 3349533 * 2 ^ 59
def prefixEnd_3349533 : Nat := 4983230072969 + 3 ^ 40 * 3349533 * 2
def baseEnd_3349533 : Nat := 1146613598064232446955523

theorem tailTrace_3349533 : CollatzResearch.WordTrace tailWord_3349533 prefixEnd_3349533 1146613598064232446955523 := by
  unfold tailWord_3349533
  simp only [CollatzResearch.WordTrace]
  refine ⟨122167504974221470537909253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81445003316147647025272835 122167504974221470537909253)
  ·
    refine ⟨22906407182666525725857985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122167504974221470537909253 22906407182666525725857985)
    ·
      refine ⟨17179805386999894294393489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22906407182666525725857985 17179805386999894294393489)
      ·
        refine ⟨12884854040249920720795117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17179805386999894294393489 12884854040249920720795117)
        ·
          refine ⟨4831820265093720270298169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12884854040249920720795117 4831820265093720270298169)
          ·
            refine ⟨3623865198820290202723627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4831820265093720270298169 3623865198820290202723627)
            ·
              refine ⟨5435797798230435304085441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623865198820290202723627 5435797798230435304085441)
              ·
                refine ⟨4076848348672826478064081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5435797798230435304085441 4076848348672826478064081)
                ·
                  refine ⟨3057636261504619858548061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4076848348672826478064081 3057636261504619858548061)
                  ·
                    refine ⟨1146613598064232446955523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3057636261504619858548061 1146613598064232446955523)
                    ·
                      rfl

theorem cell22_3349533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_3349533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349533 prefixEnd_3349533 := by exact prefixLift 3349533
  have htrace : WordTrace (prefixWord ++ tailWord_3349533) baseStart_3349533 baseEnd_3349533 := by
    simpa [prefixWord, tailWord_3349533, baseEnd_3349533] using wordTrace_append hprefix tailTrace_3349533
  have hstable : (prefixWord ++ tailWord_3349533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349533).length < 2 ^ (prefixWord ++ tailWord_3349533).sum := by decide
  have hdescent : baseEnd_3349533 < baseStart_3349533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349632 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_3349632 : Nat := 118140960795 + 3349632 * 2 ^ 59
def prefixEnd_3349632 : Nat := 4983230072969 + 3 ^ 40 * 3349632 * 2
def baseEnd_3349632 : Nat := 1146647487787429188730219

theorem tailTrace_3349632 : CollatzResearch.WordTrace tailWord_3349632 prefixEnd_3349632 1146647487787429188730219 := by
  unfold tailWord_3349632
  simp only [CollatzResearch.WordTrace]
  refine ⟨61085557900431405222881575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81447410533908540297175433 61085557900431405222881575)
  ·
    refine ⟨91628336850647107834322363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61085557900431405222881575 91628336850647107834322363)
    ·
      refine ⟨137442505275970661751483545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91628336850647107834322363 137442505275970661751483545)
      ·
        refine ⟨103081878956977996313612659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137442505275970661751483545 103081878956977996313612659)
        ·
          refine ⟨154622818435466994470418989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103081878956977996313612659 154622818435466994470418989)
          ·
            refine ⟨57983556913300122926407121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154622818435466994470418989 57983556913300122926407121)
            ·
              refine ⟨43487667684975092194805341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57983556913300122926407121 43487667684975092194805341)
              ·
                refine ⟨16307875381865659573052003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43487667684975092194805341 16307875381865659573052003)
                ·
                  refine ⟨24461813072798489359578005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16307875381865659573052003 24461813072798489359578005)
                  ·
                    refine ⟨1146647487787429188730219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24461813072798489359578005 1146647487787429188730219)
                    ·
                      rfl

theorem cell22_3349632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_3349632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349632 prefixEnd_3349632 := by exact prefixLift 3349632
  have htrace : WordTrace (prefixWord ++ tailWord_3349632) baseStart_3349632 baseEnd_3349632 := by
    simpa [prefixWord, tailWord_3349632, baseEnd_3349632] using wordTrace_append hprefix tailTrace_3349632
  have hstable : (prefixWord ++ tailWord_3349632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349632).length < 2 ^ (prefixWord ++ tailWord_3349632).sum := by decide
  have hdescent : baseEnd_3349632 < baseStart_3349632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349679 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 5, 3]
def baseStart_3349679 : Nat := 118140960795 + 3349679 * 2 ^ 59
def prefixEnd_3349679 : Nat := 4983230072969 + 3 ^ 40 * 3349679 * 2
def baseEnd_3349679 : Nat := 1146663576847936732805075

theorem tailTrace_3349679 : CollatzResearch.WordTrace tailWord_3349679 prefixEnd_3349679 1146663576847936732805075 := by
  unfold tailWord_3349679
  simp only [CollatzResearch.WordTrace]
  refine ⟨122172830031692537472724091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81448553354461691648482727 122172830031692537472724091)
  ·
    refine ⟨183259245047538806209086137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122172830031692537472724091 183259245047538806209086137)
    ·
      refine ⟨137444433785654104656814603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183259245047538806209086137 137444433785654104656814603)
      ·
        refine ⟨206166650678481156985221905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137444433785654104656814603 206166650678481156985221905)
        ·
          refine ⟨154624988008860867738916429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206166650678481156985221905 154624988008860867738916429)
          ·
            refine ⟨57984370503322825402093661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154624988008860867738916429 57984370503322825402093661)
            ·
              refine ⟨21744138938746059525785123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57984370503322825402093661 21744138938746059525785123)
              ·
                refine ⟨32616208408119089288677685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21744138938746059525785123 32616208408119089288677685)
                ·
                  refine ⟨3057769538261164620813533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32616208408119089288677685 3057769538261164620813533)
                  ·
                    refine ⟨1146663576847936732805075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3057769538261164620813533 1146663576847936732805075)
                    ·
                      rfl

theorem cell22_3349679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 3].length) (baseStart_3349679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349679 prefixEnd_3349679 := by exact prefixLift 3349679
  have htrace : WordTrace (prefixWord ++ tailWord_3349679) baseStart_3349679 baseEnd_3349679 := by
    simpa [prefixWord, tailWord_3349679, baseEnd_3349679] using wordTrace_append hprefix tailTrace_3349679
  have hstable : (prefixWord ++ tailWord_3349679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349679).length < 2 ^ (prefixWord ++ tailWord_3349679).sum := by decide
  have hdescent : baseEnd_3349679 < baseStart_3349679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349681 : List Nat := [1, 2, 2, 5, 1, 2, 3, 6]
def baseStart_3349681 : Nat := 118140960795 + 3349681 * 2 ^ 59
def prefixEnd_3349681 : Nat := 4983230072969 + 3 ^ 40 * 3349681 * 2
def baseEnd_3349681 : Nat := 127407140165423266028341

theorem tailTrace_3349681 : CollatzResearch.WordTrace tailWord_3349681 prefixEnd_3349681 127407140165423266028341 := by
  unfold tailWord_3349681
  simp only [CollatzResearch.WordTrace]
  refine ⟨122172902977685291814296897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81448601985123527876197931 122172902977685291814296897)
  ·
    refine ⟨91629677233263968860722673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122172902977685291814296897 91629677233263968860722673)
    ·
      refine ⟨68722257924947976645542005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91629677233263968860722673 68722257924947976645542005)
      ·
        refine ⟨6442711680463872810519563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68722257924947976645542005 6442711680463872810519563)
        ·
          refine ⟨9664067520695809215779345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6442711680463872810519563 9664067520695809215779345)
          ·
            refine ⟨7248050640521856911834509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9664067520695809215779345 7248050640521856911834509)
            ·
              refine ⟨2718018990195696341937941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7248050640521856911834509 2718018990195696341937941)
              ·
                refine ⟨127407140165423266028341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2718018990195696341937941 127407140165423266028341)
                ·
                  rfl

theorem cell22_3349681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 6].length) (baseStart_3349681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349681 prefixEnd_3349681 := by exact prefixLift 3349681
  have htrace : WordTrace (prefixWord ++ tailWord_3349681) baseStart_3349681 baseEnd_3349681 := by
    simpa [prefixWord, tailWord_3349681, baseEnd_3349681] using wordTrace_append hprefix tailTrace_3349681
  have hstable : (prefixWord ++ tailWord_3349681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349681).length < 2 ^ (prefixWord ++ tailWord_3349681).sum := by decide
  have hdescent : baseEnd_3349681 < baseStart_3349681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349698 : List Nat := [3, 5, 1, 1, 2, 1, 9]
def baseStart_3349698 : Nat := 118140960795 + 3349698 * 2 ^ 59
def prefixEnd_3349698 : Nat := 4983230072969 + 3 ^ 40 * 3349698 * 2
def baseEnd_3349698 : Nat := 42469262256897296910371

theorem tailTrace_3349698 : CollatzResearch.WordTrace tailWord_3349698 prefixEnd_3349698 42469262256897296910371 := by
  unfold tailWord_3349698
  simp only [CollatzResearch.WordTrace]
  refine ⟨30543380754655925929416437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81449015345749135811777165 30543380754655925929416437)
  ·
    refine ⟨2863441945748993055882791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30543380754655925929416437 2863441945748993055882791)
    ·
      refine ⟨4295162918623489583824187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2863441945748993055882791 4295162918623489583824187)
      ·
        refine ⟨6442744377935234375736281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4295162918623489583824187 6442744377935234375736281)
        ·
          refine ⟨4832058283451425781802211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6442744377935234375736281 4832058283451425781802211)
          ·
            refine ⟨7248087425177138672703317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4832058283451425781802211 7248087425177138672703317)
            ·
              refine ⟨42469262256897296910371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7248087425177138672703317 42469262256897296910371)
              ·
                rfl

theorem cell22_3349698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 9].length) (baseStart_3349698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349698 prefixEnd_3349698 := by exact prefixLift 3349698
  have htrace : WordTrace (prefixWord ++ tailWord_3349698) baseStart_3349698 baseEnd_3349698 := by
    simpa [prefixWord, tailWord_3349698, baseEnd_3349698] using wordTrace_append hprefix tailTrace_3349698
  have hstable : (prefixWord ++ tailWord_3349698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349698).length < 2 ^ (prefixWord ++ tailWord_3349698).sum := by decide
  have hdescent : baseEnd_3349698 < baseStart_3349698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349702 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3349702 : Nat := 118140960795 + 3349702 * 2 ^ 59
def prefixEnd_3349702 : Nat := 4983230072969 + 3 ^ 40 * 3349702 * 2
def baseEnd_3349702 : Nat := 1146671450217972339480005

theorem tailTrace_3349702 : CollatzResearch.WordTrace tailWord_3349702 prefixEnd_3349702 1146671450217972339480005 := by
  unfold tailWord_3349702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3817927153456537887525355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81449112607072808267207573 3817927153456537887525355)
  ·
    refine ⟨5726890730184806831288033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3817927153456537887525355 5726890730184806831288033)
    ·
      refine ⟨4295168047638605123466025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5726890730184806831288033 4295168047638605123466025)
      ·
        refine ⟨3221376035728953842599519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4295168047638605123466025 3221376035728953842599519)
        ·
          refine ⟨4832064053593430763899279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3221376035728953842599519 4832064053593430763899279)
          ·
            refine ⟨7248096080390146145848919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4832064053593430763899279 7248096080390146145848919)
            ·
              refine ⟨10872144120585219218773379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7248096080390146145848919 10872144120585219218773379)
              ·
                refine ⟨16308216180877828828160069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10872144120585219218773379 16308216180877828828160069)
                ·
                  refine ⟨3057790533914592905280013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16308216180877828828160069 3057790533914592905280013)
                  ·
                    refine ⟨1146671450217972339480005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3057790533914592905280013 1146671450217972339480005)
                    ·
                      rfl

theorem cell22_3349702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3349702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349702 prefixEnd_3349702 := by exact prefixLift 3349702
  have htrace : WordTrace (prefixWord ++ tailWord_3349702) baseStart_3349702 baseEnd_3349702 := by
    simpa [prefixWord, tailWord_3349702, baseEnd_3349702] using wordTrace_append hprefix tailTrace_3349702
  have hstable : (prefixWord ++ tailWord_3349702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349702).length < 2 ^ (prefixWord ++ tailWord_3349702).sum := by decide
  have hdescent : baseEnd_3349702 < baseStart_3349702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349771 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 6]
def baseStart_3349771 : Nat := 118140960795 + 3349771 * 2 ^ 59
def prefixEnd_3349771 : Nat := 4983230072969 + 3 ^ 40 * 3349771 * 2
def baseEnd_3349771 : Nat := 382231690109359719834931

theorem tailTrace_3349771 : CollatzResearch.WordTrace tailWord_3349771 prefixEnd_3349771 382231690109359719834931 := by
  unfold tailWord_3349771
  simp only [CollatzResearch.WordTrace]
  refine ⟨122176185547359237185073167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81450790364906158123382111 122176185547359237185073167)
  ·
    refine ⟨183264278321038855777609751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122176185547359237185073167 183264278321038855777609751)
    ·
      refine ⟨274896417481558283666414627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183264278321038855777609751 274896417481558283666414627)
      ·
        refine ⟨412344626222337425499621941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274896417481558283666414627 412344626222337425499621941)
        ·
          refine ⟨38657308708344133640589557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 412344626222337425499621941 38657308708344133640589557)
          ·
            refine ⟨3624122691407262528805271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38657308708344133640589557 3624122691407262528805271)
            ·
              refine ⟨5436184037110893793207907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624122691407262528805271 5436184037110893793207907)
              ·
                refine ⟨8154276055666340689811861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5436184037110893793207907 8154276055666340689811861)
                ·
                  refine ⟨382231690109359719834931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8154276055666340689811861 382231690109359719834931)
                  ·
                    rfl

theorem cell22_3349771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 6].length) (baseStart_3349771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349771 prefixEnd_3349771 := by exact prefixLift 3349771
  have htrace : WordTrace (prefixWord ++ tailWord_3349771) baseStart_3349771 baseEnd_3349771 := by
    simpa [prefixWord, tailWord_3349771, baseEnd_3349771] using wordTrace_append hprefix tailTrace_3349771
  have hstable : (prefixWord ++ tailWord_3349771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349771).length < 2 ^ (prefixWord ++ tailWord_3349771).sum := by decide
  have hdescent : baseEnd_3349771 < baseStart_3349771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349790 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3349790 : Nat := 118140960795 + 3349790 * 2 ^ 59
def prefixEnd_3349790 : Nat := 4983230072969 + 3 ^ 40 * 3349790 * 2
def baseEnd_3349790 : Nat := 1146701574416369443279735

theorem tailTrace_3349790 : CollatzResearch.WordTrace tailWord_3349790 prefixEnd_3349790 1146701574416369443279735 := by
  unfold tailWord_3349790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15272109816786300428751853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81451252356193602286676549 15272109816786300428751853)
  ·
    refine ⟨5727041181294862660781945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15272109816786300428751853 5727041181294862660781945)
    ·
      refine ⟨4295280885971146995586459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5727041181294862660781945 4295280885971146995586459)
      ·
        refine ⟨6442921328956720493379689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4295280885971146995586459 6442921328956720493379689)
        ·
          refine ⟨4832190996717540370034767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6442921328956720493379689 4832190996717540370034767)
          ·
            refine ⟨7248286495076310555052151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4832190996717540370034767 7248286495076310555052151)
            ·
              refine ⟨10872429742614465832578227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7248286495076310555052151 10872429742614465832578227)
              ·
                refine ⟨16308644613921698748867341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10872429742614465832578227 16308644613921698748867341)
                ·
                  refine ⟨6115741730220637030825253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16308644613921698748867341 6115741730220637030825253)
                  ·
                    refine ⟨1146701574416369443279735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6115741730220637030825253 1146701574416369443279735)
                    ·
                      rfl

theorem cell22_3349790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3349790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349790 prefixEnd_3349790 := by exact prefixLift 3349790
  have htrace : WordTrace (prefixWord ++ tailWord_3349790) baseStart_3349790 baseEnd_3349790 := by
    simpa [prefixWord, tailWord_3349790, baseEnd_3349790] using wordTrace_append hprefix tailTrace_3349790
  have hstable : (prefixWord ++ tailWord_3349790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349790).length < 2 ^ (prefixWord ++ tailWord_3349790).sum := by decide
  have hdescent : baseEnd_3349790 < baseStart_3349790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349916 : List Nat := [2, 2, 3, 4, 2, 1, 1, 3, 1, 3]
def baseStart_3349916 : Nat := 118140960795 + 3349916 * 2 ^ 59
def prefixEnd_3349916 : Nat := 4983230072969 + 3 ^ 40 * 3349916 * 2
def baseEnd_3349916 : Nat := 1146744706791347114629349

theorem tailTrace_3349916 : CollatzResearch.WordTrace tailWord_3349916 prefixEnd_3349916 1146744706791347114629349 := by
  unfold tailWord_3349916
  simp only [CollatzResearch.WordTrace]
  refine ⟨61090737065916963474550801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81454316087889284632734401 61090737065916963474550801)
  ·
    refine ⟨45818052799437722605913101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61090737065916963474550801 45818052799437722605913101)
    ·
      refine ⟨17181769799789145977217413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45818052799437722605913101 17181769799789145977217413)
      ·
        refine ⟨3221581837460464870728265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17181769799789145977217413 3221581837460464870728265)
        ·
          refine ⟨2416186378095348653046199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3221581837460464870728265 2416186378095348653046199)
          ·
            refine ⟨3624279567143022979569299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416186378095348653046199 3624279567143022979569299)
            ·
              refine ⟨5436419350714534469353949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624279567143022979569299 5436419350714534469353949)
              ·
                refine ⟨2038657256517950426007731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5436419350714534469353949 2038657256517950426007731)
                ·
                  refine ⟨3057985884776925639011597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038657256517950426007731 3057985884776925639011597)
                  ·
                    refine ⟨1146744706791347114629349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3057985884776925639011597 1146744706791347114629349)
                    ·
                      rfl

theorem cell22_3349916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_3349916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349916 prefixEnd_3349916 := by exact prefixLift 3349916
  have htrace : WordTrace (prefixWord ++ tailWord_3349916) baseStart_3349916 baseEnd_3349916 := by
    simpa [prefixWord, tailWord_3349916, baseEnd_3349916] using wordTrace_append hprefix tailTrace_3349916
  have hstable : (prefixWord ++ tailWord_3349916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349916).length < 2 ^ (prefixWord ++ tailWord_3349916).sum := by decide
  have hdescent : baseEnd_3349916 < baseStart_3349916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349955 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 2, 3]
def baseStart_3349955 : Nat := 118140960795 + 3349955 * 2 ^ 59
def prefixEnd_3349955 : Nat := 4983230072969 + 3 ^ 40 * 3349955 * 2
def baseEnd_3349955 : Nat := 1146758057288364012904229

theorem tailTrace_3349955 : CollatzResearch.WordTrace tailWord_3349955 prefixEnd_3349955 1146758057288364012904229 := by
  unfold tailWord_3349955
  simp only [CollatzResearch.WordTrace]
  refine ⟨122182896578692636609771319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81455264385795091073180879 122182896578692636609771319)
  ·
    refine ⟨183274344868038954914656979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122182896578692636609771319 183274344868038954914656979)
    ·
      refine ⟨274911517302058432371985469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183274344868038954914656979 274911517302058432371985469)
      ·
        refine ⟨103091818988271912139494551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274911517302058432371985469 103091818988271912139494551)
        ·
          refine ⟨154637728482407868209241827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103091818988271912139494551 154637728482407868209241827)
          ·
            refine ⟨231956592723611802313862741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154637728482407868209241827 231956592723611802313862741)
            ·
              refine ⟨2718241320979825808365579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 231956592723611802313862741 2718241320979825808365579)
              ·
                refine ⟨4077361981469738712548369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2718241320979825808365579 4077361981469738712548369)
                ·
                  refine ⟨3058021486102304034411277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4077361981469738712548369 3058021486102304034411277)
                  ·
                    refine ⟨1146758057288364012904229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3058021486102304034411277 1146758057288364012904229)
                    ·
                      rfl

theorem cell22_3349955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 2, 3].length) (baseStart_3349955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349955 prefixEnd_3349955 := by exact prefixLift 3349955
  have htrace : WordTrace (prefixWord ++ tailWord_3349955) baseStart_3349955 baseEnd_3349955 := by
    simpa [prefixWord, tailWord_3349955, baseEnd_3349955] using wordTrace_append hprefix tailTrace_3349955
  have hstable : (prefixWord ++ tailWord_3349955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349955).length < 2 ^ (prefixWord ++ tailWord_3349955).sum := by decide
  have hdescent : baseEnd_3349955 < baseStart_3349955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349966 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3349966 : Nat := 118140960795 + 3349966 * 2 ^ 59
def prefixEnd_3349966 : Nat := 4983230072969 + 3 ^ 40 * 3349966 * 2
def baseEnd_3349966 : Nat := 1146761822813163650879195

theorem tailTrace_3349966 : CollatzResearch.WordTrace tailWord_3349966 prefixEnd_3349966 1146761822813163650879195 := by
  unfold tailWord_3349966
  simp only [CollatzResearch.WordTrace]
  refine ⟨15272912222706598186052719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81455531854435190325614501 15272912222706598186052719)
  ·
    refine ⟨22909368334059897279079079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15272912222706598186052719 22909368334059897279079079)
    ·
      refine ⟨34364052501089845918618619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22909368334059897279079079 34364052501089845918618619)
      ·
        refine ⟨51546078751634768877927929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34364052501089845918618619 51546078751634768877927929)
        ·
          refine ⟨38659559063726076658445947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51546078751634768877927929 38659559063726076658445947)
          ·
            refine ⟨57989338595589114987668921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38659559063726076658445947 57989338595589114987668921)
            ·
              refine ⟨43492003946691836240751691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57989338595589114987668921 43492003946691836240751691)
              ·
                refine ⟨65238005920037754361127537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43492003946691836240751691 65238005920037754361127537)
                ·
                  refine ⟨48928504440028315770845653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65238005920037754361127537 48928504440028315770845653)
                  ·
                    refine ⟨1146761822813163650879195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48928504440028315770845653 1146761822813163650879195)
                    ·
                      rfl

theorem cell22_3349966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3349966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3349966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3349966 prefixEnd_3349966 := by exact prefixLift 3349966
  have htrace : WordTrace (prefixWord ++ tailWord_3349966) baseStart_3349966 baseEnd_3349966 := by
    simpa [prefixWord, tailWord_3349966, baseEnd_3349966] using wordTrace_append hprefix tailTrace_3349966
  have hstable : (prefixWord ++ tailWord_3349966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349966).length < 2 ^ (prefixWord ++ tailWord_3349966).sum := by decide
  have hdescent : baseEnd_3349966 < baseStart_3349966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350011 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 2, 5]
def baseStart_3350011 : Nat := 118140960795 + 3350011 * 2 ^ 59
def prefixEnd_3350011 : Nat := 4983230072969 + 3 ^ 40 * 3350011 * 2
def baseEnd_3350011 : Nat := 1146777227232798533504057

theorem tailTrace_3350011 : CollatzResearch.WordTrace tailWord_3350011 prefixEnd_3350011 1146777227232798533504057 := by
  unfold tailWord_3350011
  simp only [CollatzResearch.WordTrace]
  refine ⟨122184939066489758173809887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81456626044326505449206591 122184939066489758173809887)
  ·
    refine ⟨183277408599734637260714831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122184939066489758173809887 183277408599734637260714831)
    ·
      refine ⟨274916112899601955891072247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183277408599734637260714831 274916112899601955891072247)
      ·
        refine ⟨412374169349402933836608371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274916112899601955891072247 412374169349402933836608371)
        ·
          refine ⟨618561254024104400754912557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412374169349402933836608371 618561254024104400754912557)
          ·
            refine ⟨231960470259039150283092209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 618561254024104400754912557 231960470259039150283092209)
            ·
              refine ⟨173970352694279362712319157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231960470259039150283092209 173970352694279362712319157)
              ·
                refine ⟨16309720565088690254279921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173970352694279362712319157 16309720565088690254279921)
                ·
                  refine ⟨12232290423816517690709941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16309720565088690254279921 12232290423816517690709941)
                  ·
                    refine ⟨1146777227232798533504057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12232290423816517690709941 1146777227232798533504057)
                    ·
                      rfl

theorem cell22_3350011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_3350011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350011 prefixEnd_3350011 := by exact prefixLift 3350011
  have htrace : WordTrace (prefixWord ++ tailWord_3350011) baseStart_3350011 baseEnd_3350011 := by
    simpa [prefixWord, tailWord_3350011, baseEnd_3350011] using wordTrace_append hprefix tailTrace_3350011
  have hstable : (prefixWord ++ tailWord_3350011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350011).length < 2 ^ (prefixWord ++ tailWord_3350011).sum := by decide
  have hdescent : baseEnd_3350011 < baseStart_3350011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350013 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 5]
def baseStart_3350013 : Nat := 118140960795 + 3350013 * 2 ^ 59
def prefixEnd_3350013 : Nat := 4983230072969 + 3 ^ 40 * 3350013 * 2
def baseEnd_3350013 : Nat := 382259303957890398318017

theorem tailTrace_3350013 : CollatzResearch.WordTrace tailWord_3350013 prefixEnd_3350013 382259303957890398318017 := by
  unfold tailWord_3350013
  simp only [CollatzResearch.WordTrace]
  refine ⟨122185012012482512515382693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81456674674988341676921795 122185012012482512515382693)
  ·
    refine ⟨22909689752340471096634255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122185012012482512515382693 22909689752340471096634255)
    ·
      refine ⟨34364534628510706644951383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22909689752340471096634255 34364534628510706644951383)
      ·
        refine ⟨51546801942766059967427075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34364534628510706644951383 51546801942766059967427075)
        ·
          refine ⟨77320202914149089951140613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51546801942766059967427075 77320202914149089951140613)
          ·
            refine ⟨14497538046402954365838865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77320202914149089951140613 14497538046402954365838865)
            ·
              refine ⟨10873153534802215774379149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14497538046402954365838865 10873153534802215774379149)
              ·
                refine ⟨4077432575550830915392181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10873153534802215774379149 4077432575550830915392181)
                ·
                  refine ⟨382259303957890398318017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4077432575550830915392181 382259303957890398318017)
                  ·
                    rfl

theorem cell22_3350013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_3350013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350013 prefixEnd_3350013 := by exact prefixLift 3350013
  have htrace : WordTrace (prefixWord ++ tailWord_3350013) baseStart_3350013 baseEnd_3350013 := by
    simpa [prefixWord, tailWord_3350013, baseEnd_3350013] using wordTrace_append hprefix tailTrace_3350013
  have hstable : (prefixWord ++ tailWord_3350013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350013).length < 2 ^ (prefixWord ++ tailWord_3350013).sum := by decide
  have hdescent : baseEnd_3350013 < baseStart_3350013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350077 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_3350077 : Nat := 118140960795 + 3350077 * 2 ^ 59
def prefixEnd_3350077 : Nat := 4983230072969 + 3 ^ 40 * 3350077 * 2
def baseEnd_3350077 : Nat := 1146799820381596361353855

theorem tailTrace_3350077 : CollatzResearch.WordTrace tailWord_3350077 prefixEnd_3350077 1146799820381596361353855 := by
  unfold tailWord_3350077
  simp only [CollatzResearch.WordTrace]
  refine ⟨122187346284250651445712485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81458230856167100963808323 122187346284250651445712485)
  ·
    refine ⟨22910127428296997146071091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122187346284250651445712485 22910127428296997146071091)
    ·
      refine ⟨34365191142445495719106637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22910127428296997146071091 34365191142445495719106637)
      ·
        refine ⟨12886946678417060894664989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34365191142445495719106637 12886946678417060894664989)
        ·
          refine ⟨4832605004406397835499371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12886946678417060894664989 4832605004406397835499371)
          ·
            refine ⟨7248907506609596753249057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4832605004406397835499371 7248907506609596753249057)
            ·
              refine ⟨5436680629957197564936793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7248907506609596753249057 5436680629957197564936793)
              ·
                refine ⟨4077510472467898173702595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5436680629957197564936793 4077510472467898173702595)
                ·
                  refine ⟨6116265708701847260553893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4077510472467898173702595 6116265708701847260553893)
                  ·
                    refine ⟨1146799820381596361353855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6116265708701847260553893 1146799820381596361353855)
                    ·
                      rfl

theorem cell22_3350077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_3350077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350077 prefixEnd_3350077 := by exact prefixLift 3350077
  have htrace : WordTrace (prefixWord ++ tailWord_3350077) baseStart_3350077 baseEnd_3350077 := by
    simpa [prefixWord, tailWord_3350077, baseEnd_3350077] using wordTrace_append hprefix tailTrace_3350077
  have hstable : (prefixWord ++ tailWord_3350077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350077).length < 2 ^ (prefixWord ++ tailWord_3350077).sum := by decide
  have hdescent : baseEnd_3350077 < baseStart_3350077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350092 : List Nat := [2, 2, 1, 3, 1, 5, 1, 3, 4]
def baseStart_3350092 : Nat := 118140960795 + 3350092 * 2 ^ 59
def prefixEnd_3350092 : Nat := 4983230072969 + 3 ^ 40 * 3350092 * 2
def baseEnd_3350092 : Nat := 382268318396047107409603

theorem tailTrace_3350092 : CollatzResearch.WordTrace tailWord_3350092 prefixEnd_3350092 382268318396047107409603 := by
  unfold tailWord_3350092
  simp only [CollatzResearch.WordTrace]
  refine ⟨61093946689598154503754265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81458595586130872671672353 61093946689598154503754265)
  ·
    refine ⟨45820460017198615877815699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61093946689598154503754265 45820460017198615877815699)
    ·
      refine ⟨68730690025797923816723549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45820460017198615877815699 68730690025797923816723549)
      ·
        refine ⟨25774008759674221431271331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68730690025797923816723549 25774008759674221431271331)
        ·
          refine ⟨38661013139511332146906997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25774008759674221431271331 38661013139511332146906997)
          ·
            refine ⟨3624469981829187388772531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38661013139511332146906997 3624469981829187388772531)
            ·
              refine ⟨5436704972743781083158797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624469981829187388772531 5436704972743781083158797)
              ·
                refine ⟨2038764364778917906184549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5436704972743781083158797 2038764364778917906184549)
                ·
                  refine ⟨382268318396047107409603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2038764364778917906184549 382268318396047107409603)
                  ·
                    rfl

theorem cell22_3350092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_3350092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350092 prefixEnd_3350092 := by exact prefixLift 3350092
  have htrace : WordTrace (prefixWord ++ tailWord_3350092) baseStart_3350092 baseEnd_3350092 := by
    simpa [prefixWord, tailWord_3350092, baseEnd_3350092] using wordTrace_append hprefix tailTrace_3350092
  have hstable : (prefixWord ++ tailWord_3350092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350092).length < 2 ^ (prefixWord ++ tailWord_3350092).sum := by decide
  have hdescent : baseEnd_3350092 < baseStart_3350092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350103 : List Nat := [1, 1, 3, 2, 2, 5, 8]
def baseStart_3350103 : Nat := 118140960795 + 3350103 * 2 ^ 59
def prefixEnd_3350103 : Nat := 4983230072969 + 3 ^ 40 * 3350103 * 2
def baseEnd_3350103 : Nat := 42474397063442257785325

theorem tailTrace_3350103 : CollatzResearch.WordTrace tailWord_3350103 prefixEnd_3350103 42474397063442257785325 := by
  unfold tailWord_3350103
  simp only [CollatzResearch.WordTrace]
  refine ⟨122188294582156457886158963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81458863054770971924105975 122188294582156457886158963)
  ·
    refine ⟨183282441873234686829238445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122188294582156457886158963 183282441873234686829238445)
    ·
      refine ⟨68730915702463007560964417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183282441873234686829238445 68730915702463007560964417)
      ·
        refine ⟨51548186776847255670723313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68730915702463007560964417 51548186776847255670723313)
        ·
          refine ⟨38661140082635441753042485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51548186776847255670723313 38661140082635441753042485)
          ·
            refine ⟨3624481882747072664347733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38661140082635441753042485 3624481882747072664347733)
            ·
              refine ⟨42474397063442257785325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3624481882747072664347733 42474397063442257785325)
              ·
                rfl

theorem cell22_3350103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 8].length) (baseStart_3350103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350103 prefixEnd_3350103 := by exact prefixLift 3350103
  have htrace : WordTrace (prefixWord ++ tailWord_3350103) baseStart_3350103 baseEnd_3350103 := by
    simpa [prefixWord, tailWord_3350103, baseEnd_3350103] using wordTrace_append hprefix tailTrace_3350103
  have hstable : (prefixWord ++ tailWord_3350103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350103).length < 2 ^ (prefixWord ++ tailWord_3350103).sum := by decide
  have hdescent : baseEnd_3350103 < baseStart_3350103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350109 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 6]
def baseStart_3350109 : Nat := 118140960795 + 3350109 * 2 ^ 59
def prefixEnd_3350109 : Nat := 4983230072969 + 3 ^ 40 * 3350109 * 2
def baseEnd_3350109 : Nat := 382270258211852981517919

theorem tailTrace_3350109 : CollatzResearch.WordTrace tailWord_3350109 prefixEnd_3350109 382270258211852981517919 := by
  unfold tailWord_3350109
  simp only [CollatzResearch.WordTrace]
  refine ⟨122188513420134720910877381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81459008946756480607251587 122188513420134720910877381)
  ·
    refine ⟨22910346266275260170789509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122188513420134720910877381 22910346266275260170789509)
    ·
      refine ⟨4295689924926611282023033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22910346266275260170789509 4295689924926611282023033)
      ·
        refine ⟨3221767443694958461517275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4295689924926611282023033 3221767443694958461517275)
        ·
          refine ⟨4832651165542437692275913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3221767443694958461517275 4832651165542437692275913)
          ·
            refine ⟨3624488374156828269206935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4832651165542437692275913 3624488374156828269206935)
            ·
              refine ⟨5436732561235242403810403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624488374156828269206935 5436732561235242403810403)
              ·
                refine ⟨8155098841852863605715605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5436732561235242403810403 8155098841852863605715605)
                ·
                  refine ⟨382270258211852981517919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8155098841852863605715605 382270258211852981517919)
                  ·
                    rfl

theorem cell22_3350109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_3350109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350109 prefixEnd_3350109 := by exact prefixLift 3350109
  have htrace : WordTrace (prefixWord ++ tailWord_3350109) baseStart_3350109 baseEnd_3350109 := by
    simpa [prefixWord, tailWord_3350109, baseEnd_3350109] using wordTrace_append hprefix tailTrace_3350109
  have hstable : (prefixWord ++ tailWord_3350109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350109).length < 2 ^ (prefixWord ++ tailWord_3350109).sum := by decide
  have hdescent : baseEnd_3350109 < baseStart_3350109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350120 : List Nat := [2, 1, 4, 3, 1, 2, 2, 7]
def baseStart_3350120 : Nat := 118140960795 + 3350120 * 2 ^ 59
def prefixEnd_3350120 : Nat := 4983230072969 + 3 ^ 40 * 3350120 * 2
def baseEnd_3350120 : Nat := 127423837795595398058747

theorem tailTrace_3350120 : CollatzResearch.WordTrace tailWord_3350120 prefixEnd_3350120 127423837795595398058747 := by
  unfold tailWord_3350120
  simp only [CollatzResearch.WordTrace]
  refine ⟨61094457311547434894763907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81459276415396579859685209 61094457311547434894763907)
  ·
    refine ⟨91641685967321152342145861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61094457311547434894763907 91641685967321152342145861)
    ·
      refine ⟨17182816118872716064152349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91641685967321152342145861 17182816118872716064152349)
      ·
        refine ⟨6443556044577268524057131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17182816118872716064152349 6443556044577268524057131)
        ·
          refine ⟨9665334066865902786085697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6443556044577268524057131 9665334066865902786085697)
          ·
            refine ⟨7249000550149427089564273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9665334066865902786085697 7249000550149427089564273)
            ·
              refine ⟨5436750412612070317173205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7249000550149427089564273 5436750412612070317173205)
              ·
                refine ⟨127423837795595398058747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5436750412612070317173205 127423837795595398058747)
                ·
                  rfl

theorem cell22_3350120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 7].length) (baseStart_3350120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350120 prefixEnd_3350120 := by exact prefixLift 3350120
  have htrace : WordTrace (prefixWord ++ tailWord_3350120) baseStart_3350120 baseEnd_3350120 := by
    simpa [prefixWord, tailWord_3350120, baseEnd_3350120] using wordTrace_append hprefix tailTrace_3350120
  have hstable : (prefixWord ++ tailWord_3350120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350120).length < 2 ^ (prefixWord ++ tailWord_3350120).sum := by decide
  have hdescent : baseEnd_3350120 < baseStart_3350120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350180 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_3350180 : Nat := 118140960795 + 3350180 * 2 ^ 59
def prefixEnd_3350180 : Nat := 4983230072969 + 3 ^ 40 * 3350180 * 2
def baseEnd_3350180 : Nat := 1146835079386538426028539

theorem tailTrace_3350180 : CollatzResearch.WordTrace tailWord_3350180 prefixEnd_3350180 1146835079386538426028539 := by
  unfold tailWord_3350180
  simp only [CollatzResearch.WordTrace]
  refine ⟨61095551501438750018355997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81460735335251666691141329 61095551501438750018355997)
  ·
    refine ⟨22910831813039531256883499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61095551501438750018355997 22910831813039531256883499)
    ·
      refine ⟨34366247719559296885325249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22910831813039531256883499 34366247719559296885325249)
      ·
        refine ⟨25774685789669472663993937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34366247719559296885325249 25774685789669472663993937)
        ·
          refine ⟨19331014342252104497995453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25774685789669472663993937 19331014342252104497995453)
          ·
            refine ⟨7249130378344539186748295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19331014342252104497995453 7249130378344539186748295)
            ·
              refine ⟨10873695567516808780122443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7249130378344539186748295 10873695567516808780122443)
              ·
                refine ⟨16310543351275213170183665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10873695567516808780122443 16310543351275213170183665)
                ·
                  refine ⟨12232907513456409877637749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16310543351275213170183665 12232907513456409877637749)
                  ·
                    refine ⟨1146835079386538426028539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12232907513456409877637749 1146835079386538426028539)
                    ·
                      rfl

theorem cell22_3350180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_3350180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350180 prefixEnd_3350180 := by exact prefixLift 3350180
  have htrace : WordTrace (prefixWord ++ tailWord_3350180) baseStart_3350180 baseEnd_3350180 := by
    simpa [prefixWord, tailWord_3350180, baseEnd_3350180] using wordTrace_append hprefix tailTrace_3350180
  have hstable : (prefixWord ++ tailWord_3350180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350180).length < 2 ^ (prefixWord ++ tailWord_3350180).sum := by decide
  have hdescent : baseEnd_3350180 < baseStart_3350180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350195 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 1, 4]
def baseStart_3350195 : Nat := 118140960795 + 3350195 * 2 ^ 59
def prefixEnd_3350195 : Nat := 4983230072969 + 3 ^ 40 * 3350195 * 2
def baseEnd_3350195 : Nat := 1146840214193083386903493

theorem tailTrace_3350195 : CollatzResearch.WordTrace tailWord_3350195 prefixEnd_3350195 1146840214193083386903493 := by
  unfold tailWord_3350195
  simp only [CollatzResearch.WordTrace]
  refine ⟨122191650097823157598508039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81461100065215438399005359 122191650097823157598508039)
  ·
    refine ⟨183287475146734736397762059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122191650097823157598508039 183287475146734736397762059)
    ·
      refine ⟨274931212720102104596643089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183287475146734736397762059 274931212720102104596643089)
      ·
        refine ⟨206198409540076578447482317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274931212720102104596643089 206198409540076578447482317)
        ·
          refine ⟨77324403577528716917805869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206198409540076578447482317 77324403577528716917805869)
          ·
            refine ⟨28996651341573268844177201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77324403577528716917805869 28996651341573268844177201)
            ·
              refine ⟨21747488506179951633132901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28996651341573268844177201 21747488506179951633132901)
              ·
                refine ⟨4077654094908740931212419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21747488506179951633132901 4077654094908740931212419)
                ·
                  refine ⟨6116481142363111396818629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4077654094908740931212419 6116481142363111396818629)
                  ·
                    refine ⟨1146840214193083386903493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6116481142363111396818629 1146840214193083386903493)
                    ·
                      rfl

theorem cell22_3350195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 4].length) (baseStart_3350195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350195 prefixEnd_3350195 := by exact prefixLift 3350195
  have htrace : WordTrace (prefixWord ++ tailWord_3350195) baseStart_3350195 baseEnd_3350195 := by
    simpa [prefixWord, tailWord_3350195, baseEnd_3350195] using wordTrace_append hprefix tailTrace_3350195
  have hstable : (prefixWord ++ tailWord_3350195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350195).length < 2 ^ (prefixWord ++ tailWord_3350195).sum := by decide
  have hdescent : baseEnd_3350195 < baseStart_3350195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350212 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3350212 : Nat := 118140960795 + 3350212 * 2 ^ 59
def prefixEnd_3350212 : Nat := 4983230072969 + 3 ^ 40 * 3350212 * 2
def baseEnd_3350212 : Nat := 1146846033640501009228441

theorem tailTrace_3350212 : CollatzResearch.WordTrace tailWord_3350212 prefixEnd_3350212 1146846033640501009228441 := by
  unfold tailWord_3350212
  simp only [CollatzResearch.WordTrace]
  refine ⟨61096135069380784750938445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81461513425841046334584593 61096135069380784750938445)
  ·
    refine ⟨22911050651017794281601917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61096135069380784750938445 22911050651017794281601917)
    ·
      refine ⟨8591643994131672855600719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22911050651017794281601917 8591643994131672855600719)
      ·
        refine ⟨12887465991197509283401079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8591643994131672855600719 12887465991197509283401079)
        ·
          refine ⟨19331198986796263925101619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12887465991197509283401079 19331198986796263925101619)
          ·
            refine ⟨28996798480194395887652429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19331198986796263925101619 28996798480194395887652429)
            ·
              refine ⟨10873799430072898457869661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28996798480194395887652429 10873799430072898457869661)
              ·
                refine ⟨4077674786277336921701123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10873799430072898457869661 4077674786277336921701123)
                ·
                  refine ⟨6116512179416005382551685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4077674786277336921701123 6116512179416005382551685)
                  ·
                    refine ⟨1146846033640501009228441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6116512179416005382551685 1146846033640501009228441)
                    ·
                      rfl

theorem cell22_3350212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3350212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350212 prefixEnd_3350212 := by exact prefixLift 3350212
  have htrace : WordTrace (prefixWord ++ tailWord_3350212) baseStart_3350212 baseEnd_3350212 := by
    simpa [prefixWord, tailWord_3350212, baseEnd_3350212] using wordTrace_append hprefix tailTrace_3350212
  have hstable : (prefixWord ++ tailWord_3350212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350212).length < 2 ^ (prefixWord ++ tailWord_3350212).sum := by decide
  have hdescent : baseEnd_3350212 < baseStart_3350212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350214 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3350214 : Nat := 118140960795 + 3350214 * 2 ^ 59
def prefixEnd_3350214 : Nat := 4983230072969 + 3 ^ 40 * 3350214 * 2
def baseEnd_3350214 : Nat := 1146846718281373670678435

theorem tailTrace_3350214 : CollatzResearch.WordTrace tailWord_3350214 prefixEnd_3350214 1146846718281373670678435 := by
  unfold tailWord_3350214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818510721398572620107803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81461562056502882562299797 3818510721398572620107803)
  ·
    refine ⟨5727766082097858930161705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3818510721398572620107803 5727766082097858930161705)
    ·
      refine ⟨4295824561573394197621279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5727766082097858930161705 4295824561573394197621279)
      ·
        refine ⟨6443736842360091296431919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4295824561573394197621279 6443736842360091296431919)
        ·
          refine ⟨9665605263540136944647879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6443736842360091296431919 9665605263540136944647879)
          ·
            refine ⟨14498407895310205416971819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9665605263540136944647879 14498407895310205416971819)
            ·
              refine ⟨21747611842965308125457729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14498407895310205416971819 21747611842965308125457729)
              ·
                refine ⟨16310708882223981094093297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21747611842965308125457729 16310708882223981094093297)
                ·
                  refine ⟨12233031661667985820569973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16310708882223981094093297 12233031661667985820569973)
                  ·
                    refine ⟨1146846718281373670678435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12233031661667985820569973 1146846718281373670678435)
                    ·
                      rfl

theorem cell22_3350214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3350214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350214 prefixEnd_3350214 := by exact prefixLift 3350214
  have htrace : WordTrace (prefixWord ++ tailWord_3350214) baseStart_3350214 baseEnd_3350214 := by
    simpa [prefixWord, tailWord_3350214, baseEnd_3350214] using wordTrace_append hprefix tailTrace_3350214
  have hstable : (prefixWord ++ tailWord_3350214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350214).length < 2 ^ (prefixWord ++ tailWord_3350214).sum := by decide
  have hdescent : baseEnd_3350214 < baseStart_3350214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350334 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_3350334 : Nat := 118140960795 + 3350334 * 2 ^ 59
def prefixEnd_3350334 : Nat := 4983230072969 + 3 ^ 40 * 3350334 * 2
def baseEnd_3350334 : Nat := 382295932244577785892689

theorem tailTrace_3350334 : CollatzResearch.WordTrace tailWord_3350334 prefixEnd_3350334 382295932244577785892689 := by
  unfold tailWord_3350334
  simp only [CollatzResearch.WordTrace]
  refine ⟨15274589980539948042227257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81464479896213056225212037 15274589980539948042227257)
  ·
    refine ⟨11455942485404961031670443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15274589980539948042227257 11455942485404961031670443)
    ·
      refine ⟨17183913728107441547505665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11455942485404961031670443 17183913728107441547505665)
      ·
        refine ⟨12887935296080581160629249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17183913728107441547505665 12887935296080581160629249)
        ·
          refine ⟨9665951472060435870471937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12887935296080581160629249 9665951472060435870471937)
          ·
            refine ⟨7249463604045326902853953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9665951472060435870471937 7249463604045326902853953)
            ·
              refine ⟨5437097703033995177140465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7249463604045326902853953 5437097703033995177140465)
              ·
                refine ⟨4077823277275496382855349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5437097703033995177140465 4077823277275496382855349)
                ·
                  refine ⟨382295932244577785892689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4077823277275496382855349 382295932244577785892689)
                  ·
                    rfl

theorem cell22_3350334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_3350334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350334 prefixEnd_3350334 := by exact prefixLift 3350334
  have htrace : WordTrace (prefixWord ++ tailWord_3350334) baseStart_3350334 baseEnd_3350334 := by
    simpa [prefixWord, tailWord_3350334, baseEnd_3350334] using wordTrace_append hprefix tailTrace_3350334
  have hstable : (prefixWord ++ tailWord_3350334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350334).length < 2 ^ (prefixWord ++ tailWord_3350334).sum := by decide
  have hdescent : baseEnd_3350334 < baseStart_3350334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350345 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 6]
def baseStart_3350345 : Nat := 118140960795 + 3350345 * 2 ^ 59
def prefixEnd_3350345 : Nat := 4983230072969 + 3 ^ 40 * 3350345 * 2
def baseEnd_3350345 : Nat := 382297187419510998551011

theorem tailTrace_3350345 : CollatzResearch.WordTrace tailWord_3350345 prefixEnd_3350345 382297187419510998551011 := by
  unfold tailWord_3350345
  simp only [CollatzResearch.WordTrace]
  refine ⟨122197121047279733216468489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81464747364853155477645659 122197121047279733216468489)
  ·
    refine ⟨91647840785459799912351367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122197121047279733216468489 91647840785459799912351367)
    ·
      refine ⟨137471761178189699868527051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91647840785459799912351367 137471761178189699868527051)
      ·
        refine ⟨206207641767284549802790577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137471761178189699868527051 206207641767284549802790577)
        ·
          refine ⟨154655731325463412352092933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206207641767284549802790577 154655731325463412352092933)
          ·
            refine ⟨28997949623524389816017425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154655731325463412352092933 28997949623524389816017425)
            ·
              refine ⟨21748462217643292362013069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28997949623524389816017425 21748462217643292362013069)
              ·
                refine ⟨8155673331616234635754901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21748462217643292362013069 8155673331616234635754901)
                ·
                  refine ⟨382297187419510998551011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8155673331616234635754901 382297187419510998551011)
                  ·
                    rfl

theorem cell22_3350345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_3350345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350345 prefixEnd_3350345 := by exact prefixLift 3350345
  have htrace : WordTrace (prefixWord ++ tailWord_3350345) baseStart_3350345 baseEnd_3350345 := by
    simpa [prefixWord, tailWord_3350345, baseEnd_3350345] using wordTrace_append hprefix tailTrace_3350345
  have hstable : (prefixWord ++ tailWord_3350345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350345).length < 2 ^ (prefixWord ++ tailWord_3350345).sum := by decide
  have hdescent : baseEnd_3350345 < baseStart_3350345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350349 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3350349 : Nat := 118140960795 + 3350349 * 2 ^ 59
def prefixEnd_3350349 : Nat := 4983230072969 + 3 ^ 40 * 3350349 * 2
def baseEnd_3350349 : Nat := 1146892931540278318553021

theorem tailTrace_3350349 : CollatzResearch.WordTrace tailWord_3350349 prefixEnd_3350349 1146892931540278318553021 := by
  unfold tailWord_3350349
  simp only [CollatzResearch.WordTrace]
  refine ⟨122197266939265241899614101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81464844626176827933076067 122197266939265241899614101)
  ·
    refine ⟨5727996887778058214044411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122197266939265241899614101 5727996887778058214044411)
    ·
      refine ⟨8591995331667087321066617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727996887778058214044411 8591995331667087321066617)
      ·
        refine ⟨6443996498750315490799963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8591995331667087321066617 6443996498750315490799963)
        ·
          refine ⟨9665994748125473236199945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6443996498750315490799963 9665994748125473236199945)
          ·
            refine ⟨7249496061094104927149959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9665994748125473236199945 7249496061094104927149959)
            ·
              refine ⟨10874244091641157390724939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7249496061094104927149959 10874244091641157390724939)
              ·
                refine ⟨16311366137461736086087409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10874244091641157390724939 16311366137461736086087409)
                ·
                  refine ⟨12233524603096302064565557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16311366137461736086087409 12233524603096302064565557)
                  ·
                    refine ⟨1146892931540278318553021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12233524603096302064565557 1146892931540278318553021)
                    ·
                      rfl

theorem cell22_3350349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3350349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350349 prefixEnd_3350349 := by exact prefixLift 3350349
  have htrace : WordTrace (prefixWord ++ tailWord_3350349) baseStart_3350349 baseEnd_3350349 := by
    simpa [prefixWord, tailWord_3350349, baseEnd_3350349] using wordTrace_append hprefix tailTrace_3350349
  have hstable : (prefixWord ++ tailWord_3350349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350349).length < 2 ^ (prefixWord ++ tailWord_3350349).sum := by decide
  have hdescent : baseEnd_3350349 < baseStart_3350349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350394 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 2, 3]
def baseStart_3350394 : Nat := 118140960795 + 3350394 * 2 ^ 59
def prefixEnd_3350394 : Nat := 4983230072969 + 3 ^ 40 * 3350394 * 2
def baseEnd_3350394 : Nat := 1146908335959913201177883

theorem tailTrace_3350394 : CollatzResearch.WordTrace tailWord_3350394 prefixEnd_3350394 1146908335959913201177883 := by
  unfold tailWord_3350394
  simp only [CollatzResearch.WordTrace]
  refine ⟨30549727056025553646250559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81465938816068143056668157 30549727056025553646250559)
  ·
    refine ⟨45824590584038330469375839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30549727056025553646250559 45824590584038330469375839)
    ·
      refine ⟨68736885876057495704063759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45824590584038330469375839 68736885876057495704063759)
      ·
        refine ⟨103105328814086243556095639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68736885876057495704063759 103105328814086243556095639)
        ·
          refine ⟨154657993221129365334143459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103105328814086243556095639 154657993221129365334143459)
          ·
            refine ⟨231986989831694048001215189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154657993221129365334143459 231986989831694048001215189)
            ·
              refine ⟨5437195074180329250028481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 231986989831694048001215189 5437195074180329250028481)
              ·
                refine ⟨4077896305635246937521361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5437195074180329250028481 4077896305635246937521361)
                ·
                  refine ⟨3058422229226435203141021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4077896305635246937521361 3058422229226435203141021)
                  ·
                    refine ⟨1146908335959913201177883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3058422229226435203141021 1146908335959913201177883)
                    ·
                      rfl

theorem cell22_3350394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_3350394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350394 prefixEnd_3350394 := by exact prefixLift 3350394
  have htrace : WordTrace (prefixWord ++ tailWord_3350394) baseStart_3350394 baseEnd_3350394 := by
    simpa [prefixWord, tailWord_3350394, baseEnd_3350394] using wordTrace_append hprefix tailTrace_3350394
  have hstable : (prefixWord ++ tailWord_3350394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350394).length < 2 ^ (prefixWord ++ tailWord_3350394).sum := by decide
  have hdescent : baseEnd_3350394 < baseStart_3350394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350424 : List Nat := [2, 1, 2, 6, 1, 1, 1, 8]
def baseStart_3350424 : Nat := 118140960795 + 3350424 * 2 ^ 59
def prefixEnd_3350424 : Nat := 4983230072969 + 3 ^ 40 * 3350424 * 2
def baseEnd_3350424 : Nat := 127435400619222569214199

theorem tailTrace_3350424 : CollatzResearch.WordTrace tailWord_3350424 prefixEnd_3350424 127435400619222569214199 := by
  unfold tailWord_3350424
  simp only [CollatzResearch.WordTrace]
  refine ⟨61100001206996764854297163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81466668275995686472396217 61100001206996764854297163)
  ·
    refine ⟨91650001810495147281445745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61100001206996764854297163 91650001810495147281445745)
    ·
      refine ⟨68737501357871360461084309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91650001810495147281445745 68737501357871360461084309)
      ·
        refine ⟨3222070376150220021613327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68737501357871360461084309 3222070376150220021613327)
        ·
          refine ⟨4833105564225330032419991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222070376150220021613327 4833105564225330032419991)
          ·
            refine ⟨7249658346337995048629987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833105564225330032419991 7249658346337995048629987)
            ·
              refine ⟨10874487519506992572944981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7249658346337995048629987 10874487519506992572944981)
              ·
                refine ⟨127435400619222569214199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10874487519506992572944981 127435400619222569214199)
                ·
                  rfl

theorem cell22_3350424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 8].length) (baseStart_3350424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350424 prefixEnd_3350424 := by exact prefixLift 3350424
  have htrace : WordTrace (prefixWord ++ tailWord_3350424) baseStart_3350424 baseEnd_3350424 := by
    simpa [prefixWord, tailWord_3350424, baseEnd_3350424] using wordTrace_append hprefix tailTrace_3350424
  have hstable : (prefixWord ++ tailWord_3350424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350424).length < 2 ^ (prefixWord ++ tailWord_3350424).sum := by decide
  have hdescent : baseEnd_3350424 < baseStart_3350424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350430 : List Nat := [4, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_3350430 : Nat := 118140960795 + 3350430 * 2 ^ 59
def prefixEnd_3350430 : Nat := 4983230072969 + 3 ^ 40 * 3350430 * 2
def baseEnd_3350430 : Nat := 382306886498540369092591

theorem tailTrace_3350430 : CollatzResearch.WordTrace tailWord_3350430 prefixEnd_3350430 382306886498540369092591 := by
  unfold tailWord_3350430
  simp only [CollatzResearch.WordTrace]
  refine ⟨15275027656496474091664093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81466814167981195155541829 15275027656496474091664093)
  ·
    refine ⟨5728135371186177784374035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15275027656496474091664093 5728135371186177784374035)
    ·
      refine ⟨8592203056779266676561053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5728135371186177784374035 8592203056779266676561053)
      ·
        refine ⟨3222076146292225003710395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8592203056779266676561053 3222076146292225003710395)
        ·
          refine ⟨4833114219438337505565593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222076146292225003710395 4833114219438337505565593)
          ·
            refine ⟨3624835664578753129174195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4833114219438337505565593 3624835664578753129174195)
            ·
              refine ⟨5437253496868129693761293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624835664578753129174195 5437253496868129693761293)
              ·
                refine ⟨2038970061325548635160485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5437253496868129693761293 2038970061325548635160485)
                ·
                  refine ⟨382306886498540369092591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2038970061325548635160485 382306886498540369092591)
                  ·
                    rfl

theorem cell22_3350430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_3350430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350430 prefixEnd_3350430 := by exact prefixLift 3350430
  have htrace : WordTrace (prefixWord ++ tailWord_3350430) baseStart_3350430 baseEnd_3350430 := by
    simpa [prefixWord, tailWord_3350430, baseEnd_3350430] using wordTrace_append hprefix tailTrace_3350430
  have hstable : (prefixWord ++ tailWord_3350430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350430).length < 2 ^ (prefixWord ++ tailWord_3350430).sum := by decide
  have hdescent : baseEnd_3350430 < baseStart_3350430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350527 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 4, 4]
def baseStart_3350527 : Nat := 118140960795 + 3350527 * 2 ^ 59
def prefixEnd_3350527 : Nat := 4983230072969 + 3 ^ 40 * 3350527 * 2
def baseEnd_3350527 : Nat := 1146953864577945187602475

theorem tailTrace_3350527 : CollatzResearch.WordTrace tailWord_3350527 prefixEnd_3350527 1146953864577945187602475 := by
  unfold tailWord_3350527
  simp only [CollatzResearch.WordTrace]
  refine ⟨122203759132620378299593835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81469172755080252199729223 122203759132620378299593835)
  ·
    refine ⟨183305638698930567449390753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122203759132620378299593835 183305638698930567449390753)
    ·
      refine ⟨137479229024197925587043065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183305638698930567449390753 137479229024197925587043065)
      ·
        refine ⟨103109421768148444190282299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137479229024197925587043065 103109421768148444190282299)
        ·
          refine ⟨154664132652222666285423449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103109421768148444190282299 154664132652222666285423449)
          ·
            refine ⟨115998099489166999714067587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154664132652222666285423449 115998099489166999714067587)
            ·
              refine ⟨173997149233750499571101381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115998099489166999714067587 173997149233750499571101381)
              ·
                refine ⟨32624465481328218669581509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173997149233750499571101381 32624465481328218669581509)
                ·
                  refine ⟨6117087277749041000546533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32624465481328218669581509 6117087277749041000546533)
                  ·
                    refine ⟨1146953864577945187602475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6117087277749041000546533 1146953864577945187602475)
                    ·
                      rfl

theorem cell22_3350527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_3350527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350527 prefixEnd_3350527 := by exact prefixLift 3350527
  have htrace : WordTrace (prefixWord ++ tailWord_3350527) baseStart_3350527 baseEnd_3350527 := by
    simpa [prefixWord, tailWord_3350527, baseEnd_3350527] using wordTrace_append hprefix tailTrace_3350527
  have hstable : (prefixWord ++ tailWord_3350527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350527).length < 2 ^ (prefixWord ++ tailWord_3350527).sum := by decide
  have hdescent : baseEnd_3350527 < baseStart_3350527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350529 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3350529 : Nat := 118140960795 + 3350529 * 2 ^ 59
def prefixEnd_3350529 : Nat := 4983230072969 + 3 ^ 40 * 3350529 * 2
def baseEnd_3350529 : Nat := 1146954549218817849052469

theorem tailTrace_3350529 : CollatzResearch.WordTrace tailWord_3350529 prefixEnd_3350529 1146954549218817849052469 := by
  unfold tailWord_3350529
  simp only [CollatzResearch.WordTrace]
  refine ⟨122203832078613132641166641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81469221385742088427444427 122203832078613132641166641)
  ·
    refine ⟨91652874058959849480874981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122203832078613132641166641 91652874058959849480874981)
    ·
      refine ⟨17184913886054971777664059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91652874058959849480874981 17184913886054971777664059)
      ·
        refine ⟨25777370829082457666496089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17184913886054971777664059 25777370829082457666496089)
        ·
          refine ⟨19333028121811843249872067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25777370829082457666496089 19333028121811843249872067)
          ·
            refine ⟨28999542182717764874808101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19333028121811843249872067 28999542182717764874808101)
            ·
              refine ⟨5437414159259580914026519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28999542182717764874808101 5437414159259580914026519)
              ·
                refine ⟨8156121238889371371039779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5437414159259580914026519 8156121238889371371039779)
                ·
                  refine ⟨12234181858334057056559669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8156121238889371371039779 12234181858334057056559669)
                  ·
                    refine ⟨1146954549218817849052469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12234181858334057056559669 1146954549218817849052469)
                    ·
                      rfl

theorem cell22_3350529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3350529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350529 prefixEnd_3350529 := by exact prefixLift 3350529
  have htrace : WordTrace (prefixWord ++ tailWord_3350529) baseStart_3350529 baseEnd_3350529 := by
    simpa [prefixWord, tailWord_3350529, baseEnd_3350529] using wordTrace_append hprefix tailTrace_3350529
  have hstable : (prefixWord ++ tailWord_3350529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350529).length < 2 ^ (prefixWord ++ tailWord_3350529).sum := by decide
  have hdescent : baseEnd_3350529 < baseStart_3350529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350572 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_3350572 : Nat := 118140960795 + 3350572 * 2 ^ 59
def prefixEnd_3350572 : Nat := 4983230072969 + 3 ^ 40 * 3350572 * 2
def baseEnd_3350572 : Nat := 1146969268997580070227337

theorem tailTrace_3350572 : CollatzResearch.WordTrace tailWord_3350572 prefixEnd_3350572 1146969268997580070227337 := by
  unfold tailWord_3350572
  simp only [CollatzResearch.WordTrace]
  refine ⟨61102700208728675492490985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81470266944971567323321313 61102700208728675492490985)
  ·
    refine ⟨45827025156546506619368239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61102700208728675492490985 45827025156546506619368239)
    ·
      refine ⟨68740537734819759929052359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45827025156546506619368239 68740537734819759929052359)
      ·
        refine ⟨103110806602229639893578539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68740537734819759929052359 103110806602229639893578539)
        ·
          refine ⟨154666209903344459840367809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103110806602229639893578539 154666209903344459840367809)
          ·
            refine ⟨115999657427508344880275857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154666209903344459840367809 115999657427508344880275857)
            ·
              refine ⟨86999743070631258660206893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115999657427508344880275857 86999743070631258660206893)
              ·
                refine ⟨32624903651486721997577585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86999743070631258660206893 32624903651486721997577585)
                ·
                  refine ⟨24468677738615041498183189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32624903651486721997577585 24468677738615041498183189)
                  ·
                    refine ⟨1146969268997580070227337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24468677738615041498183189 1146969268997580070227337)
                    ·
                      rfl

theorem cell22_3350572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_3350572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350572 prefixEnd_3350572 := by exact prefixLift 3350572
  have htrace : WordTrace (prefixWord ++ tailWord_3350572) baseStart_3350572 baseEnd_3350572 := by
    simpa [prefixWord, tailWord_3350572, baseEnd_3350572] using wordTrace_append hprefix tailTrace_3350572
  have hstable : (prefixWord ++ tailWord_3350572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350572).length < 2 ^ (prefixWord ++ tailWord_3350572).sum := by decide
  have hdescent : baseEnd_3350572 < baseStart_3350572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350580 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_3350580 : Nat := 118140960795 + 3350580 * 2 ^ 59
def prefixEnd_3350580 : Nat := 4983230072969 + 3 ^ 40 * 3350580 * 2
def baseEnd_3350580 : Nat := 1146972007561070716027313

theorem tailTrace_3350580 : CollatzResearch.WordTrace tailWord_3350580 prefixEnd_3350580 1146972007561070716027313 := by
  unfold tailWord_3350580
  simp only [CollatzResearch.WordTrace]
  refine ⟨61102846100714184175636597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81470461467618912234182129 61102846100714184175636597)
  ·
    refine ⟨5728391821941954766465931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61102846100714184175636597 5728391821941954766465931)
    ·
      refine ⟨8592587732912932149698897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5728391821941954766465931 8592587732912932149698897)
      ·
        refine ⟨6444440799684699112274173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8592587732912932149698897 6444440799684699112274173)
        ·
          refine ⟨2416665299881762167102815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6444440799684699112274173 2416665299881762167102815)
          ·
            refine ⟨3624997949822643250654223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416665299881762167102815 3624997949822643250654223)
            ·
              refine ⟨5437496924733964875981335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624997949822643250654223 5437496924733964875981335)
              ·
                refine ⟨8156245387100947313972003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5437496924733964875981335 8156245387100947313972003)
                ·
                  refine ⟨12234368080651420970958005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8156245387100947313972003 12234368080651420970958005)
                  ·
                    refine ⟨1146972007561070716027313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12234368080651420970958005 1146972007561070716027313)
                    ·
                      rfl

theorem cell22_3350580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_3350580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350580 prefixEnd_3350580 := by exact prefixLift 3350580
  have htrace : WordTrace (prefixWord ++ tailWord_3350580) baseStart_3350580 baseEnd_3350580 := by
    simpa [prefixWord, tailWord_3350580, baseEnd_3350580] using wordTrace_append hprefix tailTrace_3350580
  have hstable : (prefixWord ++ tailWord_3350580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350580).length < 2 ^ (prefixWord ++ tailWord_3350580).sum := by decide
  have hdescent : baseEnd_3350580 < baseStart_3350580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350621 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 7]
def baseStart_3350621 : Nat := 118140960795 + 3350621 * 2 ^ 59
def prefixEnd_3350621 : Nat := 4983230072969 + 3 ^ 40 * 3350621 * 2
def baseEnd_3350621 : Nat := 382328680899653425250729

theorem tailTrace_3350621 : CollatzResearch.WordTrace tailWord_3350621 prefixEnd_3350621 382328680899653425250729 := by
  unfold tailWord_3350621
  simp only [CollatzResearch.WordTrace]
  refine ⟨122207187594279832353515717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81471458396186554902343811 122207187594279832353515717)
  ·
    refine ⟨22913847673927468566284197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122207187594279832353515717 22913847673927468566284197)
    ·
      refine ⟨4296346438861400356178287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22913847673927468566284197 4296346438861400356178287)
      ·
        refine ⟨6444519658292100534267431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4296346438861400356178287 6444519658292100534267431)
        ·
          refine ⟨9666779487438150801401147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6444519658292100534267431 9666779487438150801401147)
          ·
            refine ⟨14500169231157226202101721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9666779487438150801401147 14500169231157226202101721)
            ·
              refine ⟨10875126923367919651576291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14500169231157226202101721 10875126923367919651576291)
              ·
                refine ⟨16312690385051879477364437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10875126923367919651576291 16312690385051879477364437)
                ·
                  refine ⟨382328680899653425250729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16312690385051879477364437 382328680899653425250729)
                  ·
                    rfl

theorem cell22_3350621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_3350621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350621 prefixEnd_3350621 := by exact prefixLift 3350621
  have htrace : WordTrace (prefixWord ++ tailWord_3350621) baseStart_3350621 baseEnd_3350621 := by
    simpa [prefixWord, tailWord_3350621, baseEnd_3350621] using wordTrace_append hprefix tailTrace_3350621
  have hstable : (prefixWord ++ tailWord_3350621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350621).length < 2 ^ (prefixWord ++ tailWord_3350621).sum := by decide
  have hdescent : baseEnd_3350621 < baseStart_3350621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350676 : List Nat := [2, 4, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3350676 : Nat := 118140960795 + 3350676 * 2 ^ 59
def prefixEnd_3350676 : Nat := 4983230072969 + 3 ^ 40 * 3350676 * 2
def baseEnd_3350676 : Nat := 1147004870322958465627019

theorem tailTrace_3350676 : CollatzResearch.WordTrace tailWord_3350676 prefixEnd_3350676 1147004870322958465627019 := by
  unfold tailWord_3350676
  simp only [CollatzResearch.WordTrace]
  refine ⟨61104596804540288373383941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81472795739387051164511921 61104596804540288373383941)
  ·
    refine ⟨11457111900851304070009489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61104596804540288373383941 11457111900851304070009489)
    ·
      refine ⟨8592833925638478052507117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11457111900851304070009489 8592833925638478052507117)
      ·
        refine ⟨3222312722114429269690169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8592833925638478052507117 3222312722114429269690169)
        ·
          refine ⟨2416734541585821952267627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3222312722114429269690169 2416734541585821952267627)
          ·
            refine ⟨3625101812378732928401441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416734541585821952267627 3625101812378732928401441)
            ·
              refine ⟨2718826359284049696301081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625101812378732928401441 2718826359284049696301081)
              ·
                refine ⟨2039119769463037272225811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2718826359284049696301081 2039119769463037272225811)
                ·
                  refine ⟨3058679654194555908338717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039119769463037272225811 3058679654194555908338717)
                  ·
                    refine ⟨1147004870322958465627019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3058679654194555908338717 1147004870322958465627019)
                    ·
                      rfl

theorem cell22_3350676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3350676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350676 prefixEnd_3350676 := by exact prefixLift 3350676
  have htrace : WordTrace (prefixWord ++ tailWord_3350676) baseStart_3350676 baseEnd_3350676 := by
    simpa [prefixWord, tailWord_3350676, baseEnd_3350676] using wordTrace_append hprefix tailTrace_3350676
  have hstable : (prefixWord ++ tailWord_3350676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350676).length < 2 ^ (prefixWord ++ tailWord_3350676).sum := by decide
  have hdescent : baseEnd_3350676 < baseStart_3350676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350711 : List Nat := [1, 1, 3, 1, 4, 3, 3, 6]
def baseStart_3350711 : Nat := 118140960795 + 3350711 * 2 ^ 59
def prefixEnd_3350711 : Nat := 4983230072969 + 3 ^ 40 * 3350711 * 2
def baseEnd_3350711 : Nat := 127446316837581115666879

theorem tailTrace_3350711 : CollatzResearch.WordTrace tailWord_3350711 prefixEnd_3350711 127446316837581115666879 := by
  unfold tailWord_3350711
  simp only [CollatzResearch.WordTrace]
  refine ⟨122210470163953777724291987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81473646775969185149527991 122210470163953777724291987)
  ·
    refine ⟨183315705245930666586437981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122210470163953777724291987 183315705245930666586437981)
    ·
      refine ⟨68743389467223999969914243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183315705245930666586437981 68743389467223999969914243)
      ·
        refine ⟨103115084200835999954871365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68743389467223999969914243 103115084200835999954871365)
        ·
          refine ⟨19334078287656749991538381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103115084200835999954871365 19334078287656749991538381)
          ·
            refine ⟨7250279357871281246826893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19334078287656749991538381 7250279357871281246826893)
            ·
              refine ⟨2718854759201730467560085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7250279357871281246826893 2718854759201730467560085)
              ·
                refine ⟨127446316837581115666879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2718854759201730467560085 127446316837581115666879)
                ·
                  rfl

theorem cell22_3350711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 6].length) (baseStart_3350711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350711 prefixEnd_3350711 := by exact prefixLift 3350711
  have htrace : WordTrace (prefixWord ++ tailWord_3350711) baseStart_3350711 baseEnd_3350711 := by
    simpa [prefixWord, tailWord_3350711, baseEnd_3350711] using wordTrace_append hprefix tailTrace_3350711
  have hstable : (prefixWord ++ tailWord_3350711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350711).length < 2 ^ (prefixWord ++ tailWord_3350711).sum := by decide
  have hdescent : baseEnd_3350711 < baseStart_3350711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350732 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 2, 3]
def baseStart_3350732 : Nat := 118140960795 + 3350732 * 2 ^ 59
def prefixEnd_3350732 : Nat := 4983230072969 + 3 ^ 40 * 3350732 * 2
def baseEnd_3350732 : Nat := 1147024040267392986226847

theorem tailTrace_3350732 : CollatzResearch.WordTrace tailWord_3350732 prefixEnd_3350732 1147024040267392986226847 := by
  unfold tailWord_3350732
  simp only [CollatzResearch.WordTrace]
  refine ⟨61105618048438849155403225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81474157397918465540537633 61105618048438849155403225)
  ·
    refine ⟨45829213536329136866552419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61105618048438849155403225 45829213536329136866552419)
    ·
      refine ⟨68743820304493705299828629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45829213536329136866552419 68743820304493705299828629)
      ·
        refine ⟨3222366576773142435929467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68743820304493705299828629 3222366576773142435929467)
        ·
          refine ⟨4833549865159713653894201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222366576773142435929467 4833549865159713653894201)
          ·
            refine ⟨3625162398869785240420651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4833549865159713653894201 3625162398869785240420651)
            ·
              refine ⟨5437743598304677860630977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625162398869785240420651 5437743598304677860630977)
              ·
                refine ⟨4078307698728508395473233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5437743598304677860630977 4078307698728508395473233)
                ·
                  refine ⟨3058730774046381296604925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4078307698728508395473233 3058730774046381296604925)
                  ·
                    refine ⟨1147024040267392986226847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3058730774046381296604925 1147024040267392986226847)
                    ·
                      rfl

theorem cell22_3350732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_3350732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350732 prefixEnd_3350732 := by exact prefixLift 3350732
  have htrace : WordTrace (prefixWord ++ tailWord_3350732) baseStart_3350732 baseEnd_3350732 := by
    simpa [prefixWord, tailWord_3350732, baseEnd_3350732] using wordTrace_append hprefix tailTrace_3350732
  have hstable : (prefixWord ++ tailWord_3350732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350732).length < 2 ^ (prefixWord ++ tailWord_3350732).sum := by decide
  have hdescent : baseEnd_3350732 < baseStart_3350732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350784 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 8]
def baseStart_3350784 : Nat := 118140960795 + 3350784 * 2 ^ 59
def prefixEnd_3350784 : Nat := 4983230072969 + 3 ^ 40 * 3350784 * 2
def baseEnd_3350784 : Nat := 382347280310027394642229

theorem tailTrace_3350784 : CollatzResearch.WordTrace tailWord_3350784 prefixEnd_3350784 382347280310027394642229 := by
  unfold tailWord_3350784
  simp only [CollatzResearch.WordTrace]
  refine ⟨61106566346344655595849703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81475421795126207461132937 61106566346344655595849703)
  ·
    refine ⟨91659849519516983393774555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61106566346344655595849703 91659849519516983393774555)
    ·
      refine ⟨137489774279275475090661833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91659849519516983393774555 137489774279275475090661833)
      ·
        refine ⟨103117330709456606317996375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137489774279275475090661833 103117330709456606317996375)
        ·
          refine ⟨154675996064184909476994563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103117330709456606317996375 154675996064184909476994563)
          ·
            refine ⟨232013994096277364215491845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154675996064184909476994563 232013994096277364215491845)
            ·
              refine ⟨43502623893052005790404721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232013994096277364215491845 43502623893052005790404721)
              ·
                refine ⟨32626967919789004342803541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43502623893052005790404721 32626967919789004342803541)
                ·
                  refine ⟨382347280310027394642229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32626967919789004342803541 382347280310027394642229)
                  ·
                    rfl

theorem cell22_3350784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_3350784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350784 prefixEnd_3350784 := by exact prefixLift 3350784
  have htrace : WordTrace (prefixWord ++ tailWord_3350784) baseStart_3350784 baseEnd_3350784 := by
    simpa [prefixWord, tailWord_3350784, baseEnd_3350784] using wordTrace_append hprefix tailTrace_3350784
  have hstable : (prefixWord ++ tailWord_3350784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350784).length < 2 ^ (prefixWord ++ tailWord_3350784).sum := by decide
  have hdescent : baseEnd_3350784 < baseStart_3350784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350801 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 6]
def baseStart_3350801 : Nat := 118140960795 + 3350801 * 2 ^ 59
def prefixEnd_3350801 : Nat := 4983230072969 + 3 ^ 40 * 3350801 * 2
def baseEnd_3350801 : Nat := 382349220125833268750545

theorem tailTrace_3350801 : CollatzResearch.WordTrace tailWord_3350801 prefixEnd_3350801 382349220125833268750545 := by
  unfold tailWord_3350801
  simp only [CollatzResearch.WordTrace]
  refine ⟨122213752733627723095068257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81475835155751815396712171 122213752733627723095068257)
  ·
    refine ⟨91660314550220792321301193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122213752733627723095068257 91660314550220792321301193)
    ·
      refine ⟨68745235912665594240975895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91660314550220792321301193 68745235912665594240975895)
      ·
        refine ⟨103117853868998391361463843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68745235912665594240975895 103117853868998391361463843)
        ·
          refine ⟨154676780803497587042195765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103117853868998391361463843 154676780803497587042195765)
          ·
            refine ⟨14500948200327898785205853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154676780803497587042195765 14500948200327898785205853)
            ·
              refine ⟨5437855575122962044452195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14500948200327898785205853 5437855575122962044452195)
              ·
                refine ⟨8156783362684443066678293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5437855575122962044452195 8156783362684443066678293)
                ·
                  refine ⟨382349220125833268750545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8156783362684443066678293 382349220125833268750545)
                  ·
                    rfl

theorem cell22_3350801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_3350801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350801 prefixEnd_3350801 := by exact prefixLift 3350801
  have htrace : WordTrace (prefixWord ++ tailWord_3350801) baseStart_3350801 baseEnd_3350801 := by
    simpa [prefixWord, tailWord_3350801, baseEnd_3350801] using wordTrace_append hprefix tailTrace_3350801
  have hstable : (prefixWord ++ tailWord_3350801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350801).length < 2 ^ (prefixWord ++ tailWord_3350801).sum := by decide
  have hdescent : baseEnd_3350801 < baseStart_3350801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350820 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_3350820 : Nat := 118140960795 + 3350820 * 2 ^ 59
def prefixEnd_3350820 : Nat := 4983230072969 + 3 ^ 40 * 3350820 * 2
def baseEnd_3350820 : Nat := 1147054164465790090026577

theorem tailTrace_3350820 : CollatzResearch.WordTrace tailWord_3350820 prefixEnd_3350820 1147054164465790090026577 := by
  unfold tailWord_3350820
  simp only [CollatzResearch.WordTrace]
  refine ⟨61107222860279444670004957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81476297147039259560006609 61107222860279444670004957)
  ·
    refine ⟨22915208572604791751251859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61107222860279444670004957 22915208572604791751251859)
    ·
      refine ⟨34372812858907187626877789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22915208572604791751251859 34372812858907187626877789)
      ·
        refine ⟨12889804822090195360079171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34372812858907187626877789 12889804822090195360079171)
        ·
          refine ⟨19334707233135293040118757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12889804822090195360079171 19334707233135293040118757)
          ·
            refine ⟨3625257606212867445022267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19334707233135293040118757 3625257606212867445022267)
            ·
              refine ⟨5437886409319301167533401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625257606212867445022267 5437886409319301167533401)
              ·
                refine ⟨4078414806989475875650051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5437886409319301167533401 4078414806989475875650051)
                ·
                  refine ⟨6117622210484213813475077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078414806989475875650051 6117622210484213813475077)
                  ·
                    refine ⟨1147054164465790090026577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6117622210484213813475077 1147054164465790090026577)
                    ·
                      rfl

theorem cell22_3350820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_3350820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350820 prefixEnd_3350820 := by exact prefixLift 3350820
  have htrace : WordTrace (prefixWord ++ tailWord_3350820) baseStart_3350820 baseEnd_3350820 := by
    simpa [prefixWord, tailWord_3350820, baseEnd_3350820] using wordTrace_append hprefix tailTrace_3350820
  have hstable : (prefixWord ++ tailWord_3350820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350820).length < 2 ^ (prefixWord ++ tailWord_3350820).sum := by decide
  have hdescent : baseEnd_3350820 < baseStart_3350820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350831 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 2, 4]
def baseStart_3350831 : Nat := 118140960795 + 3350831 * 2 ^ 59
def prefixEnd_3350831 : Nat := 4983230072969 + 3 ^ 40 * 3350831 * 2
def baseEnd_3350831 : Nat := 1147057929990589728001543

theorem tailTrace_3350831 : CollatzResearch.WordTrace tailWord_3350831 prefixEnd_3350831 1147057929990589728001543 := by
  unfold tailWord_3350831
  simp only [CollatzResearch.WordTrace]
  refine ⟨122214846923519038218660347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81476564615679358812440231 122214846923519038218660347)
  ·
    refine ⟨183322270385278557327990521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122214846923519038218660347 183322270385278557327990521)
    ·
      refine ⟨137491702788958917995992891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183322270385278557327990521 137491702788958917995992891)
      ·
        refine ⟨206237554183438376993989337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137491702788958917995992891 206237554183438376993989337)
        ·
          refine ⟨154678165637578782745492003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206237554183438376993989337 154678165637578782745492003)
          ·
            refine ⟨232017248456368174118238005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154678165637578782745492003 232017248456368174118238005)
            ·
              refine ⟨21751617042784516323584813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232017248456368174118238005 21751617042784516323584813)
              ·
                refine ⟨8156856391044193621344305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21751617042784516323584813 8156856391044193621344305)
                ·
                  refine ⟨6117642293283145216008229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8156856391044193621344305 6117642293283145216008229)
                  ·
                    refine ⟨1147057929990589728001543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6117642293283145216008229 1147057929990589728001543)
                    ·
                      rfl

theorem cell22_3350831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_3350831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350831 prefixEnd_3350831 := by exact prefixLift 3350831
  have htrace : WordTrace (prefixWord ++ tailWord_3350831) baseStart_3350831 baseEnd_3350831 := by
    simpa [prefixWord, tailWord_3350831, baseEnd_3350831] using wordTrace_append hprefix tailTrace_3350831
  have hstable : (prefixWord ++ tailWord_3350831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350831).length < 2 ^ (prefixWord ++ tailWord_3350831).sum := by decide
  have hdescent : baseEnd_3350831 < baseStart_3350831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350833 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 1, 5]
def baseStart_3350833 : Nat := 118140960795 + 3350833 * 2 ^ 59
def prefixEnd_3350833 : Nat := 4983230072969 + 3 ^ 40 * 3350833 * 2
def baseEnd_3350833 : Nat := 1147058614631462389451537

theorem tailTrace_3350833 : CollatzResearch.WordTrace tailWord_3350833 prefixEnd_3350833 1147058614631462389451537 := by
  unfold tailWord_3350833
  simp only [CollatzResearch.WordTrace]
  refine ⟨122214919869511792560233153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81476613246341195040155435 122214919869511792560233153)
  ·
    refine ⟨91661189902133844420174865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122214919869511792560233153 91661189902133844420174865)
    ·
      refine ⟨68745892426600383315131149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91661189902133844420174865 68745892426600383315131149)
      ·
        refine ⟨25779709659975143743174181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68745892426600383315131149 25779709659975143743174181)
        ·
          refine ⟨4833695561245339451845159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25779709659975143743174181 4833695561245339451845159)
          ·
            refine ⟨7250543341868009177767739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833695561245339451845159 7250543341868009177767739)
            ·
              refine ⟨10875815012802013766651609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250543341868009177767739 10875815012802013766651609)
              ·
                refine ⟨8156861259601510324988707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10875815012802013766651609 8156861259601510324988707)
                ·
                  refine ⟨12235291889402265487483061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8156861259601510324988707 12235291889402265487483061)
                  ·
                    refine ⟨1147058614631462389451537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12235291889402265487483061 1147058614631462389451537)
                    ·
                      rfl

theorem cell22_3350833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_3350833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350833 prefixEnd_3350833 := by exact prefixLift 3350833
  have htrace : WordTrace (prefixWord ++ tailWord_3350833) baseStart_3350833 baseEnd_3350833 := by
    simpa [prefixWord, tailWord_3350833, baseEnd_3350833] using wordTrace_append hprefix tailTrace_3350833
  have hstable : (prefixWord ++ tailWord_3350833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350833).length < 2 ^ (prefixWord ++ tailWord_3350833).sum := by decide
  have hdescent : baseEnd_3350833 < baseStart_3350833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350846 : List Nat := [4, 2, 1, 2, 1, 12]
def baseStart_3350846 : Nat := 118140960795 + 3350846 * 2 ^ 59
def prefixEnd_3350846 : Nat := 4983230072969 + 3 ^ 40 * 3350846 * 2
def baseEnd_3350846 : Nat := 14161272404902897393537

theorem tailTrace_3350846 : CollatzResearch.WordTrace tailWord_3350846 prefixEnd_3350846 14161272404902897393537 := by
  unfold tailWord_3350846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15276924252308086972557049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81476929345643130520304261 15276924252308086972557049)
  ·
    refine ⟨11457693189231065229417787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15276924252308086972557049 11457693189231065229417787)
    ·
      refine ⟨17186539783846597844126681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11457693189231065229417787 17186539783846597844126681)
      ·
        refine ⟨12889904837884948383095011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17186539783846597844126681 12889904837884948383095011)
        ·
          refine ⟨19334857256827422574642517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12889904837884948383095011 19334857256827422574642517)
          ·
            refine ⟨14161272404902897393537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19334857256827422574642517 14161272404902897393537)
            ·
              rfl

theorem cell22_3350846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 12].length) (baseStart_3350846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350846 prefixEnd_3350846 := by exact prefixLift 3350846
  have htrace : WordTrace (prefixWord ++ tailWord_3350846) baseStart_3350846 baseEnd_3350846 := by
    simpa [prefixWord, tailWord_3350846, baseEnd_3350846] using wordTrace_append hprefix tailTrace_3350846
  have hstable : (prefixWord ++ tailWord_3350846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350846).length < 2 ^ (prefixWord ++ tailWord_3350846).sum := by decide
  have hdescent : baseEnd_3350846 < baseStart_3350846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350852 : List Nat := [2, 3, 4, 1, 2, 1, 1, 4, 4]
def baseStart_3350852 : Nat := 118140960795 + 3350852 * 2 ^ 59
def prefixEnd_3350852 : Nat := 4983230072969 + 3 ^ 40 * 3350852 * 2
def baseEnd_3350852 : Nat := 382355039573250891075493

theorem tailTrace_3350852 : CollatzResearch.WordTrace tailWord_3350852 prefixEnd_3350852 382355039573250891075493 := by
  unfold tailWord_3350852
  simp only [CollatzResearch.WordTrace]
  refine ⟨61107806428221479402587405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81477075237628639203449873 61107806428221479402587405)
  ·
    refine ⟨22915427410583054775970277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61107806428221479402587405 22915427410583054775970277)
    ·
      refine ⟨4296642639484322770494427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22915427410583054775970277 4296642639484322770494427)
      ·
        refine ⟨6444963959226484155741641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4296642639484322770494427 6444963959226484155741641)
        ·
          refine ⟨4833722969419863116806231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6444963959226484155741641 4833722969419863116806231)
          ·
            refine ⟨7250584454129794675209347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833722969419863116806231 7250584454129794675209347)
            ·
              refine ⟨10875876681194692012814021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250584454129794675209347 10875876681194692012814021)
              ·
                refine ⟨2039226877724004752402629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10875876681194692012814021 2039226877724004752402629)
                ·
                  refine ⟨382355039573250891075493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2039226877724004752402629 382355039573250891075493)
                  ·
                    rfl

theorem cell22_3350852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_3350852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3350852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3350852 prefixEnd_3350852 := by exact prefixLift 3350852
  have htrace : WordTrace (prefixWord ++ tailWord_3350852) baseStart_3350852 baseEnd_3350852 := by
    simpa [prefixWord, tailWord_3350852, baseEnd_3350852] using wordTrace_append hprefix tailTrace_3350852
  have hstable : (prefixWord ++ tailWord_3350852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350852).length < 2 ^ (prefixWord ++ tailWord_3350852).sum := by decide
  have hdescent : baseEnd_3350852 < baseStart_3350852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351043 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 5]
def baseStart_3351043 : Nat := 118140960795 + 3351043 * 2 ^ 59
def prefixEnd_3351043 : Nat := 4983230072969 + 3 ^ 40 * 3351043 * 2
def baseEnd_3351043 : Nat := 382376833974363947233631

theorem tailTrace_3351043 : CollatzResearch.WordTrace tailWord_3351043 prefixEnd_3351043 382376833974363947233631 := by
  unfold tailWord_3351043
  simp only [CollatzResearch.WordTrace]
  refine ⟨122222579198750998425377783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81481719465833998950251855 122222579198750998425377783)
  ·
    refine ⟨183333868798126497638066675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122222579198750998425377783 183333868798126497638066675)
    ·
      refine ⟨275000803197189746457100013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183333868798126497638066675 275000803197189746457100013)
      ·
        refine ⟨103125301198946154921412505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275000803197189746457100013 103125301198946154921412505)
        ·
          refine ⟨77343975899209616191059379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103125301198946154921412505 77343975899209616191059379)
          ·
            refine ⟨116015963848814424286589069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77343975899209616191059379 116015963848814424286589069)
            ·
              refine ⟨43505986443305409107470901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116015963848814424286589069 43505986443305409107470901)
              ·
                refine ⟨4078686229059882103825397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43505986443305409107470901 4078686229059882103825397)
                ·
                  refine ⟨382376833974363947233631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4078686229059882103825397 382376833974363947233631)
                  ·
                    rfl

theorem cell22_3351043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 5].length) (baseStart_3351043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351043 prefixEnd_3351043 := by exact prefixLift 3351043
  have htrace : WordTrace (prefixWord ++ tailWord_3351043) baseStart_3351043 baseEnd_3351043 := by
    simpa [prefixWord, tailWord_3351043, baseEnd_3351043] using wordTrace_append hprefix tailTrace_3351043
  have hstable : (prefixWord ++ tailWord_3351043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351043).length < 2 ^ (prefixWord ++ tailWord_3351043).sum := by decide
  have hdescent : baseEnd_3351043 < baseStart_3351043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351047 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 3, 3]
def baseStart_3351047 : Nat := 118140960795 + 3351047 * 2 ^ 59
def prefixEnd_3351047 : Nat := 4983230072969 + 3 ^ 40 * 3351047 * 2
def baseEnd_3351047 : Nat := 1147131871204837164600881

theorem tailTrace_3351047 : CollatzResearch.WordTrace tailWord_3351047 prefixEnd_3351047 1147131871204837164600881 := by
  unfold tailWord_3351047
  simp only [CollatzResearch.WordTrace]
  refine ⟨122222725090736507108523395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81481816727157671405682263 122222725090736507108523395)
  ·
    refine ⟨183334087636104760662785093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122222725090736507108523395 183334087636104760662785093)
    ·
      refine ⟨34375141431769642624272205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183334087636104760662785093 34375141431769642624272205)
      ·
        refine ⟨12890678036913615984102077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34375141431769642624272205 12890678036913615984102077)
        ·
          refine ⟨4834004263842605994038279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12890678036913615984102077 4834004263842605994038279)
          ·
            refine ⟨7251006395763908991057419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4834004263842605994038279 7251006395763908991057419)
            ·
              refine ⟨10876509593645863486586129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7251006395763908991057419 10876509593645863486586129)
              ·
                refine ⟨8157382195234397614939597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10876509593645863486586129 8157382195234397614939597)
                ·
                  refine ⟨3059018323212899105602349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8157382195234397614939597 3059018323212899105602349)
                  ·
                    refine ⟨1147131871204837164600881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3059018323212899105602349 1147131871204837164600881)
                    ·
                      rfl

theorem cell22_3351047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_3351047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351047 prefixEnd_3351047 := by exact prefixLift 3351047
  have htrace : WordTrace (prefixWord ++ tailWord_3351047) baseStart_3351047 baseEnd_3351047 := by
    simpa [prefixWord, tailWord_3351047, baseEnd_3351047] using wordTrace_append hprefix tailTrace_3351047
  have hstable : (prefixWord ++ tailWord_3351047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351047).length < 2 ^ (prefixWord ++ tailWord_3351047).sum := by decide
  have hdescent : baseEnd_3351047 < baseStart_3351047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351064 : List Nat := [2, 1, 2, 3, 3, 2, 2, 3, 1, 3]
def baseStart_3351064 : Nat := 118140960795 + 3351064 * 2 ^ 59
def prefixEnd_3351064 : Nat := 4983230072969 + 3 ^ 40 * 3351064 * 2
def baseEnd_3351064 : Nat := 1147137690652254786925829

theorem tailTrace_3351064 : CollatzResearch.WordTrace tailWord_3351064 prefixEnd_3351064 1147137690652254786925829 := by
  unfold tailWord_3351064
  simp only [CollatzResearch.WordTrace]
  refine ⟨61111672565837459505946123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81482230087783279341261497 61111672565837459505946123)
  ·
    refine ⟨91667508848756189258919185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61111672565837459505946123 91667508848756189258919185)
    ·
      refine ⟨68750631636567141944189389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91667508848756189258919185 68750631636567141944189389)
      ·
        refine ⟨25781486863712678229071021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68750631636567141944189389 25781486863712678229071021)
        ·
          refine ⟨9668057573892254335901633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25781486863712678229071021 9668057573892254335901633)
          ·
            refine ⟨7251043180419190751926225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9668057573892254335901633 7251043180419190751926225)
            ·
              refine ⟨5438282385314393063944669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7251043180419190751926225 5438282385314393063944669)
              ·
                refine ⟨2039355894492897398979251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5438282385314393063944669 2039355894492897398979251)
                ·
                  refine ⟨3059033841739346098468877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039355894492897398979251 3059033841739346098468877)
                  ·
                    refine ⟨1147137690652254786925829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3059033841739346098468877 1147137690652254786925829)
                    ·
                      rfl

theorem cell22_3351064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_3351064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351064 prefixEnd_3351064 := by exact prefixLift 3351064
  have htrace : WordTrace (prefixWord ++ tailWord_3351064) baseStart_3351064 baseEnd_3351064 := by
    simpa [prefixWord, tailWord_3351064, baseEnd_3351064] using wordTrace_append hprefix tailTrace_3351064
  have hstable : (prefixWord ++ tailWord_3351064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351064).length < 2 ^ (prefixWord ++ tailWord_3351064).sum := by decide
  have hdescent : baseEnd_3351064 < baseStart_3351064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351088 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 6]
def baseStart_3351088 : Nat := 118140960795 + 3351088 * 2 ^ 59
def prefixEnd_3351088 : Nat := 4983230072969 + 3 ^ 40 * 3351088 * 2
def baseEnd_3351088 : Nat := 382381968780908908108585

theorem tailTrace_3351088 : CollatzResearch.WordTrace tailWord_3351088 prefixEnd_3351088 382381968780908908108585 := by
  unfold tailWord_3351088
  simp only [CollatzResearch.WordTrace]
  refine ⟨61112110241793985555382959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81482813655725314073843945 61112110241793985555382959)
  ·
    refine ⟨91668165362690978333074439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61112110241793985555382959 91668165362690978333074439)
    ·
      refine ⟨137502248044036467499611659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91668165362690978333074439 137502248044036467499611659)
      ·
        refine ⟨206253372066054701249417489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137502248044036467499611659 206253372066054701249417489)
        ·
          refine ⟨154690029049541025937063117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206253372066054701249417489 154690029049541025937063117)
          ·
            refine ⟨58008760893577884726398669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154690029049541025937063117 58008760893577884726398669)
            ·
              refine ⟨21753285335091706772399501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58008760893577884726398669 21753285335091706772399501)
              ·
                refine ⟨8157482000659390039649813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21753285335091706772399501 8157482000659390039649813)
                ·
                  refine ⟨382381968780908908108585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8157482000659390039649813 382381968780908908108585)
                  ·
                    rfl

theorem cell22_3351088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_3351088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351088 prefixEnd_3351088 := by exact prefixLift 3351088
  have htrace : WordTrace (prefixWord ++ tailWord_3351088) baseStart_3351088 baseEnd_3351088 := by
    simpa [prefixWord, tailWord_3351088, baseEnd_3351088] using wordTrace_append hprefix tailTrace_3351088
  have hstable : (prefixWord ++ tailWord_3351088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351088).length < 2 ^ (prefixWord ++ tailWord_3351088).sum := by decide
  have hdescent : baseEnd_3351088 < baseStart_3351088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351094 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_3351094 : Nat := 118140960795 + 3351094 * 2 ^ 59
def prefixEnd_3351094 : Nat := 4983230072969 + 3 ^ 40 * 3351094 * 2
def baseEnd_3351094 : Nat := 382382653421781569558579

theorem tailTrace_3351094 : CollatzResearch.WordTrace tailWord_3351094 prefixEnd_3351094 382382653421781569558579 := by
  unfold tailWord_3351094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7639027457597889633467771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81482959547710822756989557 7639027457597889633467771)
  ·
    refine ⟨11458541186396834450201657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7639027457597889633467771 11458541186396834450201657)
    ·
      refine ⟨8593905889797625837651243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11458541186396834450201657 8593905889797625837651243)
      ·
        refine ⟨12890858834696438756476865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8593905889797625837651243 12890858834696438756476865)
        ·
          refine ⟨9668144126022329067357649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12890858834696438756476865 9668144126022329067357649)
          ·
            refine ⟨7251108094516746800518237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9668144126022329067357649 7251108094516746800518237)
            ·
              refine ⟨2719165535443780050194339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7251108094516746800518237 2719165535443780050194339)
              ·
                refine ⟨4078748303165670075291509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719165535443780050194339 4078748303165670075291509)
                ·
                  refine ⟨382382653421781569558579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4078748303165670075291509 382382653421781569558579)
                  ·
                    rfl

theorem cell22_3351094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_3351094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351094 prefixEnd_3351094 := by exact prefixLift 3351094
  have htrace : WordTrace (prefixWord ++ tailWord_3351094) baseStart_3351094 baseEnd_3351094 := by
    simpa [prefixWord, tailWord_3351094, baseEnd_3351094] using wordTrace_append hprefix tailTrace_3351094
  have hstable : (prefixWord ++ tailWord_3351094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351094).length < 2 ^ (prefixWord ++ tailWord_3351094).sum := by decide
  have hdescent : baseEnd_3351094 < baseStart_3351094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351105 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 6]
def baseStart_3351105 : Nat := 118140960795 + 3351105 * 2 ^ 59
def prefixEnd_3351105 : Nat := 4983230072969 + 3 ^ 40 * 3351105 * 2
def baseEnd_3351105 : Nat := 382383908596714782216901

theorem tailTrace_3351105 : CollatzResearch.WordTrace tailWord_3351105 prefixEnd_3351105 382383908596714782216901 := by
  unfold tailWord_3351105
  simp only [CollatzResearch.WordTrace]
  refine ⟨122224840524526383014134769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81483227016350922009423179 122224840524526383014134769)
  ·
    refine ⟨91668630393394787260601077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122224840524526383014134769 91668630393394787260601077)
    ·
      refine ⟨8593934099380761305681351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91668630393394787260601077 8593934099380761305681351)
      ·
        refine ⟨12890901149071141958522027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8593934099380761305681351 12890901149071141958522027)
        ·
          refine ⟨19336351723606712937783041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12890901149071141958522027 19336351723606712937783041)
          ·
            refine ⟨14502263792705034703337281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19336351723606712937783041 14502263792705034703337281)
            ·
              refine ⟨10876697844528776027502961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14502263792705034703337281 10876697844528776027502961)
              ·
                refine ⟨8157523383396582020627221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10876697844528776027502961 8157523383396582020627221)
                ·
                  refine ⟨382383908596714782216901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8157523383396582020627221 382383908596714782216901)
                  ·
                    rfl

theorem cell22_3351105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_3351105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351105 prefixEnd_3351105 := by exact prefixLift 3351105
  have htrace : WordTrace (prefixWord ++ tailWord_3351105) baseStart_3351105 baseEnd_3351105 := by
    simpa [prefixWord, tailWord_3351105, baseEnd_3351105] using wordTrace_append hprefix tailTrace_3351105
  have hstable : (prefixWord ++ tailWord_3351105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351105).length < 2 ^ (prefixWord ++ tailWord_3351105).sum := by decide
  have hdescent : baseEnd_3351105 < baseStart_3351105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351150 : List Nat := [4, 1, 2, 2, 2, 1, 1, 9]
def baseStart_3351150 : Nat := 118140960795 + 3351150 * 2 ^ 59
def prefixEnd_3351150 : Nat := 4983230072969 + 3 ^ 40 * 3351150 * 2
def baseEnd_3351150 : Nat := 127463014467753247697285

theorem tailTrace_3351150 : CollatzResearch.WordTrace tailWord_3351150 prefixEnd_3351150 127463014467753247697285 := by
  unfold tailWord_3351150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15278310226170419462440363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81484321206242237133015269 15278310226170419462440363)
  ·
    refine ⟨22917465339255629193660545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15278310226170419462440363 22917465339255629193660545)
    ·
      refine ⟨17188099004441721895245409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22917465339255629193660545 17188099004441721895245409)
      ·
        refine ⟨12891074253331291421434057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17188099004441721895245409 12891074253331291421434057)
        ·
          refine ⟨9668305689998468566075543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12891074253331291421434057 9668305689998468566075543)
          ·
            refine ⟨14502458534997702849113315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9668305689998468566075543 14502458534997702849113315)
            ·
              refine ⟨21753687802496554273669973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14502458534997702849113315 21753687802496554273669973)
              ·
                refine ⟨127463014467753247697285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21753687802496554273669973 127463014467753247697285)
                ·
                  rfl

theorem cell22_3351150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_3351150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351150 prefixEnd_3351150 := by exact prefixLift 3351150
  have htrace : WordTrace (prefixWord ++ tailWord_3351150) baseStart_3351150 baseEnd_3351150 := by
    simpa [prefixWord, tailWord_3351150, baseEnd_3351150] using wordTrace_append hprefix tailTrace_3351150
  have hstable : (prefixWord ++ tailWord_3351150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351150).length < 2 ^ (prefixWord ++ tailWord_3351150).sum := by decide
  have hdescent : baseEnd_3351150 < baseStart_3351150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351154 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_3351154 : Nat := 118140960795 + 3351154 * 2 ^ 59
def prefixEnd_3351154 : Nat := 4983230072969 + 3 ^ 40 * 3351154 * 2
def baseEnd_3351154 : Nat := 1147168499491524552175553

theorem tailTrace_3351154 : CollatzResearch.WordTrace tailWord_3351154 prefixEnd_3351154 1147168499491524552175553 := by
  unfold tailWord_3351154
  simp only [CollatzResearch.WordTrace]
  refine ⟨30556656925337216095667129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81484418467565909588445677 30556656925337216095667129)
  ·
    refine ⟨22917492694002912071750347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30556656925337216095667129 22917492694002912071750347)
    ·
      refine ⟨34376239041004368107625521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22917492694002912071750347 34376239041004368107625521)
      ·
        refine ⟨25782179280753276080719141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34376239041004368107625521 25782179280753276080719141)
        ·
          refine ⟨4834158615141239265134839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25782179280753276080719141 4834158615141239265134839)
          ·
            refine ⟨7251237922711858897702259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4834158615141239265134839 7251237922711858897702259)
            ·
              refine ⟨10876856884067788346553389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7251237922711858897702259 10876856884067788346553389)
              ·
                refine ⟨4078821331525420629957521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10876856884067788346553389 4078821331525420629957521)
                ·
                  refine ⟨3059115998644065472468141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4078821331525420629957521 3059115998644065472468141)
                  ·
                    refine ⟨1147168499491524552175553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3059115998644065472468141 1147168499491524552175553)
                    ·
                      rfl

theorem cell22_3351154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_3351154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351154 prefixEnd_3351154 := by exact prefixLift 3351154
  have htrace : WordTrace (prefixWord ++ tailWord_3351154) baseStart_3351154 baseEnd_3351154 := by
    simpa [prefixWord, tailWord_3351154, baseEnd_3351154] using wordTrace_append hprefix tailTrace_3351154
  have hstable : (prefixWord ++ tailWord_3351154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351154).length < 2 ^ (prefixWord ++ tailWord_3351154).sum := by decide
  have hdescent : baseEnd_3351154 < baseStart_3351154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351163 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 4, 6]
def baseStart_3351163 : Nat := 118140960795 + 3351163 * 2 ^ 59
def prefixEnd_3351163 : Nat := 4983230072969 + 3 ^ 40 * 3351163 * 2
def baseEnd_3351163 : Nat := 1147171580375451528700525

theorem tailTrace_3351163 : CollatzResearch.WordTrace tailWord_3351163 prefixEnd_3351163 1147171580375451528700525 := by
  unfold tailWord_3351163
  simp only [CollatzResearch.WordTrace]
  refine ⟨122226955958316258919746143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81484637305544172613164095 122226955958316258919746143)
  ·
    refine ⟨183340433937474388379619215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122226955958316258919746143 183340433937474388379619215)
    ·
      refine ⟨275010650906211582569428823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183340433937474388379619215 275010650906211582569428823)
      ·
        refine ⟨412515976359317373854143235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275010650906211582569428823 412515976359317373854143235)
        ·
          refine ⟨618773964538976060781214853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412515976359317373854143235 618773964538976060781214853)
          ·
            refine ⟨116020118351058011396477785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 618773964538976060781214853 116020118351058011396477785)
            ·
              refine ⟨87015088763293508547358339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116020118351058011396477785 87015088763293508547358339)
              ·
                refine ⟨130522633144940262821037509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87015088763293508547358339 130522633144940262821037509)
                ·
                  refine ⟨24472993714676299278944533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130522633144940262821037509 24472993714676299278944533)
                  ·
                    refine ⟨1147171580375451528700525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24472993714676299278944533 1147171580375451528700525)
                    ·
                      rfl

theorem cell22_3351163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_3351163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351163 prefixEnd_3351163 := by exact prefixLift 3351163
  have htrace : WordTrace (prefixWord ++ tailWord_3351163) baseStart_3351163 baseEnd_3351163 := by
    simpa [prefixWord, tailWord_3351163, baseEnd_3351163] using wordTrace_append hprefix tailTrace_3351163
  have hstable : (prefixWord ++ tailWord_3351163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351163).length < 2 ^ (prefixWord ++ tailWord_3351163).sum := by decide
  have hdescent : baseEnd_3351163 < baseStart_3351163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351257 : List Nat := [1, 2, 1, 2, 3, 2, 1, 6, 4]
def baseStart_3351257 : Nat := 118140960795 + 3351257 * 2 ^ 59
def prefixEnd_3351257 : Nat := 4983230072969 + 3 ^ 40 * 3351257 * 2
def baseEnd_3351257 : Nat := 382401252832155538950079

theorem tailTrace_3351257 : CollatzResearch.WordTrace tailWord_3351257 prefixEnd_3351257 382401252832155538950079 := by
  unfold tailWord_3351257
  simp only [CollatzResearch.WordTrace]
  refine ⟨122230384419975712973668025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81486922946650475315778683 122230384419975712973668025)
  ·
    refine ⟨91672788314981784730251019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122230384419975712973668025 91672788314981784730251019)
    ·
      refine ⟨137509182472472677095376529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91672788314981784730251019 137509182472472677095376529)
      ·
        refine ⟨103131886854354507821532397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137509182472472677095376529 103131886854354507821532397)
        ·
          refine ⟨38674457570382940433074649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103131886854354507821532397 38674457570382940433074649)
          ·
            refine ⟨29005843177787205324805987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38674457570382940433074649 29005843177787205324805987)
            ·
              refine ⟨43508764766680807987208981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29005843177787205324805987 43508764766680807987208981)
              ·
                refine ⟨2039473348438162874400421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43508764766680807987208981 2039473348438162874400421)
                ·
                  refine ⟨382401252832155538950079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2039473348438162874400421 382401252832155538950079)
                  ·
                    rfl

theorem cell22_3351257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 4].length) (baseStart_3351257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351257 prefixEnd_3351257 := by exact prefixLift 3351257
  have htrace : WordTrace (prefixWord ++ tailWord_3351257) baseStart_3351257 baseEnd_3351257 := by
    simpa [prefixWord, tailWord_3351257, baseEnd_3351257] using wordTrace_append hprefix tailTrace_3351257
  have hstable : (prefixWord ++ tailWord_3351257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351257).length < 2 ^ (prefixWord ++ tailWord_3351257).sum := by decide
  have hdescent : baseEnd_3351257 < baseStart_3351257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351315 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 2, 6]
def baseStart_3351315 : Nat := 118140960795 + 3351315 * 2 ^ 59
def prefixEnd_3351315 : Nat := 4983230072969 + 3 ^ 40 * 3351315 * 2
def baseEnd_3351315 : Nat := 1147223613081773798900059

theorem tailTrace_3351315 : CollatzResearch.WordTrace tailWord_3351315 prefixEnd_3351315 1147223613081773798900059 := by
  unfold tailWord_3351315
  simp only [CollatzResearch.WordTrace]
  refine ⟨122232499853765588879279399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81488333235843725919519599 122232499853765588879279399)
  ·
    refine ⟨183348749780648383318919099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122232499853765588879279399 183348749780648383318919099)
    ·
      refine ⟨275023124670972574978378649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183348749780648383318919099 275023124670972574978378649)
      ·
        refine ⟨206267343503229431233783987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275023124670972574978378649 206267343503229431233783987)
        ·
          refine ⟨309401015254844146850675981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206267343503229431233783987 309401015254844146850675981)
          ·
            refine ⟨116025380720566555069003493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309401015254844146850675981 116025380720566555069003493)
            ·
              refine ⟨21754758885106229075438155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116025380720566555069003493 21754758885106229075438155)
              ·
                refine ⟨32632138327659343613157233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21754758885106229075438155 32632138327659343613157233)
                ·
                  refine ⟨24474103745744507709867925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32632138327659343613157233 24474103745744507709867925)
                  ·
                    refine ⟨1147223613081773798900059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24474103745744507709867925 1147223613081773798900059)
                    ·
                      rfl

theorem cell22_3351315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_3351315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351315 prefixEnd_3351315 := by exact prefixLift 3351315
  have htrace : WordTrace (prefixWord ++ tailWord_3351315) baseStart_3351315 baseEnd_3351315 := by
    simpa [prefixWord, tailWord_3351315, baseEnd_3351315] using wordTrace_append hprefix tailTrace_3351315
  have hstable : (prefixWord ++ tailWord_3351315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351315).length < 2 ^ (prefixWord ++ tailWord_3351315).sum := by decide
  have hdescent : baseEnd_3351315 < baseStart_3351315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351375 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 12]
def baseStart_3351375 : Nat := 118140960795 + 3351375 * 2 ^ 59
def prefixEnd_3351375 : Nat := 4983230072969 + 3 ^ 40 * 3351375 * 2
def baseEnd_3351375 : Nat := 382414717435984547466625

theorem tailTrace_3351375 : CollatzResearch.WordTrace tailWord_3351375 prefixEnd_3351375 382414717435984547466625 := by
  unfold tailWord_3351375
  simp only [CollatzResearch.WordTrace]
  refine ⟨122234688233548219126463579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81489792155698812750975719 122234688233548219126463579)
  ·
    refine ⟨183352032350322328689695369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122234688233548219126463579 183352032350322328689695369)
    ·
      refine ⟨137514024262741746517271527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183352032350322328689695369 137514024262741746517271527)
      ·
        refine ⟨206271036394112619775907291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137514024262741746517271527 206271036394112619775907291)
        ·
          refine ⟨309406554591168929663860937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206271036394112619775907291 309406554591168929663860937)
          ·
            refine ⟨232054915943376697247895703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309406554591168929663860937 232054915943376697247895703)
            ·
              refine ⟨348082373915065045871843555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232054915943376697247895703 348082373915065045871843555)
              ·
                refine ⟨522123560872597568807765333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348082373915065045871843555 522123560872597568807765333)
                ·
                  refine ⟨382414717435984547466625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 522123560872597568807765333 382414717435984547466625)
                  ·
                    rfl

theorem cell22_3351375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 12].length) (baseStart_3351375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351375 prefixEnd_3351375 := by exact prefixLift 3351375
  have htrace : WordTrace (prefixWord ++ tailWord_3351375) baseStart_3351375 baseEnd_3351375 := by
    simpa [prefixWord, tailWord_3351375, baseEnd_3351375] using wordTrace_append hprefix tailTrace_3351375
  have hstable : (prefixWord ++ tailWord_3351375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351375).length < 2 ^ (prefixWord ++ tailWord_3351375).sum := by decide
  have hdescent : baseEnd_3351375 < baseStart_3351375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351392 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 6]
def baseStart_3351392 : Nat := 118140960795 + 3351392 * 2 ^ 59
def prefixEnd_3351392 : Nat := 4983230072969 + 3 ^ 40 * 3351392 * 2
def baseEnd_3351392 : Nat := 382416657251790421574941

theorem tailTrace_3351392 : CollatzResearch.WordTrace tailWord_3351392 prefixEnd_3351392 382416657251790421574941 := by
  unfold tailWord_3351392
  simp only [CollatzResearch.WordTrace]
  refine ⟨61117654137243315514916215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81490205516324420686554953 61117654137243315514916215)
  ·
    refine ⟨91676481205864973272374323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61117654137243315514916215 91676481205864973272374323)
    ·
      refine ⟨137514721808797459908561485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91676481205864973272374323 137514721808797459908561485)
      ·
        refine ⟨51568020678299047465710557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137514721808797459908561485 51568020678299047465710557)
        ·
          refine ⟨19338007754362142799641459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51568020678299047465710557 19338007754362142799641459)
          ·
            refine ⟨29007011631543214199462189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19338007754362142799641459 29007011631543214199462189)
            ·
              refine ⟨10877629361828705324798321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29007011631543214199462189 10877629361828705324798321)
              ·
                refine ⟨8158222021371528993598741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10877629361828705324798321 8158222021371528993598741)
                ·
                  refine ⟨382416657251790421574941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8158222021371528993598741 382416657251790421574941)
                  ·
                    rfl

theorem cell22_3351392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_3351392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351392 prefixEnd_3351392 := by exact prefixLift 3351392
  have htrace : WordTrace (prefixWord ++ tailWord_3351392) baseStart_3351392 baseEnd_3351392 := by
    simpa [prefixWord, tailWord_3351392, baseEnd_3351392] using wordTrace_append hprefix tailTrace_3351392
  have hstable : (prefixWord ++ tailWord_3351392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351392).length < 2 ^ (prefixWord ++ tailWord_3351392).sum := by decide
  have hdescent : baseEnd_3351392 < baseStart_3351392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351409 : List Nat := [1, 2, 2, 2, 1, 4, 1, 5, 4]
def baseStart_3351409 : Nat := 118140960795 + 3351409 * 2 ^ 59
def prefixEnd_3351409 : Nat := 4983230072969 + 3 ^ 40 * 3351409 * 2
def baseEnd_3351409 : Nat := 382418597067596295683257

theorem tailTrace_3351409 : CollatzResearch.WordTrace tailWord_3351409 prefixEnd_3351409 382418597067596295683257 := by
  unfold tailWord_3351409
  simp only [CollatzResearch.WordTrace]
  refine ⟨122235928315425042933201281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81490618876950028622134187 122235928315425042933201281)
  ·
    refine ⟨91676946236568782199900961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122235928315425042933201281 91676946236568782199900961)
    ·
      refine ⟨68757709677426586649925721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91676946236568782199900961 68757709677426586649925721)
      ·
        refine ⟨51568282258069939987444291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68757709677426586649925721 51568282258069939987444291)
        ·
          refine ⟨77352423387104909981166437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51568282258069939987444291 77352423387104909981166437)
          ·
            refine ⟨14503579385082170621468707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77352423387104909981166437 14503579385082170621468707)
            ·
              refine ⟨21755369077623255932203061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14503579385082170621468707 21755369077623255932203061)
              ·
                refine ⟨2039565851027180243644037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21755369077623255932203061 2039565851027180243644037)
                ·
                  refine ⟨382418597067596295683257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2039565851027180243644037 382418597067596295683257)
                  ·
                    rfl

theorem cell22_3351409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 4].length) (baseStart_3351409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351409 prefixEnd_3351409 := by exact prefixLift 3351409
  have htrace : WordTrace (prefixWord ++ tailWord_3351409) baseStart_3351409 baseEnd_3351409 := by
    simpa [prefixWord, tailWord_3351409, baseEnd_3351409] using wordTrace_append hprefix tailTrace_3351409
  have hstable : (prefixWord ++ tailWord_3351409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351409).length < 2 ^ (prefixWord ++ tailWord_3351409).sum := by decide
  have hdescent : baseEnd_3351409 < baseStart_3351409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351424 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 2, 3]
def baseStart_3351424 : Nat := 118140960795 + 3351424 * 2 ^ 59
def prefixEnd_3351424 : Nat := 4983230072969 + 3 ^ 40 * 3351424 * 2
def baseEnd_3351424 : Nat := 1147260926009333847924725

theorem tailTrace_3351424 : CollatzResearch.WordTrace tailWord_3351424 prefixEnd_3351424 1147260926009333847924725 := by
  unfold tailWord_3351424
  simp only [CollatzResearch.WordTrace]
  refine ⟨61118237705185350247498663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81490983606913800329998217 61118237705185350247498663)
  ·
    refine ⟨91677356557778025371247995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61118237705185350247498663 91677356557778025371247995)
    ·
      refine ⟨137516034836667038056871993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91677356557778025371247995 137516034836667038056871993)
      ·
        refine ⟨103137026127500278542653995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137516034836667038056871993 103137026127500278542653995)
        ·
          refine ⟨154705539191250417813980993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103137026127500278542653995 154705539191250417813980993)
          ·
            refine ⟨116029154393437813360485745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154705539191250417813980993 116029154393437813360485745)
            ·
              refine ⟨87021865795078360020364309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116029154393437813360485745 87021865795078360020364309)
              ·
                refine ⟨4079149959144298125954577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87021865795078360020364309 4079149959144298125954577)
                ·
                  refine ⟨3059362469358223594465933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4079149959144298125954577 3059362469358223594465933)
                  ·
                    refine ⟨1147260926009333847924725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3059362469358223594465933 1147260926009333847924725)
                    ·
                      rfl

theorem cell22_3351424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2, 3].length) (baseStart_3351424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351424 prefixEnd_3351424 := by exact prefixLift 3351424
  have htrace : WordTrace (prefixWord ++ tailWord_3351424) baseStart_3351424 baseEnd_3351424 := by
    simpa [prefixWord, tailWord_3351424, baseEnd_3351424] using wordTrace_append hprefix tailTrace_3351424
  have hstable : (prefixWord ++ tailWord_3351424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351424).length < 2 ^ (prefixWord ++ tailWord_3351424).sum := by decide
  have hdescent : baseEnd_3351424 < baseStart_3351424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351482 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_3351482 : Nat := 118140960795 + 3351482 * 2 ^ 59
def prefixEnd_3351482 : Nat := 4983230072969 + 3 ^ 40 * 3351482 * 2
def baseEnd_3351482 : Nat := 382426926864880343324849

theorem tailTrace_3351482 : CollatzResearch.WordTrace tailWord_3351482 prefixEnd_3351482 382426926864880343324849 := by
  unfold tailWord_3351482
  simp only [CollatzResearch.WordTrace]
  refine ⟨30559647711040144100152175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81492393896107050933739133 30559647711040144100152175)
  ·
    refine ⟨45839471566560216150228263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30559647711040144100152175 45839471566560216150228263)
    ·
      refine ⟨68759207349840324225342395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45839471566560216150228263 68759207349840324225342395)
      ·
        refine ⟨103138811024760486338013593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68759207349840324225342395 103138811024760486338013593)
        ·
          refine ⟨77354108268570364753510195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103138811024760486338013593 77354108268570364753510195)
          ·
            refine ⟨116031162402855547130265293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77354108268570364753510195 116031162402855547130265293)
            ·
              refine ⟨43511685901070830173849485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116031162402855547130265293 43511685901070830173849485)
              ·
                refine ⟨16316882212901561315193557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43511685901070830173849485 16316882212901561315193557)
                ·
                  refine ⟨382426926864880343324849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16316882212901561315193557 382426926864880343324849)
                  ·
                    rfl

theorem cell22_3351482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_3351482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351482 prefixEnd_3351482 := by exact prefixLift 3351482
  have htrace : WordTrace (prefixWord ++ tailWord_3351482) baseStart_3351482 baseEnd_3351482 := by
    simpa [prefixWord, tailWord_3351482, baseEnd_3351482] using wordTrace_append hprefix tailTrace_3351482
  have hstable : (prefixWord ++ tailWord_3351482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351482).length < 2 ^ (prefixWord ++ tailWord_3351482).sum := by decide
  have hdescent : baseEnd_3351482 < baseStart_3351482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351492 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_3351492 : Nat := 118140960795 + 3351492 * 2 ^ 59
def prefixEnd_3351492 : Nat := 4983230072969 + 3 ^ 40 * 3351492 * 2
def baseEnd_3351492 : Nat := 1147284203799004337224517

theorem tailTrace_3351492 : CollatzResearch.WordTrace tailWord_3351492 prefixEnd_3351492 1147284203799004337224517 := by
  unfold tailWord_3351492
  simp only [CollatzResearch.WordTrace]
  refine ⟨61119477787062174054236365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81492637049416232072315153 61119477787062174054236365)
  ·
    refine ⟨22919804170148315270338637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61119477787062174054236365 22919804170148315270338637)
    ·
      refine ⟨8594926563805618226376989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22919804170148315270338637 8594926563805618226376989)
      ·
        refine ⟨3223097461427106834891371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8594926563805618226376989 3223097461427106834891371)
        ·
          refine ⟨4834646192140660252337057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3223097461427106834891371 4834646192140660252337057)
          ·
            refine ⟨3625984644105495189252793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4834646192140660252337057 3625984644105495189252793)
            ·
              refine ⟨2719488483079121391939595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625984644105495189252793 2719488483079121391939595)
              ·
                refine ⟨4079232724618682087909393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719488483079121391939595 4079232724618682087909393)
                ·
                  refine ⟨3059424543464011565932045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4079232724618682087909393 3059424543464011565932045)
                  ·
                    refine ⟨1147284203799004337224517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3059424543464011565932045 1147284203799004337224517)
                    ·
                      rfl

theorem cell22_3351492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_3351492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351492 prefixEnd_3351492 := by exact prefixLift 3351492
  have htrace : WordTrace (prefixWord ++ tailWord_3351492) baseStart_3351492 baseEnd_3351492 := by
    simpa [prefixWord, tailWord_3351492, baseEnd_3351492] using wordTrace_append hprefix tailTrace_3351492
  have hstable : (prefixWord ++ tailWord_3351492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351492).length < 2 ^ (prefixWord ++ tailWord_3351492).sum := by decide
  have hdescent : baseEnd_3351492 < baseStart_3351492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351499 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 5]
def baseStart_3351499 : Nat := 118140960795 + 3351499 * 2 ^ 59
def prefixEnd_3351499 : Nat := 4983230072969 + 3 ^ 40 * 3351499 * 2
def baseEnd_3351499 : Nat := 382428866680686217433165

theorem tailTrace_3351499 : CollatzResearch.WordTrace tailWord_3351499 prefixEnd_3351499 382428866680686217433165 := by
  unfold tailWord_3351499
  simp only [CollatzResearch.WordTrace]
  refine ⟨122239210885098988303977551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81492807256732658869318367 122239210885098988303977551)
  ·
    refine ⟨183358816327648482455966327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122239210885098988303977551 183358816327648482455966327)
    ·
      refine ⟨275038224491472723683949491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183358816327648482455966327 275038224491472723683949491)
      ·
        refine ⟨412557336737209085525924237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275038224491472723683949491 412557336737209085525924237)
        ·
          refine ⟨154709001276453407072221589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412557336737209085525924237 154709001276453407072221589)
          ·
            refine ⟨7251984434833753456510387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154709001276453407072221589 7251984434833753456510387)
            ·
              refine ⟨10877976652250630184765581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7251984434833753456510387 10877976652250630184765581)
              ·
                refine ⟨4079241244593986319287093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10877976652250630184765581 4079241244593986319287093)
                ·
                  refine ⟨382428866680686217433165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4079241244593986319287093 382428866680686217433165)
                  ·
                    rfl

theorem cell22_3351499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 5].length) (baseStart_3351499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351499 prefixEnd_3351499 := by exact prefixLift 3351499
  have htrace : WordTrace (prefixWord ++ tailWord_3351499) baseStart_3351499 baseEnd_3351499 := by
    simpa [prefixWord, tailWord_3351499, baseEnd_3351499] using wordTrace_append hprefix tailTrace_3351499
  have hstable : (prefixWord ++ tailWord_3351499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351499).length < 2 ^ (prefixWord ++ tailWord_3351499).sum := by decide
  have hdescent : baseEnd_3351499 < baseStart_3351499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351580 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 1, 4]
def baseStart_3351580 : Nat := 118140960795 + 3351580 * 2 ^ 59
def prefixEnd_3351580 : Nat := 4983230072969 + 3 ^ 40 * 3351580 * 2
def baseEnd_3351580 : Nat := 1147314327997401441024247

theorem tailTrace_3351580 : CollatzResearch.WordTrace tailWord_3351580 prefixEnd_3351580 1147314327997401441024247 := by
  unfold tailWord_3351580
  simp only [CollatzResearch.WordTrace]
  refine ⟨61121082598902769568838097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81494776798537026091784129 61121082598902769568838097)
  ·
    refine ⟨45840811949177077176628573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61121082598902769568838097 45840811949177077176628573)
    ·
      refine ⟨17190304480941403941235715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45840811949177077176628573 17190304480941403941235715)
      ·
        refine ⟨25785456721412105911853573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17190304480941403941235715 25785456721412105911853573)
        ·
          refine ⟨4834773135264769858472545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25785456721412105911853573 4834773135264769858472545)
          ·
            refine ⟨3626079851448577393854409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4834773135264769858472545 3626079851448577393854409)
            ·
              refine ⟨2719559888586433045390807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3626079851448577393854409 2719559888586433045390807)
              ·
                refine ⟨4079339832879649568086211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719559888586433045390807 4079339832879649568086211)
                ·
                  refine ⟨6119009749319474352129317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079339832879649568086211 6119009749319474352129317)
                  ·
                    refine ⟨1147314327997401441024247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6119009749319474352129317 1147314327997401441024247)
                    ·
                      rfl

theorem cell22_3351580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_3351580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351580 prefixEnd_3351580 := by exact prefixLift 3351580
  have htrace : WordTrace (prefixWord ++ tailWord_3351580) baseStart_3351580 baseEnd_3351580 := by
    simpa [prefixWord, tailWord_3351580, baseEnd_3351580] using wordTrace_append hprefix tailTrace_3351580
  have hstable : (prefixWord ++ tailWord_3351580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351580).length < 2 ^ (prefixWord ++ tailWord_3351580).sum := by decide
  have hdescent : baseEnd_3351580 < baseStart_3351580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351621 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 3, 3]
def baseStart_3351621 : Nat := 118140960795 + 3351621 * 2 ^ 59
def prefixEnd_3351621 : Nat := 4983230072969 + 3 ^ 40 * 3351621 * 2
def baseEnd_3351621 : Nat := 1147328363135291000749121

theorem tailTrace_3351621 : CollatzResearch.WordTrace tailWord_3351621 prefixEnd_3351621 1147328363135291000749121 := by
  unfold tailWord_3351621
  simp only [CollatzResearch.WordTrace]
  refine ⟨122243660590657003139918717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81495773727104668759945811 122243660590657003139918717)
  ·
    refine ⟨45841372721496376177469519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122243660590657003139918717 45841372721496376177469519)
    ·
      refine ⟨68762059082244564266204279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45841372721496376177469519 68762059082244564266204279)
      ·
        refine ⟨103143088623366846399306419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68762059082244564266204279 103143088623366846399306419)
        ·
          refine ⟨154714632935050269598959629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103143088623366846399306419 154714632935050269598959629)
          ·
            refine ⟨58017987350643851099609861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154714632935050269598959629 58017987350643851099609861)
            ·
              refine ⟨10878372628245722081176849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58017987350643851099609861 10878372628245722081176849)
              ·
                refine ⟨8158779471184291560882637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10878372628245722081176849 8158779471184291560882637)
                ·
                  refine ⟨3059542301694109335330989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8158779471184291560882637 3059542301694109335330989)
                  ·
                    refine ⟨1147328363135291000749121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3059542301694109335330989 1147328363135291000749121)
                    ·
                      rfl

theorem cell22_3351621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_3351621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351621 prefixEnd_3351621 := by exact prefixLift 3351621
  have htrace : WordTrace (prefixWord ++ tailWord_3351621) baseStart_3351621 baseEnd_3351621 := by
    simpa [prefixWord, tailWord_3351621, baseEnd_3351621] using wordTrace_append hprefix tailTrace_3351621
  have hstable : (prefixWord ++ tailWord_3351621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351621).length < 2 ^ (prefixWord ++ tailWord_3351621).sum := by decide
  have hdescent : baseEnd_3351621 < baseStart_3351621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351649 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_3351649 : Nat := 118140960795 + 3351649 * 2 ^ 59
def prefixEnd_3351649 : Nat := 4983230072969 + 3 ^ 40 * 3351649 * 2
def baseEnd_3351649 : Nat := 1147337948107508261049035

theorem tailTrace_3351649 : CollatzResearch.WordTrace tailWord_3351649 prefixEnd_3351649 1147337948107508261049035 := by
  unfold tailWord_3351649
  simp only [CollatzResearch.WordTrace]
  refine ⟨122244681834555563921938001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81496454556370375947958667 122244681834555563921938001)
  ·
    refine ⟨91683511375916672941453501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122244681834555563921938001 91683511375916672941453501)
    ·
      refine ⟨34381316765968752353045063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91683511375916672941453501 34381316765968752353045063)
      ·
        refine ⟨51571975148953128529567595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34381316765968752353045063 51571975148953128529567595)
        ·
          refine ⟨77357962723429692794351393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51571975148953128529567595 77357962723429692794351393)
          ·
            refine ⟨58018472042572269595763545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77357962723429692794351393 58018472042572269595763545)
            ·
              refine ⟨43513854031929202196822659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58018472042572269595763545 43513854031929202196822659)
              ·
                refine ⟨65270781047893803295233989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43513854031929202196822659 65270781047893803295233989)
                ·
                  refine ⟨12238271446480088117856373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65270781047893803295233989 12238271446480088117856373)
                  ·
                    refine ⟨1147337948107508261049035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12238271446480088117856373 1147337948107508261049035)
                    ·
                      rfl

theorem cell22_3351649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_3351649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351649 prefixEnd_3351649 := by exact prefixLift 3351649
  have htrace : WordTrace (prefixWord ++ tailWord_3351649) baseStart_3351649 baseEnd_3351649 := by
    simpa [prefixWord, tailWord_3351649, baseEnd_3351649] using wordTrace_append hprefix tailTrace_3351649
  have hstable : (prefixWord ++ tailWord_3351649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351649).length < 2 ^ (prefixWord ++ tailWord_3351649).sum := by decide
  have hdescent : baseEnd_3351649 < baseStart_3351649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351713 : List Nat := [1, 2, 3, 3, 1, 1, 3, 4, 4]
def baseStart_3351713 : Nat := 118140960795 + 3351713 * 2 ^ 59
def prefixEnd_3351713 : Nat := 4983230072969 + 3 ^ 40 * 3351713 * 2
def baseEnd_3351713 : Nat := 382453285538477809149613

theorem tailTrace_3351713 : CollatzResearch.WordTrace tailWord_3351713 prefixEnd_3351713 382453285538477809149613 := by
  unfold tailWord_3351713
  simp only [CollatzResearch.WordTrace]
  refine ⟨122247016106323702852267793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81498010737549135234845195 122247016106323702852267793)
  ·
    refine ⟨91685262079742777139200845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122247016106323702852267793 91685262079742777139200845)
    ·
      refine ⟨34381973279903541427200317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91685262079742777139200845 34381973279903541427200317)
      ·
        refine ⟨12893239979963828035200119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34381973279903541427200317 12893239979963828035200119)
        ·
          refine ⟨19339859969945742052800179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12893239979963828035200119 19339859969945742052800179)
          ·
            refine ⟨29009789954918613079200269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19339859969945742052800179 29009789954918613079200269)
            ·
              refine ⟨10878671233094479904700101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29009789954918613079200269 10878671233094479904700101)
              ·
                refine ⟨2039750856205214982131269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10878671233094479904700101 2039750856205214982131269)
                ·
                  refine ⟨382453285538477809149613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2039750856205214982131269 382453285538477809149613)
                  ·
                    rfl

theorem cell22_3351713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 4].length) (baseStart_3351713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351713 prefixEnd_3351713 := by exact prefixLift 3351713
  have htrace : WordTrace (prefixWord ++ tailWord_3351713) baseStart_3351713 baseEnd_3351713 := by
    simpa [prefixWord, tailWord_3351713, baseEnd_3351713] using wordTrace_append hprefix tailTrace_3351713
  have hstable : (prefixWord ++ tailWord_3351713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351713).length < 2 ^ (prefixWord ++ tailWord_3351713).sum := by decide
  have hdescent : baseEnd_3351713 < baseStart_3351713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351724 : List Nat := [2, 2, 1, 1, 1, 1, 1, 13]
def baseStart_3351724 : Nat := 118140960795 + 3351724 * 2 ^ 59
def prefixEnd_3351724 : Nat := 4983230072969 + 3 ^ 40 * 3351724 * 2
def baseEnd_3351724 : Nat := 127484846904470340602645

theorem tailTrace_3351724 : CollatzResearch.WordTrace tailWord_3351724 prefixEnd_3351724 127484846904470340602645 := by
  unfold tailWord_3351724
  simp only [CollatzResearch.WordTrace]
  refine ⟨61123708654641925865459113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81498278206189234487278817 61123708654641925865459113)
  ·
    refine ⟨45842781490981444399094335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61123708654641925865459113 45842781490981444399094335)
    ·
      refine ⟨68764172236472166598641503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45842781490981444399094335 68764172236472166598641503)
      ·
        refine ⟨103146258354708249897962255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68764172236472166598641503 103146258354708249897962255)
        ·
          refine ⟨154719387532062374846943383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103146258354708249897962255 154719387532062374846943383)
          ·
            refine ⟨232079081298093562270415075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154719387532062374846943383 232079081298093562270415075)
            ·
              refine ⟨348118621947140343405622613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232079081298093562270415075 348118621947140343405622613)
              ·
                refine ⟨127484846904470340602645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 348118621947140343405622613 127484846904470340602645)
                ·
                  rfl

theorem cell22_3351724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 13].length) (baseStart_3351724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351724 prefixEnd_3351724 := by exact prefixLift 3351724
  have htrace : WordTrace (prefixWord ++ tailWord_3351724) baseStart_3351724 baseEnd_3351724 := by
    simpa [prefixWord, tailWord_3351724, baseEnd_3351724] using wordTrace_append hprefix tailTrace_3351724
  have hstable : (prefixWord ++ tailWord_3351724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351724).length < 2 ^ (prefixWord ++ tailWord_3351724).sum := by decide
  have hdescent : baseEnd_3351724 < baseStart_3351724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351739 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 1, 9]
def baseStart_3351739 : Nat := 118140960795 + 3351739 * 2 ^ 59
def prefixEnd_3351739 : Nat := 4983230072969 + 3 ^ 40 * 3351739 * 2
def baseEnd_3351739 : Nat := 1147368756946778026298759

theorem tailTrace_3351739 : CollatzResearch.WordTrace tailWord_3351739 prefixEnd_3351739 1147368756946778026298759 := by
  unfold tailWord_3351739
  simp only [CollatzResearch.WordTrace]
  refine ⟨122247964404229509292714271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81498642936153006195142847 122247964404229509292714271)
  ·
    refine ⟨183371946606344263939071407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122247964404229509292714271 183371946606344263939071407)
    ·
      refine ⟨275057919909516395908607111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183371946606344263939071407 275057919909516395908607111)
      ·
        refine ⟨412586879864274593862910667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275057919909516395908607111 412586879864274593862910667)
        ·
          refine ⟨618880319796411890794366001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412586879864274593862910667 618880319796411890794366001)
          ·
            refine ⟨464160239847308918095774501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 618880319796411890794366001 464160239847308918095774501)
            ·
              refine ⟨87030044971370422142957719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 464160239847308918095774501 87030044971370422142957719)
              ·
                refine ⟨130545067457055633214436579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87030044971370422142957719 130545067457055633214436579)
                ·
                  refine ⟨195817601185583449821654869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130545067457055633214436579 195817601185583449821654869)
                  ·
                    refine ⟨1147368756946778026298759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 195817601185583449821654869 1147368756946778026298759)
                    ·
                      rfl

theorem cell22_3351739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_3351739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351739 prefixEnd_3351739 := by exact prefixLift 3351739
  have htrace : WordTrace (prefixWord ++ tailWord_3351739) baseStart_3351739 baseEnd_3351739 := by
    simpa [prefixWord, tailWord_3351739, baseEnd_3351739] using wordTrace_append hprefix tailTrace_3351739
  have hstable : (prefixWord ++ tailWord_3351739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351739).length < 2 ^ (prefixWord ++ tailWord_3351739).sum := by decide
  have hdescent : baseEnd_3351739 < baseStart_3351739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351807 : List Nat := [1, 1, 2, 2, 1, 7, 1, 3, 1, 3]
def baseStart_3351807 : Nat := 118140960795 + 3351807 * 2 ^ 59
def prefixEnd_3351807 : Nat := 4983230072969 + 3 ^ 40 * 3351807 * 2
def baseEnd_3351807 : Nat := 1147392034736448515598551

theorem tailTrace_3351807 : CollatzResearch.WordTrace tailWord_3351807 prefixEnd_3351807 1147392034736448515598551 := by
  unfold tailWord_3351807
  simp only [CollatzResearch.WordTrace]
  refine ⟨122250444567983156906189675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81500296378655437937459783 122250444567983156906189675)
  ·
    refine ⟨183375666851974735359284513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122250444567983156906189675 183375666851974735359284513)
    ·
      refine ⟨137531750138981051519463385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183375666851974735359284513 137531750138981051519463385)
      ·
        refine ⟨103148812604235788639597539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137531750138981051519463385 103148812604235788639597539)
        ·
          refine ⟨154723218906353682959396309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103148812604235788639597539 154723218906353682959396309)
          ·
            refine ⟨3626325443117664444360851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 154723218906353682959396309 3626325443117664444360851)
            ·
              refine ⟨5439488164676496666541277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3626325443117664444360851 5439488164676496666541277)
              ·
                refine ⟨2039808061753686249952979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5439488164676496666541277 2039808061753686249952979)
                ·
                  refine ⟨3059712092630529374929469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039808061753686249952979 3059712092630529374929469)
                  ·
                    refine ⟨1147392034736448515598551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3059712092630529374929469 1147392034736448515598551)
                    ·
                      rfl

theorem cell22_3351807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 1, 3].length) (baseStart_3351807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351807 prefixEnd_3351807 := by exact prefixLift 3351807
  have htrace : WordTrace (prefixWord ++ tailWord_3351807) baseStart_3351807 baseEnd_3351807 := by
    simpa [prefixWord, tailWord_3351807, baseEnd_3351807] using wordTrace_append hprefix tailTrace_3351807
  have hstable : (prefixWord ++ tailWord_3351807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351807).length < 2 ^ (prefixWord ++ tailWord_3351807).sum := by decide
  have hdescent : baseEnd_3351807 < baseStart_3351807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351837 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 5]
def baseStart_3351837 : Nat := 118140960795 + 3351837 * 2 ^ 59
def prefixEnd_3351837 : Nat := 4983230072969 + 3 ^ 40 * 3351837 * 2
def baseEnd_3351837 : Nat := 382467434783179479116153

theorem tailTrace_3351837 : CollatzResearch.WordTrace tailWord_3351837 prefixEnd_3351837 382467434783179479116153 := by
  unfold tailWord_3351837
  simp only [CollatzResearch.WordTrace]
  refine ⟨122251538757874472029781765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81501025838582981353187843 122251538757874472029781765)
  ·
    refine ⟨22922163517101463505584081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122251538757874472029781765 22922163517101463505584081)
    ·
      refine ⟨17191622637826097629188061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22922163517101463505584081 17191622637826097629188061)
      ·
        refine ⟨6446858489184786610945523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17191622637826097629188061 6446858489184786610945523)
        ·
          refine ⟨9670287733777179916418285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6446858489184786610945523 9670287733777179916418285)
          ·
            refine ⟨3626357900166442468656857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9670287733777179916418285 3626357900166442468656857)
            ·
              refine ⟨2719768425124831851492643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3626357900166442468656857 2719768425124831851492643)
              ·
                refine ⟨4079652637687247777238965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719768425124831851492643 4079652637687247777238965)
                ·
                  refine ⟨382467434783179479116153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4079652637687247777238965 382467434783179479116153)
                  ·
                    rfl

theorem cell22_3351837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_3351837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351837 prefixEnd_3351837 := by exact prefixLift 3351837
  have htrace : WordTrace (prefixWord ++ tailWord_3351837) baseStart_3351837 baseEnd_3351837 := by
    simpa [prefixWord, tailWord_3351837, baseEnd_3351837] using wordTrace_append hprefix tailTrace_3351837
  have hstable : (prefixWord ++ tailWord_3351837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351837).length < 2 ^ (prefixWord ++ tailWord_3351837).sum := by decide
  have hdescent : baseEnd_3351837 < baseStart_3351837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351850 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3351850 : Nat := 118140960795 + 3351850 * 2 ^ 59
def prefixEnd_3351850 : Nat := 4983230072969 + 3 ^ 40 * 3351850 * 2
def baseEnd_3351850 : Nat := 1147406754515210736773419

theorem tailTrace_3351850 : CollatzResearch.WordTrace tailWord_3351850 prefixEnd_3351850 1147406754515210736773419 := by
  unfold tailWord_3351850
  simp only [CollatzResearch.WordTrace]
  refine ⟨30563003226706843812501251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81501341937884916833336669 30563003226706843812501251)
  ·
    refine ⟨45844504840060265718751877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30563003226706843812501251 45844504840060265718751877)
    ·
      refine ⟨8595844657511299822265977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45844504840060265718751877 8595844657511299822265977)
      ·
        refine ⟨6446883493133474866699483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8595844657511299822265977 6446883493133474866699483)
        ·
          refine ⟨9670325239700212300049225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6446883493133474866699483 9670325239700212300049225)
          ·
            refine ⟨7252743929775159225036919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9670325239700212300049225 7252743929775159225036919)
            ·
              refine ⟨10879115894662738837555379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7252743929775159225036919 10879115894662738837555379)
              ·
                refine ⟨16318673841994108256333069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10879115894662738837555379 16318673841994108256333069)
                ·
                  refine ⟨6119502690747790596124901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16318673841994108256333069 6119502690747790596124901)
                  ·
                    refine ⟨1147406754515210736773419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6119502690747790596124901 1147406754515210736773419)
                    ·
                      rfl

theorem cell22_3351850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3351850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351850 prefixEnd_3351850 := by exact prefixLift 3351850
  have htrace : WordTrace (prefixWord ++ tailWord_3351850) baseStart_3351850 baseEnd_3351850 := by
    simpa [prefixWord, tailWord_3351850, baseEnd_3351850] using wordTrace_append hprefix tailTrace_3351850
  have hstable : (prefixWord ++ tailWord_3351850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351850).length < 2 ^ (prefixWord ++ tailWord_3351850).sum := by decide
  have hdescent : baseEnd_3351850 < baseStart_3351850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351893 : List Nat := [1, 3, 2, 2, 3, 1, 3, 7]
def baseStart_3351893 : Nat := 118140960795 + 3351893 * 2 ^ 59
def prefixEnd_3351893 : Nat := 4983230072969 + 3 ^ 40 * 3351893 * 2
def baseEnd_3351893 : Nat := 127491274921552550883143

theorem tailTrace_3351893 : CollatzResearch.WordTrace tailWord_3351893 prefixEnd_3351893 127491274921552550883143 := by
  unfold tailWord_3351893
  simp only [CollatzResearch.WordTrace]
  refine ⟨122253581245671593593820333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81502387497114395729213555 122253581245671593593820333)
  ·
    refine ⟨45845092967126847597682625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122253581245671593593820333 45845092967126847597682625)
    ·
      refine ⟨34383819725345135698261969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45845092967126847597682625 34383819725345135698261969)
      ·
        refine ⟨25787864794008851773696477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34383819725345135698261969 25787864794008851773696477)
        ·
          refine ⟨9670449297753319415136179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25787864794008851773696477 9670449297753319415136179)
          ·
            refine ⟨14505673946629979122704269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9670449297753319415136179 14505673946629979122704269)
            ·
              refine ⟨5439627729986242171014101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14505673946629979122704269 5439627729986242171014101)
              ·
                refine ⟨127491274921552550883143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5439627729986242171014101 127491274921552550883143)
                ·
                  rfl

theorem cell22_3351893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 7].length) (baseStart_3351893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3351893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3351893 prefixEnd_3351893 := by exact prefixLift 3351893
  have htrace : WordTrace (prefixWord ++ tailWord_3351893) baseStart_3351893 baseEnd_3351893 := by
    simpa [prefixWord, tailWord_3351893, baseEnd_3351893] using wordTrace_append hprefix tailTrace_3351893
  have hstable : (prefixWord ++ tailWord_3351893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351893).length < 2 ^ (prefixWord ++ tailWord_3351893).sum := by decide
  have hdescent : baseEnd_3351893 < baseStart_3351893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
