import V185TrunkScan23Chunk0043

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_261113 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 6, 4]
def baseStart_261113 : Nat := 118140960795 + 261113 * 2 ^ 59
def prefixEnd_261113 : Nat := 4983230072969 + 3 ^ 40 * 261113 * 2
def baseEnd_261113 : Nat := 44692158045847375962223

theorem tailTrace_261113 : CollatzResearch.WordTrace tailWord_261113 prefixEnd_261113 44692158045847375962223 := by
  unfold tailWord_261113
  simp only [CollatzResearch.WordTrace]
  refine ⟨9523573503039670395155993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6349049002026446930103995 9523573503039670395155993)
  ·
    refine ⟨7142680127279752796366995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9523573503039670395155993 7142680127279752796366995)
    ·
      refine ⟨10714020190919629194550493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7142680127279752796366995 10714020190919629194550493)
      ·
        refine ⟨4017757571594860947956435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10714020190919629194550493 4017757571594860947956435)
        ·
          refine ⟨6026636357392291421934653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4017757571594860947956435 6026636357392291421934653)
          ·
            refine ⟨2259988634022109283225495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6026636357392291421934653 2259988634022109283225495)
            ·
              refine ⟨3389982951033163924838243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259988634022109283225495 3389982951033163924838243)
              ·
                refine ⟨5084974426549745887257365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3389982951033163924838243 5084974426549745887257365)
                ·
                  refine ⟨238358176244519338465189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5084974426549745887257365 238358176244519338465189)
                  ·
                    refine ⟨44692158045847375962223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238358176244519338465189 44692158045847375962223)
                    ·
                      rfl

theorem cell23_261113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 4].length) (baseStart_261113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261113 prefixEnd_261113 := by exact prefixLift 261113
  have htrace : WordTrace (prefixWord ++ tailWord_261113) baseStart_261113 baseEnd_261113 := by
    simpa [prefixWord, tailWord_261113, baseEnd_261113] using wordTrace_append hprefix tailTrace_261113
  have hstable : (prefixWord ++ tailWord_261113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261113).length < 2 ^ (prefixWord ++ tailWord_261113).sum := by decide
  have hdescent : baseEnd_261113 < baseStart_261113 := by decide
  rcases family_descends (prefixWord ++ tailWord_261113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261123 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 3]
def baseStart_261123 : Nat := 118140960795 + 261123 * 2 ^ 59
def prefixEnd_261123 : Nat := 4983230072969 + 3 ^ 40 * 261123 * 2
def baseEnd_261123 : Nat := 134081608944087088761623

theorem tailTrace_261123 : CollatzResearch.WordTrace tailWord_261123 prefixEnd_261123 134081608944087088761623 := by
  unfold tailWord_261123
  simp only [CollatzResearch.WordTrace]
  refine ⟨9523938233003442103020023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6349292155335628068680015 9523938233003442103020023)
  ·
    refine ⟨14285907349505163154530035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9523938233003442103020023 14285907349505163154530035)
    ·
      refine ⟨21428861024257744731795053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14285907349505163154530035 21428861024257744731795053)
      ·
        refine ⟨8035822884096654274423145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21428861024257744731795053 8035822884096654274423145)
        ·
          refine ⟨6026867163072490705817359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8035822884096654274423145 6026867163072490705817359)
          ·
            refine ⟨9040300744608736058726039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6026867163072490705817359 9040300744608736058726039)
            ·
              refine ⟨13560451116913104088089059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9040300744608736058726039 13560451116913104088089059)
              ·
                refine ⟨20340676675369656132133589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13560451116913104088089059 20340676675369656132133589)
                ·
                  refine ⟨476734609578976315596881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20340676675369656132133589 476734609578976315596881)
                  ·
                    refine ⟨357550957184232236697661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 476734609578976315596881 357550957184232236697661)
                    ·
                      refine ⟨134081608944087088761623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 357550957184232236697661 134081608944087088761623)
                      ·
                        rfl

theorem cell23_261123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_261123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261123 prefixEnd_261123 := by exact prefixLift 261123
  have htrace : WordTrace (prefixWord ++ tailWord_261123) baseStart_261123 baseEnd_261123 := by
    simpa [prefixWord, tailWord_261123, baseEnd_261123] using wordTrace_append hprefix tailTrace_261123
  have hstable : (prefixWord ++ tailWord_261123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261123).length < 2 ^ (prefixWord ++ tailWord_261123).sum := by decide
  have hdescent : baseEnd_261123 < baseStart_261123 := by decide
  rcases family_descends (prefixWord ++ tailWord_261123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261130 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 4, 4]
def baseStart_261130 : Nat := 118140960795 + 261130 * 2 ^ 59
def prefixEnd_261130 : Nat := 4983230072969 + 3 ^ 40 * 261130 * 2
def baseEnd_261130 : Nat := 44695067769556187124697

theorem tailTrace_261130 : CollatzResearch.WordTrace tailWord_261130 prefixEnd_261130 44695067769556187124697 := by
  unfold tailWord_261130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2381048385994520574631211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6349462362652054865683229 2381048385994520574631211)
  ·
    refine ⟨3571572578991780861946817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2381048385994520574631211 3571572578991780861946817)
    ·
      refine ⟨2678679434243835646460113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3571572578991780861946817 2678679434243835646460113)
      ·
        refine ⟨2009009575682876734845085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2678679434243835646460113 2009009575682876734845085)
        ·
          refine ⟨753378590881078775566907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2009009575682876734845085 753378590881078775566907)
          ·
            refine ⟨1130067886321618163350361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753378590881078775566907 1130067886321618163350361)
            ·
              refine ⟨847550914741213622512771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130067886321618163350361 847550914741213622512771)
              ·
                refine ⟨1271326372111820433769157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847550914741213622512771 1271326372111820433769157)
                ·
                  refine ⟨238373694770966331331717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1271326372111820433769157 238373694770966331331717)
                  ·
                    refine ⟨44695067769556187124697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238373694770966331331717 44695067769556187124697)
                    ·
                      rfl

theorem cell23_261130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_261130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261130 prefixEnd_261130 := by exact prefixLift 261130
  have htrace : WordTrace (prefixWord ++ tailWord_261130) baseStart_261130 baseEnd_261130 := by
    simpa [prefixWord, tailWord_261130, baseEnd_261130] using wordTrace_append hprefix tailTrace_261130
  have hstable : (prefixWord ++ tailWord_261130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261130).length < 2 ^ (prefixWord ++ tailWord_261130).sum := by decide
  have hdescent : baseEnd_261130 < baseStart_261130 := by decide
  rcases family_descends (prefixWord ++ tailWord_261130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261136 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_261136 : Nat := 118140960795 + 261136 * 2 ^ 59
def prefixEnd_261136 : Nat := 4983230072969 + 3 ^ 40 * 261136 * 2
def baseEnd_261136 : Nat := 134088284192595537899063

theorem tailTrace_261136 : CollatzResearch.WordTrace tailWord_261136 prefixEnd_261136 134088284192595537899063 := by
  unfold tailWord_261136
  simp only [CollatzResearch.WordTrace]
  refine ⟨4762206190978172661621631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6349608254637563548828841 4762206190978172661621631)
  ·
    refine ⟨7143309286467258992432447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4762206190978172661621631 7143309286467258992432447)
    ·
      refine ⟨10714963929700888488648671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7143309286467258992432447 10714963929700888488648671)
      ·
        refine ⟨16072445894551332732973007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10714963929700888488648671 16072445894551332732973007)
        ·
          refine ⟨24108668841826999099459511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16072445894551332732973007 24108668841826999099459511)
          ·
            refine ⟨36163003262740498649189267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24108668841826999099459511 36163003262740498649189267)
            ·
              refine ⟨54244504894110747973783901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36163003262740498649189267 54244504894110747973783901)
              ·
                refine ⟨20341689335291530490168963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54244504894110747973783901 20341689335291530490168963)
                ·
                  refine ⟨30512534002937295735253445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20341689335291530490168963 30512534002937295735253445)
                  ·
                    refine ⟨5721100125550742950360021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30512534002937295735253445 5721100125550742950360021)
                    ·
                      refine ⟨134088284192595537899063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5721100125550742950360021 134088284192595537899063)
                      ·
                        rfl

theorem cell23_261136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_261136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261136 prefixEnd_261136 := by exact prefixLift 261136
  have htrace : WordTrace (prefixWord ++ tailWord_261136) baseStart_261136 baseEnd_261136 := by
    simpa [prefixWord, tailWord_261136, baseEnd_261136] using wordTrace_append hprefix tailTrace_261136
  have hstable : (prefixWord ++ tailWord_261136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261136).length < 2 ^ (prefixWord ++ tailWord_261136).sum := by decide
  have hdescent : baseEnd_261136 < baseStart_261136 := by decide
  rcases family_descends (prefixWord ++ tailWord_261136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261138 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 6]
def baseStart_261138 : Nat := 118140960795 + 261138 * 2 ^ 59
def prefixEnd_261138 : Nat := 4983230072969 + 3 ^ 40 * 261138 * 2
def baseEnd_261138 : Nat := 14898812350433836674895

theorem tailTrace_261138 : CollatzResearch.WordTrace tailWord_261138 prefixEnd_261138 14898812350433836674895 := by
  unfold tailWord_261138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2381121331987274916204017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6349656885299399776544045 2381121331987274916204017)
  ·
    refine ⟨1785840998990456187153013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2381121331987274916204017 1785840998990456187153013)
    ·
      refine ⟨167422593655355267545595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1785840998990456187153013 167422593655355267545595)
      ·
        refine ⟨251133890483032901318393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167422593655355267545595 251133890483032901318393)
        ·
          refine ⟨188350417862274675988795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251133890483032901318393 188350417862274675988795)
          ·
            refine ⟨282525626793412013983193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188350417862274675988795 282525626793412013983193)
            ·
              refine ⟨211894220095059010487395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282525626793412013983193 211894220095059010487395)
              ·
                refine ⟨317841330142588515731093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211894220095059010487395 317841330142588515731093)
                ·
                  refine ⟨14898812350433836674895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 317841330142588515731093 14898812350433836674895)
                  ·
                    rfl

theorem cell23_261138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_261138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261138 prefixEnd_261138 := by exact prefixLift 261138
  have htrace : WordTrace (prefixWord ++ tailWord_261138) baseStart_261138 baseEnd_261138 := by
    simpa [prefixWord, tailWord_261138, baseEnd_261138] using wordTrace_append hprefix tailTrace_261138
  have hstable : (prefixWord ++ tailWord_261138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261138).length < 2 ^ (prefixWord ++ tailWord_261138).sum := by decide
  have hdescent : baseEnd_261138 < baseStart_261138 := by decide
  rcases family_descends (prefixWord ++ tailWord_261138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261143 : List Nat := [1, 1, 3, 5, 1, 1, 1, 10]
def baseStart_261143 : Nat := 118140960795 + 261143 * 2 ^ 59
def prefixEnd_261143 : Nat := 4983230072969 + 3 ^ 40 * 261143 * 2
def baseEnd_261143 : Nat := 4966365872488037426353

theorem tailTrace_261143 : CollatzResearch.WordTrace tailWord_261143 prefixEnd_261143 4966365872488037426353 := by
  unfold tailWord_261143
  simp only [CollatzResearch.WordTrace]
  refine ⟨9524667692930985518748083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6349778461953990345832055 9524667692930985518748083)
  ·
    refine ⟨14287001539396478278122125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9524667692930985518748083 14287001539396478278122125)
    ·
      refine ⟨5357625577273679354295797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14287001539396478278122125 5357625577273679354295797)
      ·
        refine ⟨502277397869407439465231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5357625577273679354295797 502277397869407439465231)
        ·
          refine ⟨753416096804111159197847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502277397869407439465231 753416096804111159197847)
          ·
            refine ⟨1130124145206166738796771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753416096804111159197847 1130124145206166738796771)
            ·
              refine ⟨1695186217809250108195157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130124145206166738796771 1695186217809250108195157)
              ·
                refine ⟨4966365872488037426353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1695186217809250108195157 4966365872488037426353)
                ·
                  rfl

theorem cell23_261143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 10].length) (baseStart_261143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261143 prefixEnd_261143 := by exact prefixLift 261143
  have htrace : WordTrace (prefixWord ++ tailWord_261143) baseStart_261143 baseEnd_261143 := by
    simpa [prefixWord, tailWord_261143, baseEnd_261143] using wordTrace_append hprefix tailTrace_261143
  have hstable : (prefixWord ++ tailWord_261143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261143).length < 2 ^ (prefixWord ++ tailWord_261143).sum := by decide
  have hdescent : baseEnd_261143 < baseStart_261143 := by decide
  rcases family_descends (prefixWord ++ tailWord_261143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261170 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_261170 : Nat := 118140960795 + 261170 * 2 ^ 59
def prefixEnd_261170 : Nat := 4983230072969 + 3 ^ 40 * 261170 * 2
def baseEnd_261170 : Nat := 134105742534848404873907

theorem tailTrace_261170 : CollatzResearch.WordTrace tailWord_261170 prefixEnd_261170 134105742534848404873907 := by
  unfold tailWord_261170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2381413115958292282495241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6350434975888779419987309 2381413115958292282495241)
  ·
    refine ⟨1786059836968719211871431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2381413115958292282495241 1786059836968719211871431)
    ·
      refine ⟨2679089755453078817807147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1786059836968719211871431 2679089755453078817807147)
      ·
        refine ⟨4018634633179618226710721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2679089755453078817807147 4018634633179618226710721)
        ·
          refine ⟨3013975974884713670033041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4018634633179618226710721 3013975974884713670033041)
          ·
            refine ⟨2260481981163535252524781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3013975974884713670033041 2260481981163535252524781)
            ·
              refine ⟨847680742936325719696793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2260481981163535252524781 847680742936325719696793)
              ·
                refine ⟨635760557202244289772595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847680742936325719696793 635760557202244289772595)
                ·
                  refine ⟨953640835803366434658893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635760557202244289772595 953640835803366434658893)
                  ·
                    refine ⟨357615313426262412997085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 953640835803366434658893 357615313426262412997085)
                    ·
                      refine ⟨134105742534848404873907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 357615313426262412997085 134105742534848404873907)
                      ·
                        rfl

theorem cell23_261170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_261170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261170 prefixEnd_261170 := by exact prefixLift 261170
  have htrace : WordTrace (prefixWord ++ tailWord_261170) baseStart_261170 baseEnd_261170 := by
    simpa [prefixWord, tailWord_261170, baseEnd_261170] using wordTrace_append hprefix tailTrace_261170
  have hstable : (prefixWord ++ tailWord_261170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261170).length < 2 ^ (prefixWord ++ tailWord_261170).sum := by decide
  have hdescent : baseEnd_261170 < baseStart_261170 := by decide
  rcases family_descends (prefixWord ++ tailWord_261170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261187 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 2, 1, 3]
def baseStart_261187 : Nat := 118140960795 + 261187 * 2 ^ 59
def prefixEnd_261187 : Nat := 4983230072969 + 3 ^ 40 * 261187 * 2
def baseEnd_261187 : Nat := 134114471705974838361329

theorem tailTrace_261187 : CollatzResearch.WordTrace tailWord_261187 prefixEnd_261187 134114471705974838361329 := by
  unfold tailWord_261187
  simp only [CollatzResearch.WordTrace]
  refine ⟨9526272504771581033349815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6350848336514387355566543 9526272504771581033349815)
  ·
    refine ⟨14289408757157371550024723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9526272504771581033349815 14289408757157371550024723)
    ·
      refine ⟨21434113135736057325037085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14289408757157371550024723 21434113135736057325037085)
      ·
        refine ⟨8037792425901021496888907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21434113135736057325037085 8037792425901021496888907)
        ·
          refine ⟨12056688638851532245333361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037792425901021496888907 12056688638851532245333361)
          ·
            refine ⟨9042516479138649184000021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12056688638851532245333361 9042516479138649184000021)
            ·
              refine ⟨423867959959624180500001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9042516479138649184000021 423867959959624180500001)
              ·
                refine ⟨317900969969718135375001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423867959959624180500001 317900969969718135375001)
                ·
                  refine ⟨238425727477288601531251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317900969969718135375001 238425727477288601531251)
                  ·
                    refine ⟨357638591215932902296877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238425727477288601531251 357638591215932902296877)
                    ·
                      refine ⟨134114471705974838361329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 357638591215932902296877 134114471705974838361329)
                      ·
                        rfl

theorem cell23_261187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_261187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261187 prefixEnd_261187 := by exact prefixLift 261187
  have htrace : WordTrace (prefixWord ++ tailWord_261187) baseStart_261187 baseEnd_261187 := by
    simpa [prefixWord, tailWord_261187, baseEnd_261187] using wordTrace_append hprefix tailTrace_261187
  have hstable : (prefixWord ++ tailWord_261187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261187).length < 2 ^ (prefixWord ++ tailWord_261187).sum := by decide
  have hdescent : baseEnd_261187 < baseStart_261187 := by decide
  rcases family_descends (prefixWord ++ tailWord_261187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261273 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_261273 : Nat := 118140960795 + 261273 * 2 ^ 59
def prefixEnd_261273 : Nat := 4983230072969 + 3 ^ 40 * 261273 * 2
def baseEnd_261273 : Nat := 134158631042261501885933

theorem tailTrace_261273 : CollatzResearch.WordTrace tailWord_261273 prefixEnd_261273 134158631042261501885933 := by
  unfold tailWord_261273
  simp only [CollatzResearch.WordTrace]
  refine ⟨9529409182460017720980473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6352939454973345147320315 9529409182460017720980473)
  ·
    refine ⟨7147056886845013290735355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9529409182460017720980473 7147056886845013290735355)
    ·
      refine ⟨10720585330267519936103033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7147056886845013290735355 10720585330267519936103033)
      ·
        refine ⟨8040438997700639952077275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10720585330267519936103033 8040438997700639952077275)
        ·
          refine ⟨12060658496550959928115913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8040438997700639952077275 12060658496550959928115913)
          ·
            refine ⟨9045493872413219946086935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12060658496550959928115913 9045493872413219946086935)
            ·
              refine ⟨13568240808619829919130403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9045493872413219946086935 13568240808619829919130403)
              ·
                refine ⟨20352361212929744878695605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13568240808619829919130403 20352361212929744878695605)
                ·
                  refine ⟨1908033863712163582377713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20352361212929744878695605 1908033863712163582377713)
                  ·
                    refine ⟨1431025397784122686783285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1908033863712163582377713 1431025397784122686783285)
                    ·
                      refine ⟨134158631042261501885933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1431025397784122686783285 134158631042261501885933)
                      ·
                        rfl

theorem cell23_261273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_261273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261273 prefixEnd_261273 := by exact prefixLift 261273
  have htrace : WordTrace (prefixWord ++ tailWord_261273) baseStart_261273 baseEnd_261273 := by
    simpa [prefixWord, tailWord_261273, baseEnd_261273] using wordTrace_append hprefix tailTrace_261273
  have hstable : (prefixWord ++ tailWord_261273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261273).length < 2 ^ (prefixWord ++ tailWord_261273).sum := by decide
  have hdescent : baseEnd_261273 < baseStart_261273 := by decide
  rcases family_descends (prefixWord ++ tailWord_261273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261280 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 2, 5]
def baseStart_261280 : Nat := 118140960795 + 261280 * 2 ^ 59
def prefixEnd_261280 : Nat := 4983230072969 + 3 ^ 40 * 261280 * 2
def baseEnd_261280 : Nat := 44720741802280991499467

theorem tailTrace_261280 : CollatzResearch.WordTrace tailWord_261280 prefixEnd_261280 44720741802280991499467 := by
  unfold tailWord_261280
  simp only [CollatzResearch.WordTrace]
  refine ⟨4764832246717328958242647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6353109662289771944323529 4764832246717328958242647)
  ·
    refine ⟨7147248370075993437363971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4764832246717328958242647 7147248370075993437363971)
    ·
      refine ⟨10720872555113990156045957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7147248370075993437363971 10720872555113990156045957)
      ·
        refine ⟨2010163604083873154258617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10720872555113990156045957 2010163604083873154258617)
        ·
          refine ⟨1507622703062904865693963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2010163604083873154258617 1507622703062904865693963)
          ·
            refine ⟨2261434054594357298540945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507622703062904865693963 2261434054594357298540945)
            ·
              refine ⟨1696075540945767973905709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2261434054594357298540945 1696075540945767973905709)
              ·
                refine ⟨636028327854662990214641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1696075540945767973905709 636028327854662990214641)
                ·
                  refine ⟨477021245890997242660981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636028327854662990214641 477021245890997242660981)
                  ·
                    refine ⟨44720741802280991499467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 477021245890997242660981 44720741802280991499467)
                    ·
                      rfl

theorem cell23_261280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_261280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261280 prefixEnd_261280 := by exact prefixLift 261280
  have htrace : WordTrace (prefixWord ++ tailWord_261280) baseStart_261280 baseEnd_261280 := by
    simpa [prefixWord, tailWord_261280, baseEnd_261280] using wordTrace_append hprefix tailTrace_261280
  have hstable : (prefixWord ++ tailWord_261280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261280).length < 2 ^ (prefixWord ++ tailWord_261280).sum := by decide
  have hdescent : baseEnd_261280 < baseStart_261280 := by decide
  rcases family_descends (prefixWord ++ tailWord_261280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261284 : List Nat := [2, 3, 1, 2, 3, 3, 1, 3, 5]
def baseStart_261284 : Nat := 118140960795 + 261284 * 2 ^ 59
def prefixEnd_261284 : Nat := 4983230072969 + 3 ^ 40 * 261284 * 2
def baseEnd_261284 : Nat := 14907142147717884316487

theorem tailTrace_261284 : CollatzResearch.WordTrace tailWord_261284 prefixEnd_261284 14907142147717884316487 := by
  unfold tailWord_261284
  simp only [CollatzResearch.WordTrace]
  refine ⟨4764905192710083299815453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6353206923613444399753937 4764905192710083299815453)
  ·
    refine ⟨1786839447266281237430795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4764905192710083299815453 1786839447266281237430795)
    ·
      refine ⟨2680259170899421856146193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1786839447266281237430795 2680259170899421856146193)
      ·
        refine ⟨2010194378174566392109645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2680259170899421856146193 2010194378174566392109645)
        ·
          refine ⟨753822891815462397041117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2010194378174566392109645 753822891815462397041117)
          ·
            refine ⟨282683584430798398890419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 753822891815462397041117 282683584430798398890419)
            ·
              refine ⟨424025376646197598335629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282683584430798398890419 424025376646197598335629)
              ·
                refine ⟨159009516242324099375861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424025376646197598335629 159009516242324099375861)
                ·
                  refine ⟨14907142147717884316487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159009516242324099375861 14907142147717884316487)
                  ·
                    rfl

theorem cell23_261284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_261284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261284 prefixEnd_261284 := by exact prefixLift 261284
  have htrace : WordTrace (prefixWord ++ tailWord_261284) baseStart_261284 baseEnd_261284 := by
    simpa [prefixWord, tailWord_261284, baseEnd_261284] using wordTrace_append hprefix tailTrace_261284
  have hstable : (prefixWord ++ tailWord_261284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261284).length < 2 ^ (prefixWord ++ tailWord_261284).sum := by decide
  have hdescent : baseEnd_261284 < baseStart_261284 := by decide
  rcases family_descends (prefixWord ++ tailWord_261284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261297 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 2, 5]
def baseStart_261297 : Nat := 118140960795 + 261297 * 2 ^ 59
def prefixEnd_261297 : Nat := 4983230072969 + 3 ^ 40 * 261297 * 2
def baseEnd_261297 : Nat := 44723651525989802661941

theorem tailTrace_261297 : CollatzResearch.WordTrace tailWord_261297 prefixEnd_261297 44723651525989802661941 := by
  unfold tailWord_261297
  simp only [CollatzResearch.WordTrace]
  refine ⟨9530284534373069819854145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6353523022915379879902763 9530284534373069819854145)
  ·
    refine ⟨7147713400779802364890609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9530284534373069819854145 7147713400779802364890609)
    ·
      refine ⟨5360785050584851773667957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7147713400779802364890609 5360785050584851773667957)
      ·
        refine ⟨502573598492329853781371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5360785050584851773667957 502573598492329853781371)
        ·
          refine ⟨753860397738494780672057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502573598492329853781371 753860397738494780672057)
          ·
            refine ⟨565395298303871085504043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753860397738494780672057 565395298303871085504043)
            ·
              refine ⟨848092947455806628256065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565395298303871085504043 848092947455806628256065)
              ·
                refine ⟨636069710591854971192049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848092947455806628256065 636069710591854971192049)
                ·
                  refine ⟨477052282943891228394037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636069710591854971192049 477052282943891228394037)
                  ·
                    refine ⟨44723651525989802661941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 477052282943891228394037 44723651525989802661941)
                    ·
                      rfl

theorem cell23_261297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_261297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261297 prefixEnd_261297 := by exact prefixLift 261297
  have htrace : WordTrace (prefixWord ++ tailWord_261297) baseStart_261297 baseEnd_261297 := by
    simpa [prefixWord, tailWord_261297, baseEnd_261297] using wordTrace_append hprefix tailTrace_261297
  have hstable : (prefixWord ++ tailWord_261297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261297).length < 2 ^ (prefixWord ++ tailWord_261297).sum := by decide
  have hdescent : baseEnd_261297 < baseStart_261297 := by decide
  rcases family_descends (prefixWord ++ tailWord_261297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261320 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_261320 : Nat := 118140960795 + 261320 * 2 ^ 59
def prefixEnd_261320 : Nat := 4983230072969 + 3 ^ 40 * 261320 * 2
def baseEnd_261320 : Nat := 134182764633022817998217

theorem tailTrace_261320 : CollatzResearch.WordTrace tailWord_261320 prefixEnd_261320 134182764633022817998217 := by
  unfold tailWord_261320
  simp only [CollatzResearch.WordTrace]
  refine ⟨4765561706644872373970707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6354082275526496498627609 4765561706644872373970707)
  ·
    refine ⟨7148342559967308560956061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4765561706644872373970707 7148342559967308560956061)
    ·
      refine ⟨2680628459987740710358523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7148342559967308560956061 2680628459987740710358523)
      ·
        refine ⟨4020942689981611065537785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2680628459987740710358523 4020942689981611065537785)
        ·
          refine ⟨3015707017486208299153339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4020942689981611065537785 3015707017486208299153339)
          ·
            refine ⟨4523560526229312448730009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015707017486208299153339 4523560526229312448730009)
            ·
              refine ⟨3392670394671984336547507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4523560526229312448730009 3392670394671984336547507)
              ·
                refine ⟨5089005592007976504821261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3392670394671984336547507 5089005592007976504821261)
                ·
                  refine ⟨1908377097002991189307973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5089005592007976504821261 1908377097002991189307973)
                  ·
                    refine ⟨357820705688060847995245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1908377097002991189307973 357820705688060847995245)
                    ·
                      refine ⟨134182764633022817998217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 357820705688060847995245 134182764633022817998217)
                      ·
                        rfl

theorem cell23_261320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_261320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261320 prefixEnd_261320 := by exact prefixLift 261320
  have htrace : WordTrace (prefixWord ++ tailWord_261320) baseStart_261320 baseEnd_261320 := by
    simpa [prefixWord, tailWord_261320, baseEnd_261320] using wordTrace_append hprefix tailTrace_261320
  have hstable : (prefixWord ++ tailWord_261320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261320).length < 2 ^ (prefixWord ++ tailWord_261320).sum := by decide
  have hdescent : baseEnd_261320 < baseStart_261320 := by decide
  rcases family_descends (prefixWord ++ tailWord_261320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261323 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 10]
def baseStart_261323 : Nat := 118140960795 + 261323 * 2 ^ 59
def prefixEnd_261323 : Nat := 4983230072969 + 3 ^ 40 * 261323 * 2
def baseEnd_261323 : Nat := 14909367230554034028967

theorem tailTrace_261323 : CollatzResearch.WordTrace tailWord_261323 prefixEnd_261323 14909367230554034028967 := by
  unfold tailWord_261323
  simp only [CollatzResearch.WordTrace]
  refine ⟨9531232832278876260300623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6354155221519250840200415 9531232832278876260300623)
  ·
    refine ⟨14296849248418314390450935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9531232832278876260300623 14296849248418314390450935)
    ·
      refine ⟨21445273872627471585676403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14296849248418314390450935 21445273872627471585676403)
      ·
        refine ⟨32167910808941207378514605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21445273872627471585676403 32167910808941207378514605)
        ·
          refine ⟨12062966553352952766942977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32167910808941207378514605 12062966553352952766942977)
          ·
            refine ⟨9047224915014714575207233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12062966553352952766942977 9047224915014714575207233)
            ·
              refine ⟨6785418686261035931405425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9047224915014714575207233 6785418686261035931405425)
              ·
                refine ⟨5089064014695776948554069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6785418686261035931405425 5089064014695776948554069)
                ·
                  refine ⟨14909367230554034028967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 5089064014695776948554069 14909367230554034028967)
                  ·
                    rfl

theorem cell23_261323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 10].length) (baseStart_261323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261323 prefixEnd_261323 := by exact prefixLift 261323
  have htrace : WordTrace (prefixWord ++ tailWord_261323) baseStart_261323 baseEnd_261323 := by
    simpa [prefixWord, tailWord_261323, baseEnd_261323] using wordTrace_append hprefix tailTrace_261323
  have hstable : (prefixWord ++ tailWord_261323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261323).length < 2 ^ (prefixWord ++ tailWord_261323).sum := by decide
  have hdescent : baseEnd_261323 < baseStart_261323 := by decide
  rcases family_descends (prefixWord ++ tailWord_261323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261357 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 6]
def baseStart_261357 : Nat := 118140960795 + 261357 * 2 ^ 59
def prefixEnd_261357 : Nat := 4983230072969 + 3 ^ 40 * 261357 * 2
def baseEnd_261357 : Nat := 14911307046359908137283

theorem tailTrace_261357 : CollatzResearch.WordTrace tailWord_261357 prefixEnd_261357 14911307046359908137283 := by
  unfold tailWord_261357
  simp only [CollatzResearch.WordTrace]
  refine ⟨9532472914155700067038325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6354981942770466711358883 9532472914155700067038325)
  ·
    refine ⟨893669335702096881284843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9532472914155700067038325 893669335702096881284843)
    ·
      refine ⟨1340504003553145321927265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 893669335702096881284843 1340504003553145321927265)
      ·
        refine ⟨1005378002664858991445449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1340504003553145321927265 1005378002664858991445449)
        ·
          refine ⟨754033501998644243584087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005378002664858991445449 754033501998644243584087)
          ·
            refine ⟨1131050252997966365376131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754033501998644243584087 1131050252997966365376131)
            ·
              refine ⟨1696575379496949548064197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131050252997966365376131 1696575379496949548064197)
              ·
                refine ⟨318107883655678040262037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1696575379496949548064197 318107883655678040262037)
                ·
                  refine ⟨14911307046359908137283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 318107883655678040262037 14911307046359908137283)
                  ·
                    rfl

theorem cell23_261357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_261357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261357 prefixEnd_261357 := by exact prefixLift 261357
  have htrace : WordTrace (prefixWord ++ tailWord_261357) baseStart_261357 baseEnd_261357 := by
    simpa [prefixWord, tailWord_261357, baseEnd_261357] using wordTrace_append hprefix tailTrace_261357
  have hstable : (prefixWord ++ tailWord_261357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261357).length < 2 ^ (prefixWord ++ tailWord_261357).sum := by decide
  have hdescent : baseEnd_261357 < baseStart_261357 := by decide
  rcases family_descends (prefixWord ++ tailWord_261357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261370 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_261370 : Nat := 118140960795 + 261370 * 2 ^ 59
def prefixEnd_261370 : Nat := 4983230072969 + 3 ^ 40 * 261370 * 2
def baseEnd_261370 : Nat := 44736146221915874124329

theorem tailTrace_261370 : CollatzResearch.WordTrace tailWord_261370 prefixEnd_261370 44736146221915874124329 := by
  unfold tailWord_261370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383236765777150821815391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6355298042072402191507709 2383236765777150821815391)
  ·
    refine ⟨3574855148665726232723087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2383236765777150821815391 3574855148665726232723087)
    ·
      refine ⟨5362282722998589349084631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3574855148665726232723087 5362282722998589349084631)
      ·
        refine ⟨8043424084497884023626947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5362282722998589349084631 8043424084497884023626947)
        ·
          refine ⟨12065136126746826035440421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8043424084497884023626947 12065136126746826035440421)
          ·
            refine ⟨2262213023765029881645079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12065136126746826035440421 2262213023765029881645079)
            ·
              refine ⟨3393319535647544822467619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262213023765029881645079 3393319535647544822467619)
              ·
                refine ⟨5089979303471317233701429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393319535647544822467619 5089979303471317233701429)
                ·
                  refine ⟨477185559700435990659509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5089979303471317233701429 477185559700435990659509)
                  ·
                    refine ⟨44736146221915874124329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 477185559700435990659509 44736146221915874124329)
                    ·
                      rfl

theorem cell23_261370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_261370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261370 prefixEnd_261370 := by exact prefixLift 261370
  have htrace : WordTrace (prefixWord ++ tailWord_261370) baseStart_261370 baseEnd_261370 := by
    simpa [prefixWord, tailWord_261370, baseEnd_261370] using wordTrace_append hprefix tailTrace_261370
  have hstable : (prefixWord ++ tailWord_261370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261370).length < 2 ^ (prefixWord ++ tailWord_261370).sum := by decide
  have hdescent : baseEnd_261370 < baseStart_261370 := by decide
  rcases family_descends (prefixWord ++ tailWord_261370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261404 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 1, 5]
def baseStart_261404 : Nat := 118140960795 + 261404 * 2 ^ 59
def prefixEnd_261404 : Nat := 4983230072969 + 3 ^ 40 * 261404 * 2
def baseEnd_261404 : Nat := 44741965669333496449277

theorem tailTrace_261404 : CollatzResearch.WordTrace tailWord_261404 prefixEnd_261404 44741965669333496449277 := by
  unfold tailWord_261404
  simp only [CollatzResearch.WordTrace]
  refine ⟨4767093572492713546999633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6356124763323618062666177 4767093572492713546999633)
  ·
    refine ⟨3575320179369535160249725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4767093572492713546999633 3575320179369535160249725)
    ·
      refine ⟨1340745067263575685093647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3575320179369535160249725 1340745067263575685093647)
      ·
        refine ⟨2011117600895363527640471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340745067263575685093647 2011117600895363527640471)
        ·
          refine ⟨3016676401343045291460707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011117600895363527640471 3016676401343045291460707)
          ·
            refine ⟨4525014602014567937191061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016676401343045291460707 4525014602014567937191061)
            ·
              refine ⟨212110059469432872055831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4525014602014567937191061 212110059469432872055831)
              ·
                refine ⟨318165089204149308083747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212110059469432872055831 318165089204149308083747)
                ·
                  refine ⟨477247633806223962125621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318165089204149308083747 477247633806223962125621)
                  ·
                    refine ⟨44741965669333496449277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 477247633806223962125621 44741965669333496449277)
                    ·
                      rfl

theorem cell23_261404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_261404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261404 prefixEnd_261404 := by exact prefixLift 261404
  have htrace : WordTrace (prefixWord ++ tailWord_261404) baseStart_261404 baseEnd_261404 := by
    simpa [prefixWord, tailWord_261404, baseEnd_261404] using wordTrace_append hprefix tailTrace_261404
  have hstable : (prefixWord ++ tailWord_261404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261404).length < 2 ^ (prefixWord ++ tailWord_261404).sum := by decide
  have hdescent : baseEnd_261404 < baseStart_261404 := by decide
  rcases family_descends (prefixWord ++ tailWord_261404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261418 : List Nat := [3, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_261418 : Nat := 118140960795 + 261418 * 2 ^ 59
def prefixEnd_261418 : Nat := 4983230072969 + 3 ^ 40 * 261418 * 2
def baseEnd_261418 : Nat := 134233085737163434572767

theorem tailTrace_261418 : CollatzResearch.WordTrace tailWord_261418 prefixEnd_261418 134233085737163434572767 := by
  unfold tailWord_261418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383674441733676871252227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6356465177956471656672605 2383674441733676871252227)
  ·
    refine ⟨3575511662600515306878341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2383674441733676871252227 3575511662600515306878341)
    ·
      refine ⟨670408436737596620039689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3575511662600515306878341 670408436737596620039689)
      ·
        refine ⟨502806327553197465029767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670408436737596620039689 502806327553197465029767)
        ·
          refine ⟨754209491329796197544651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502806327553197465029767 754209491329796197544651)
          ·
            refine ⟨1131314236994694296316977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754209491329796197544651 1131314236994694296316977)
            ·
              refine ⟨848485677746020722237733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131314236994694296316977 848485677746020722237733)
              ·
                refine ⟨159091064577378885419575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 848485677746020722237733 159091064577378885419575)
                ·
                  refine ⟨238636596866068328129363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159091064577378885419575 238636596866068328129363)
                  ·
                    refine ⟨357954895299102492194045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238636596866068328129363 357954895299102492194045)
                    ·
                      refine ⟨134233085737163434572767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 357954895299102492194045 134233085737163434572767)
                      ·
                        rfl

theorem cell23_261418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_261418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261418 prefixEnd_261418 := by exact prefixLift 261418
  have htrace : WordTrace (prefixWord ++ tailWord_261418) baseStart_261418 baseEnd_261418 := by
    simpa [prefixWord, tailWord_261418, baseEnd_261418] using wordTrace_append hprefix tailTrace_261418
  have hstable : (prefixWord ++ tailWord_261418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261418).length < 2 ^ (prefixWord ++ tailWord_261418).sum := by decide
  have hdescent : baseEnd_261418 < baseStart_261418 := by decide
  rcases family_descends (prefixWord ++ tailWord_261418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261420 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_261420 : Nat := 118140960795 + 261420 * 2 ^ 59
def prefixEnd_261420 : Nat := 4983230072969 + 3 ^ 40 * 261420 * 2
def baseEnd_261420 : Nat := 134234112698472426747757

theorem tailTrace_261420 : CollatzResearch.WordTrace tailWord_261420 prefixEnd_261420 134234112698472426747757 := by
  unfold tailWord_261420
  simp only [CollatzResearch.WordTrace]
  refine ⟨4767385356463730913290857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6356513808618307884387809 4767385356463730913290857)
  ·
    refine ⟨3575539017347798184968143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4767385356463730913290857 3575539017347798184968143)
    ·
      refine ⟨5363308526021697277452215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3575539017347798184968143 5363308526021697277452215)
      ·
        refine ⟨8044962789032545916178323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5363308526021697277452215 8044962789032545916178323)
        ·
          refine ⟨12067444183548818874267485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044962789032545916178323 12067444183548818874267485)
          ·
            refine ⟨4525291568830807077850307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12067444183548818874267485 4525291568830807077850307)
            ·
              refine ⟨6787937353246210616775461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525291568830807077850307 6787937353246210616775461)
              ·
                refine ⟨1272738253733664490645399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6787937353246210616775461 1272738253733664490645399)
                ·
                  refine ⟨1909107380600496735968099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1272738253733664490645399 1909107380600496735968099)
                  ·
                    refine ⟨2863661070900745103952149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1909107380600496735968099 2863661070900745103952149)
                    ·
                      refine ⟨134234112698472426747757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2863661070900745103952149 134234112698472426747757)
                      ·
                        rfl

theorem cell23_261420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_261420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261420 prefixEnd_261420 := by exact prefixLift 261420
  have htrace : WordTrace (prefixWord ++ tailWord_261420) baseStart_261420 baseEnd_261420 := by
    simpa [prefixWord, tailWord_261420, baseEnd_261420] using wordTrace_append hprefix tailTrace_261420
  have hstable : (prefixWord ++ tailWord_261420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261420).length < 2 ^ (prefixWord ++ tailWord_261420).sum := by decide
  have hdescent : baseEnd_261420 < baseStart_261420 := by decide
  rcases family_descends (prefixWord ++ tailWord_261420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261427 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 5]
def baseStart_261427 : Nat := 118140960795 + 261427 * 2 ^ 59
def prefixEnd_261427 : Nat := 4983230072969 + 3 ^ 40 * 261427 * 2
def baseEnd_261427 : Nat := 134237707063053899360225

theorem tailTrace_261427 : CollatzResearch.WordTrace tailWord_261427 prefixEnd_261427 134237707063053899360225 := by
  unfold tailWord_261427
  simp only [CollatzResearch.WordTrace]
  refine ⟨9535026023902102022086535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6356684015934734681391023 9535026023902102022086535)
  ·
    refine ⟨14302539035853153033129803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9535026023902102022086535 14302539035853153033129803)
    ·
      refine ⟨21453808553779729549694705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14302539035853153033129803 21453808553779729549694705)
      ·
        refine ⟨16090356415334797162271029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21453808553779729549694705 16090356415334797162271029)
        ·
          refine ⟨1508470913937637233962909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16090356415334797162271029 1508470913937637233962909)
          ·
            refine ⟨565676592726613962736091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1508470913937637233962909 565676592726613962736091)
            ·
              refine ⟨848514889089920944104137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565676592726613962736091 848514889089920944104137)
              ·
                refine ⟨636386166817440708078103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848514889089920944104137 636386166817440708078103)
                ·
                  refine ⟨954579250226161062117155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 636386166817440708078103 954579250226161062117155)
                  ·
                    refine ⟨1431868875339241593175733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 954579250226161062117155 1431868875339241593175733)
                    ·
                      refine ⟨134237707063053899360225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1431868875339241593175733 134237707063053899360225)
                      ·
                        rfl

theorem cell23_261427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_261427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261427 prefixEnd_261427 := by exact prefixLift 261427
  have htrace : WordTrace (prefixWord ++ tailWord_261427) baseStart_261427 baseEnd_261427 := by
    simpa [prefixWord, tailWord_261427, baseEnd_261427] using wordTrace_append hprefix tailTrace_261427
  have hstable : (prefixWord ++ tailWord_261427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261427).length < 2 ^ (prefixWord ++ tailWord_261427).sum := by decide
  have hdescent : baseEnd_261427 < baseStart_261427 := by decide
  rcases family_descends (prefixWord ++ tailWord_261427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261441 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_261441 : Nat := 118140960795 + 261441 * 2 ^ 59
def prefixEnd_261441 : Nat := 4983230072969 + 3 ^ 40 * 261441 * 2
def baseEnd_261441 : Nat := 134244895792216844585161

theorem tailTrace_261441 : CollatzResearch.WordTrace tailWord_261441 prefixEnd_261441 134244895792216844585161 := by
  unfold tailWord_261441
  simp only [CollatzResearch.WordTrace]
  refine ⟨9535536645851382413096177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6357024430567588275397451 9535536645851382413096177)
  ·
    refine ⟨7151652484388536809822133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9535536645851382413096177 7151652484388536809822133)
    ·
      refine ⟨670467420411425325920825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7151652484388536809822133 670467420411425325920825)
      ·
        refine ⟨502850565308568994440619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670467420411425325920825 502850565308568994440619)
        ·
          refine ⟨754275847962853491660929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502850565308568994440619 754275847962853491660929)
          ·
            refine ⟨565706885972140118745697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754275847962853491660929 565706885972140118745697)
            ·
              refine ⟨424280164479105089059273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565706885972140118745697 424280164479105089059273)
              ·
                refine ⟨318210123359328816794455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424280164479105089059273 318210123359328816794455)
                ·
                  refine ⟨477315185038993225191683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318210123359328816794455 477315185038993225191683)
                  ·
                    refine ⟨715972777558489837787525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 477315185038993225191683 715972777558489837787525)
                    ·
                      refine ⟨134244895792216844585161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 715972777558489837787525 134244895792216844585161)
                      ·
                        rfl

theorem cell23_261441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_261441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261441 prefixEnd_261441 := by exact prefixLift 261441
  have htrace : WordTrace (prefixWord ++ tailWord_261441) baseStart_261441 baseEnd_261441 := by
    simpa [prefixWord, tailWord_261441, baseEnd_261441] using wordTrace_append hprefix tailTrace_261441
  have hstable : (prefixWord ++ tailWord_261441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261441).length < 2 ^ (prefixWord ++ tailWord_261441).sum := by decide
  have hdescent : baseEnd_261441 < baseStart_261441 := by decide
  rcases family_descends (prefixWord ++ tailWord_261441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261447 : List Nat := [1, 1, 4, 1, 2, 3, 4, 7]
def baseStart_261447 : Nat := 118140960795 + 261447 * 2 ^ 59
def prefixEnd_261447 : Nat := 4983230072969 + 3 ^ 40 * 261447 * 2
def baseEnd_261447 : Nat := 4972147284301623004079

theorem tailTrace_261447 : CollatzResearch.WordTrace tailWord_261447 prefixEnd_261447 4972147284301623004079 := by
  unfold tailWord_261447
  simp only [CollatzResearch.WordTrace]
  refine ⟨9535755483829645437814595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6357170322553096958543063 9535755483829645437814595)
  ·
    refine ⟨14303633225744468156721893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9535755483829645437814595 14303633225744468156721893)
    ·
      refine ⟨2681931229827087779385355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14303633225744468156721893 2681931229827087779385355)
      ·
        refine ⟨4022896844740631669078033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681931229827087779385355 4022896844740631669078033)
        ·
          refine ⟨3017172633555473751808525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4022896844740631669078033 3017172633555473751808525)
          ·
            refine ⟨1131439737583302656928197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3017172633555473751808525 1131439737583302656928197)
            ·
              refine ⟨212144950796869248174037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1131439737583302656928197 212144950796869248174037)
              ·
                refine ⟨4972147284301623004079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212144950796869248174037 4972147284301623004079)
                ·
                  rfl

theorem cell23_261447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 7].length) (baseStart_261447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261447 prefixEnd_261447 := by exact prefixLift 261447
  have htrace : WordTrace (prefixWord ++ tailWord_261447) baseStart_261447 baseEnd_261447 := by
    simpa [prefixWord, tailWord_261447, baseEnd_261447] using wordTrace_append hprefix tailTrace_261447
  have hstable : (prefixWord ++ tailWord_261447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261447).length < 2 ^ (prefixWord ++ tailWord_261447).sum := by decide
  have hdescent : baseEnd_261447 < baseStart_261447 := by decide
  rcases family_descends (prefixWord ++ tailWord_261447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261450 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_261450 : Nat := 118140960795 + 261450 * 2 ^ 59
def prefixEnd_261450 : Nat := 4983230072969 + 3 ^ 40 * 261450 * 2
def baseEnd_261450 : Nat := 134249517118107309372619

theorem tailTrace_261450 : CollatzResearch.WordTrace tailWord_261450 prefixEnd_261450 134249517118107309372619 := by
  unfold tailWord_261450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383966225704694237543451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6357243268545851300115869 2383966225704694237543451)
  ·
    refine ⟨3575949338557041356315177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2383966225704694237543451 3575949338557041356315177)
    ·
      refine ⟨2681962003917781017236383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3575949338557041356315177 2681962003917781017236383)
      ·
        refine ⟨4022943005876671525854575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681962003917781017236383 4022943005876671525854575)
        ·
          refine ⟨6034414508815007288781863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022943005876671525854575 6034414508815007288781863)
          ·
            refine ⟨9051621763222510933172795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034414508815007288781863 9051621763222510933172795)
            ·
              refine ⟨13577432644833766399759193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9051621763222510933172795 13577432644833766399759193)
              ·
                refine ⟨10183074483625324799819395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13577432644833766399759193 10183074483625324799819395)
                ·
                  refine ⟨15274611725437987199729093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10183074483625324799819395 15274611725437987199729093)
                  ·
                    refine ⟨2863989698519622599949205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15274611725437987199729093 2863989698519622599949205)
                    ·
                      refine ⟨134249517118107309372619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2863989698519622599949205 134249517118107309372619)
                      ·
                        rfl

theorem cell23_261450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_261450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261450 prefixEnd_261450 := by exact prefixLift 261450
  have htrace : WordTrace (prefixWord ++ tailWord_261450) baseStart_261450 baseEnd_261450 := by
    simpa [prefixWord, tailWord_261450, baseEnd_261450] using wordTrace_append hprefix tailTrace_261450
  have hstable : (prefixWord ++ tailWord_261450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261450).length < 2 ^ (prefixWord ++ tailWord_261450).sum := by decide
  have hdescent : baseEnd_261450 < baseStart_261450 := by decide
  rcases family_descends (prefixWord ++ tailWord_261450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261457 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 3, 3, 3]
def baseStart_261457 : Nat := 118140960795 + 261457 * 2 ^ 59
def prefixEnd_261457 : Nat := 4983230072969 + 3 ^ 40 * 261457 * 2
def baseEnd_261457 : Nat := 134253111482688781985087

theorem tailTrace_261457 : CollatzResearch.WordTrace tailWord_261457 prefixEnd_261457 134253111482688781985087 := by
  unfold tailWord_261457
  simp only [CollatzResearch.WordTrace]
  refine ⟨9536120213793417145678625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6357413475862278097119083 9536120213793417145678625)
  ·
    refine ⟨7152090160345062859258969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9536120213793417145678625 7152090160345062859258969)
    ·
      refine ⟨5364067620258797144444227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7152090160345062859258969 5364067620258797144444227)
      ·
        refine ⟨8046101430388195716666341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5364067620258797144444227 8046101430388195716666341)
        ·
          refine ⟨1508644018197786696874939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8046101430388195716666341 1508644018197786696874939)
          ·
            refine ⟨2262966027296680045312409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508644018197786696874939 2262966027296680045312409)
            ·
              refine ⟨1697224520472510033984307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2262966027296680045312409 1697224520472510033984307)
              ·
                refine ⟨2545836780708765050976461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697224520472510033984307 2545836780708765050976461)
                ·
                  refine ⟨954688792765786894116173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2545836780708765050976461 954688792765786894116173)
                  ·
                    refine ⟨358008297287170085293565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 954688792765786894116173 358008297287170085293565)
                    ·
                      refine ⟨134253111482688781985087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 358008297287170085293565 134253111482688781985087)
                      ·
                        rfl

theorem cell23_261457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_261457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261457 prefixEnd_261457 := by exact prefixLift 261457
  have htrace : WordTrace (prefixWord ++ tailWord_261457) baseStart_261457 baseEnd_261457 := by
    simpa [prefixWord, tailWord_261457, baseEnd_261457] using wordTrace_append hprefix tailTrace_261457
  have hstable : (prefixWord ++ tailWord_261457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261457).length < 2 ^ (prefixWord ++ tailWord_261457).sum := by decide
  have hdescent : baseEnd_261457 < baseStart_261457 := by decide
  rcases family_descends (prefixWord ++ tailWord_261457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261462 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_261462 : Nat := 118140960795 + 261462 * 2 ^ 59
def prefixEnd_261462 : Nat := 4983230072969 + 3 ^ 40 * 261462 * 2
def baseEnd_261462 : Nat := 134255678885961262422565

theorem tailTrace_261462 : CollatzResearch.WordTrace tailWord_261462 prefixEnd_261462 134255678885961262422565 := by
  unfold tailWord_261462
  simp only [CollatzResearch.WordTrace]
  refine ⟨596018911173456437475665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6357535052516868666407093 596018911173456437475665)
  ·
    refine ⟨447014183380092328106749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 596018911173456437475665 447014183380092328106749)
    ·
      refine ⟨167630318767534623040031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447014183380092328106749 167630318767534623040031)
      ·
        refine ⟨251445478151301934560047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167630318767534623040031 251445478151301934560047)
        ·
          refine ⟨377168217226952901840071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251445478151301934560047 377168217226952901840071)
          ·
            refine ⟨565752325840429352760107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377168217226952901840071 565752325840429352760107)
            ·
              refine ⟨848628488760644029140161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565752325840429352760107 848628488760644029140161)
              ·
                refine ⟨636471366570483021855121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848628488760644029140161 636471366570483021855121)
                ·
                  refine ⟨477353524927862266391341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 636471366570483021855121 477353524927862266391341)
                  ·
                    refine ⟨179007571847948349896753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 477353524927862266391341 179007571847948349896753)
                    ·
                      refine ⟨134255678885961262422565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179007571847948349896753 134255678885961262422565)
                      ·
                        rfl

theorem cell23_261462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_261462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261462 prefixEnd_261462 := by exact prefixLift 261462
  have htrace : WordTrace (prefixWord ++ tailWord_261462) baseStart_261462 baseEnd_261462 := by
    simpa [prefixWord, tailWord_261462, baseEnd_261462] using wordTrace_append hprefix tailTrace_261462
  have hstable : (prefixWord ++ tailWord_261462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261462).length < 2 ^ (prefixWord ++ tailWord_261462).sum := by decide
  have hdescent : baseEnd_261462 < baseStart_261462 := by decide
  rcases family_descends (prefixWord ++ tailWord_261462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261469 : List Nat := [1, 4, 5, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_261469 : Nat := 118140960795 + 261469 * 2 ^ 59
def prefixEnd_261469 : Nat := 4983230072969 + 3 ^ 40 * 261469 * 2
def baseEnd_261469 : Nat := 134259273250542735035033

theorem tailTrace_261469 : CollatzResearch.WordTrace tailWord_261469 prefixEnd_261469 134259273250542735035033 := by
  unfold tailWord_261469
  simp only [CollatzResearch.WordTrace]
  refine ⟨9536557889749943195115461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6357705259833295463410307 9536557889749943195115461)
  ·
    refine ⟨1788104604328114349084149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9536557889749943195115461 1788104604328114349084149)
    ·
      refine ⟨167634806655760720226639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1788104604328114349084149 167634806655760720226639)
      ·
        refine ⟨251452209983641080339959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167634806655760720226639 251452209983641080339959)
        ·
          refine ⟨377178314975461620509939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251452209983641080339959 377178314975461620509939)
          ·
            refine ⟨565767472463192430764909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377178314975461620509939 565767472463192430764909)
            ·
              refine ⟨212162802173697161536841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565767472463192430764909 212162802173697161536841)
              ·
                refine ⟨159122101630272871152631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212162802173697161536841 159122101630272871152631)
                ·
                  refine ⟨238683152445409306728947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159122101630272871152631 238683152445409306728947)
                  ·
                    refine ⟨358024728668113960093421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238683152445409306728947 358024728668113960093421)
                    ·
                      refine ⟨134259273250542735035033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 358024728668113960093421 134259273250542735035033)
                      ·
                        rfl

theorem cell23_261469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_261469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261469 prefixEnd_261469 := by exact prefixLift 261469
  have htrace : WordTrace (prefixWord ++ tailWord_261469) baseStart_261469 baseEnd_261469 := by
    simpa [prefixWord, tailWord_261469, baseEnd_261469] using wordTrace_append hprefix tailTrace_261469
  have hstable : (prefixWord ++ tailWord_261469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261469).length < 2 ^ (prefixWord ++ tailWord_261469).sum := by decide
  have hdescent : baseEnd_261469 < baseStart_261469 := by decide
  rcases family_descends (prefixWord ++ tailWord_261469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261475 : List Nat := [1, 1, 1, 5, 2, 3, 3, 2, 1, 2, 2]
def baseStart_261475 : Nat := 118140960795 + 261475 * 2 ^ 59
def prefixEnd_261475 : Nat := 4983230072969 + 3 ^ 40 * 261475 * 2
def baseEnd_261475 : Nat := 134262354134469711560005

theorem tailTrace_261475 : CollatzResearch.WordTrace tailWord_261475 prefixEnd_261475 134262354134469711560005 := by
  unfold tailWord_261475
  simp only [CollatzResearch.WordTrace]
  refine ⟨9536776727728206219833879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6357851151818804146555919 9536776727728206219833879)
  ·
    refine ⟨14305165091592309329750819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9536776727728206219833879 14305165091592309329750819)
    ·
      refine ⟨21457747637388463994626229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14305165091592309329750819 21457747637388463994626229)
      ·
        refine ⟨2011663841005168499496209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21457747637388463994626229 2011663841005168499496209)
        ·
          refine ⟨1508747880753876374622157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2011663841005168499496209 1508747880753876374622157)
          ·
            refine ⟨565780455282703640483309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1508747880753876374622157 565780455282703640483309)
            ·
              refine ⟨212167670731013865181241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565780455282703640483309 212167670731013865181241)
              ·
                refine ⟨159125753048260398885931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212167670731013865181241 159125753048260398885931)
                ·
                  refine ⟨238688629572390598328897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159125753048260398885931 238688629572390598328897)
                  ·
                    refine ⟨179016472179292948746673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 238688629572390598328897 179016472179292948746673)
                    ·
                      refine ⟨134262354134469711560005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179016472179292948746673 134262354134469711560005)
                      ·
                        rfl

theorem cell23_261475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_261475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261475 prefixEnd_261475 := by exact prefixLift 261475
  have htrace : WordTrace (prefixWord ++ tailWord_261475) baseStart_261475 baseEnd_261475 := by
    simpa [prefixWord, tailWord_261475, baseEnd_261475] using wordTrace_append hprefix tailTrace_261475
  have hstable : (prefixWord ++ tailWord_261475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261475).length < 2 ^ (prefixWord ++ tailWord_261475).sum := by decide
  have hdescent : baseEnd_261475 < baseStart_261475 := by decide
  rcases family_descends (prefixWord ++ tailWord_261475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261527 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_261527 : Nat := 118140960795 + 261527 * 2 ^ 59
def prefixEnd_261527 : Nat := 4983230072969 + 3 ^ 40 * 261527 * 2
def baseEnd_261527 : Nat := 134289055128503508109765

theorem tailTrace_261527 : CollatzResearch.WordTrace tailWord_261527 prefixEnd_261527 134289055128503508109765 := by
  unfold tailWord_261527
  simp only [CollatzResearch.WordTrace]
  refine ⟨9538673323539819100726835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6359115549026546067151223 9538673323539819100726835)
  ·
    refine ⟨14308009985309728651090253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9538673323539819100726835 14308009985309728651090253)
    ·
      refine ⟨5365503744491148244158845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14308009985309728651090253 5365503744491148244158845)
      ·
        refine ⟨2012063904184180591559567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5365503744491148244158845 2012063904184180591559567)
        ·
          refine ⟨3018095856276270887339351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2012063904184180591559567 3018095856276270887339351)
          ·
            refine ⟨4527143784414406331009027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018095856276270887339351 4527143784414406331009027)
            ·
              refine ⟨6790715676621609496513541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527143784414406331009027 6790715676621609496513541)
              ·
                refine ⟨1273259189366551780596289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6790715676621609496513541 1273259189366551780596289)
                ·
                  refine ⟨954944392024913835447217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1273259189366551780596289 954944392024913835447217)
                  ·
                    refine ⟨716208294018685376585413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 954944392024913835447217 716208294018685376585413)
                    ·
                      refine ⟨134289055128503508109765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 716208294018685376585413 134289055128503508109765)
                      ·
                        rfl

theorem cell23_261527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_261527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261527 prefixEnd_261527 := by exact prefixLift 261527
  have htrace : WordTrace (prefixWord ++ tailWord_261527) baseStart_261527 baseEnd_261527 := by
    simpa [prefixWord, tailWord_261527, baseEnd_261527] using wordTrace_append hprefix tailTrace_261527
  have hstable : (prefixWord ++ tailWord_261527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261527).length < 2 ^ (prefixWord ++ tailWord_261527).sum := by decide
  have hdescent : baseEnd_261527 < baseStart_261527 := by decide
  rcases family_descends (prefixWord ++ tailWord_261527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261621 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_261621 : Nat := 118140960795 + 261621 * 2 ^ 59
def prefixEnd_261621 : Nat := 4983230072969 + 3 ^ 40 * 261621 * 2
def baseEnd_261621 : Nat := 134337322310026140334333

theorem tailTrace_261621 : CollatzResearch.WordTrace tailWord_261621 prefixEnd_261621 134337322310026140334333 := by
  unfold tailWord_261621
  simp only [CollatzResearch.WordTrace]
  refine ⟨9542101785199273154648717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6361401190132848769765811 9542101785199273154648717)
  ·
    refine ⟨3578288169449727432993269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9542101785199273154648717 3578288169449727432993269)
    ·
      refine ⟨335464515885911946843119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3578288169449727432993269 335464515885911946843119)
      ·
        refine ⟨503196773828867920264679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335464515885911946843119 503196773828867920264679)
        ·
          refine ⟨754795160743301880397019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503196773828867920264679 754795160743301880397019)
          ·
            refine ⟨1132192741114952820595529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754795160743301880397019 1132192741114952820595529)
            ·
              refine ⟨849144555836214615446647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132192741114952820595529 849144555836214615446647)
              ·
                refine ⟨1273716833754321923169971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849144555836214615446647 1273716833754321923169971)
                ·
                  refine ⟨1910575250631482884754957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273716833754321923169971 1910575250631482884754957)
                  ·
                    refine ⟨716465718986806081783109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1910575250631482884754957 716465718986806081783109)
                    ·
                      refine ⟨134337322310026140334333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 716465718986806081783109 134337322310026140334333)
                      ·
                        rfl

theorem cell23_261621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_261621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261621 prefixEnd_261621 := by exact prefixLift 261621
  have htrace : WordTrace (prefixWord ++ tailWord_261621) baseStart_261621 baseEnd_261621 := by
    simpa [prefixWord, tailWord_261621, baseEnd_261621] using wordTrace_append hprefix tailTrace_261621
  have hstable : (prefixWord ++ tailWord_261621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261621).length < 2 ^ (prefixWord ++ tailWord_261621).sum := by decide
  have hdescent : baseEnd_261621 < baseStart_261621 := by decide
  rcases family_descends (prefixWord ++ tailWord_261621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261624 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 1, 4, 3]
def baseStart_261624 : Nat := 118140960795 + 261624 * 2 ^ 59
def prefixEnd_261624 : Nat := 4983230072969 + 3 ^ 40 * 261624 * 2
def baseEnd_261624 : Nat := 134338862751989628596819

theorem tailTrace_261624 : CollatzResearch.WordTrace tailWord_261624 prefixEnd_261624 134338862751989628596819 := by
  unfold tailWord_261624
  simp only [CollatzResearch.WordTrace]
  refine ⟨4771105602094202333503963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6361474136125603111338617 4771105602094202333503963)
  ·
    refine ⟨7156658403141303500255945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4771105602094202333503963 7156658403141303500255945)
    ·
      refine ⟨5367493802355977625191959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7156658403141303500255945 5367493802355977625191959)
      ·
        refine ⟨8051240703533966437787939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5367493802355977625191959 8051240703533966437787939)
        ·
          refine ⟨12076861055300949656681909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8051240703533966437787939 12076861055300949656681909)
          ·
            refine ⟨1132205723934464030313929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12076861055300949656681909 1132205723934464030313929)
            ·
              refine ⟨849154292950848022735447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132205723934464030313929 849154292950848022735447)
              ·
                refine ⟨1273731439426272034103171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849154292950848022735447 1273731439426272034103171)
                ·
                  refine ⟨1910597159139408051154757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1273731439426272034103171 1910597159139408051154757)
                  ·
                    refine ⟨358236967338639009591517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1910597159139408051154757 358236967338639009591517)
                    ·
                      refine ⟨134338862751989628596819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 358236967338639009591517 134338862751989628596819)
                      ·
                        rfl

theorem cell23_261624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_261624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261624 prefixEnd_261624 := by exact prefixLift 261624
  have htrace : WordTrace (prefixWord ++ tailWord_261624) baseStart_261624 baseEnd_261624 := by
    simpa [prefixWord, tailWord_261624, baseEnd_261624] using wordTrace_append hprefix tailTrace_261624
  have hstable : (prefixWord ++ tailWord_261624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261624).length < 2 ^ (prefixWord ++ tailWord_261624).sum := by decide
  have hdescent : baseEnd_261624 < baseStart_261624 := by decide
  rcases family_descends (prefixWord ++ tailWord_261624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261631 : List Nat := [1, 1, 2, 2, 1, 2, 2, 7, 1, 4]
def baseStart_261631 : Nat := 118140960795 + 261631 * 2 ^ 59
def prefixEnd_261631 : Nat := 4983230072969 + 3 ^ 40 * 261631 * 2
def baseEnd_261631 : Nat := 44780819038857033736429

theorem tailTrace_261631 : CollatzResearch.WordTrace tailWord_261631 prefixEnd_261631 44780819038857033736429 := by
  unfold tailWord_261631
  simp only [CollatzResearch.WordTrace]
  refine ⟨9542466515163044862512747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6361644343442029908341831 9542466515163044862512747)
  ·
    refine ⟨14313699772744567293769121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9542466515163044862512747 14313699772744567293769121)
    ·
      refine ⟨10735274829558425470326841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14313699772744567293769121 10735274829558425470326841)
      ·
        refine ⟨8051456122168819102745131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10735274829558425470326841 8051456122168819102745131)
        ·
          refine ⟨12077184183253228654117697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8051456122168819102745131 12077184183253228654117697)
          ·
            refine ⟨9057888137439921490588273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12077184183253228654117697 9057888137439921490588273)
            ·
              refine ⟨6793416103079941117941205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9057888137439921490588273 6793416103079941117941205)
              ·
                refine ⟨159220689915936119951747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6793416103079941117941205 159220689915936119951747)
                ·
                  refine ⟨238831034873904179927621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159220689915936119951747 238831034873904179927621)
                  ·
                    refine ⟨44780819038857033736429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238831034873904179927621 44780819038857033736429)
                    ·
                      rfl

theorem cell23_261631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 1, 4].length) (baseStart_261631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261631 prefixEnd_261631 := by exact prefixLift 261631
  have htrace : WordTrace (prefixWord ++ tailWord_261631) baseStart_261631 baseEnd_261631 := by
    simpa [prefixWord, tailWord_261631, baseEnd_261631] using wordTrace_append hprefix tailTrace_261631
  have hstable : (prefixWord ++ tailWord_261631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261631).length < 2 ^ (prefixWord ++ tailWord_261631).sum := by decide
  have hdescent : baseEnd_261631 < baseStart_261631 := by decide
  rcases family_descends (prefixWord ++ tailWord_261631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261731 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 3]
def baseStart_261731 : Nat := 118140960795 + 261731 * 2 ^ 59
def prefixEnd_261731 : Nat := 4983230072969 + 3 ^ 40 * 261731 * 2
def baseEnd_261731 : Nat := 134393805182020709958827

theorem tailTrace_261731 : CollatzResearch.WordTrace tailWord_261731 prefixEnd_261731 134393805182020709958827 := by
  unfold tailWord_261731
  simp only [CollatzResearch.WordTrace]
  refine ⟨9546113814800761941153047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6364075876533841294102031 9546113814800761941153047)
  ·
    refine ⟨14319170722201142911729571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9546113814800761941153047 14319170722201142911729571)
    ·
      refine ⟨21478756083301714367594357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14319170722201142911729571 21478756083301714367594357)
      ·
        refine ⟨2013633382809535721961971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21478756083301714367594357 2013633382809535721961971)
        ·
          refine ⟨3020450074214303582942957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013633382809535721961971 3020450074214303582942957)
          ·
            refine ⟨1132668777830363843603609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3020450074214303582942957 1132668777830363843603609)
            ·
              refine ⟨849501583372772882702707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132668777830363843603609 849501583372772882702707)
              ·
                refine ⟨1274252375059159324054061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849501583372772882702707 1274252375059159324054061)
                ·
                  refine ⟨477844640647184746520273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1274252375059159324054061 477844640647184746520273)
                  ·
                    refine ⟨358383480485388559890205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 477844640647184746520273 358383480485388559890205)
                    ·
                      refine ⟨134393805182020709958827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 358383480485388559890205 134393805182020709958827)
                      ·
                        rfl

theorem cell23_261731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_261731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261731 prefixEnd_261731 := by exact prefixLift 261731
  have htrace : WordTrace (prefixWord ++ tailWord_261731) baseStart_261731 baseEnd_261731 := by
    simpa [prefixWord, tailWord_261731, baseEnd_261731] using wordTrace_append hprefix tailTrace_261731
  have hstable : (prefixWord ++ tailWord_261731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261731).length < 2 ^ (prefixWord ++ tailWord_261731).sum := by decide
  have hdescent : baseEnd_261731 < baseStart_261731 := by decide
  rcases family_descends (prefixWord ++ tailWord_261731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261742 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_261742 : Nat := 118140960795 + 261742 * 2 ^ 59
def prefixEnd_261742 : Nat := 4983230072969 + 3 ^ 40 * 261742 * 2
def baseEnd_261742 : Nat := 44799817823073388973759

theorem tailTrace_261742 : CollatzResearch.WordTrace tailWord_261742 prefixEnd_261742 44799817823073388973759 := by
  unfold tailWord_261742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193314377220113852475435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6364343345173940546535653 1193314377220113852475435)
  ·
    refine ⟨1789971565830170778713153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1193314377220113852475435 1789971565830170778713153)
    ·
      refine ⟨1342478674372628084034865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1789971565830170778713153 1342478674372628084034865)
      ·
        refine ⟨1006859005779471063026149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1342478674372628084034865 1006859005779471063026149)
        ·
          refine ⟨188786063583650824317403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1006859005779471063026149 188786063583650824317403)
          ·
            refine ⟨283179095375476236476105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188786063583650824317403 283179095375476236476105)
            ·
              refine ⟨212384321531607177357079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283179095375476236476105 212384321531607177357079)
              ·
                refine ⟨318576482297410766035619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212384321531607177357079 318576482297410766035619)
                ·
                  refine ⟨477864723446116149053429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318576482297410766035619 477864723446116149053429)
                  ·
                    refine ⟨44799817823073388973759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 477864723446116149053429 44799817823073388973759)
                    ·
                      rfl

theorem cell23_261742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_261742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261742 prefixEnd_261742 := by exact prefixLift 261742
  have htrace : WordTrace (prefixWord ++ tailWord_261742) baseStart_261742 baseEnd_261742 := by
    simpa [prefixWord, tailWord_261742, baseEnd_261742] using wordTrace_append hprefix tailTrace_261742
  have hstable : (prefixWord ++ tailWord_261742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261742).length < 2 ^ (prefixWord ++ tailWord_261742).sum := by decide
  have hdescent : baseEnd_261742 < baseStart_261742 := by decide
  rcases family_descends (prefixWord ++ tailWord_261742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261805 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_261805 : Nat := 118140960795 + 261805 * 2 ^ 59
def prefixEnd_261805 : Nat := 4983230072969 + 3 ^ 40 * 261805 * 2
def baseEnd_261805 : Nat := 134431802750453420433487

theorem tailTrace_261805 : CollatzResearch.WordTrace tailWord_261805 prefixEnd_261805 134431802750453420433487 := by
  unfold tailWord_261805
  simp only [CollatzResearch.WordTrace]
  refine ⟨9548812816532672579346869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6365875211021781719564579 9548812816532672579346869)
  ·
    refine ⟨895201201549938054313769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9548812816532672579346869 895201201549938054313769)
    ·
      refine ⟨671400901162453540735327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 895201201549938054313769 671400901162453540735327)
      ·
        refine ⟨1007101351743680311102991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671400901162453540735327 1007101351743680311102991)
        ·
          refine ⟨1510652027615520466654487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007101351743680311102991 1510652027615520466654487)
          ·
            refine ⟨2265978041423280699981731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510652027615520466654487 2265978041423280699981731)
            ·
              refine ⟨3398967062134921049972597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2265978041423280699981731 3398967062134921049972597)
              ·
                refine ⟨318653162075148848434931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3398967062134921049972597 318653162075148848434931)
                ·
                  refine ⟨477979743112723272652397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318653162075148848434931 477979743112723272652397)
                  ·
                    refine ⟨179242403667271227244649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 477979743112723272652397 179242403667271227244649)
                    ·
                      refine ⟨134431802750453420433487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179242403667271227244649 134431802750453420433487)
                      ·
                        rfl

theorem cell23_261805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_261805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261805 prefixEnd_261805 := by exact prefixLift 261805
  have htrace : WordTrace (prefixWord ++ tailWord_261805) baseStart_261805 baseEnd_261805 := by
    simpa [prefixWord, tailWord_261805, baseEnd_261805] using wordTrace_append hprefix tailTrace_261805
  have hstable : (prefixWord ++ tailWord_261805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261805).length < 2 ^ (prefixWord ++ tailWord_261805).sum := by decide
  have hdescent : baseEnd_261805 < baseStart_261805 := by decide
  rcases family_descends (prefixWord ++ tailWord_261805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261821 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_261821 : Nat := 118140960795 + 261821 * 2 ^ 59
def prefixEnd_261821 : Nat := 4983230072969 + 3 ^ 40 * 261821 * 2
def baseEnd_261821 : Nat := 134440018440925357833413

theorem tailTrace_261821 : CollatzResearch.WordTrace tailWord_261821 prefixEnd_261821 134440018440925357833413 := by
  unfold tailWord_261821
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549396384474707311929317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6366264256316471541286211 9549396384474707311929317)
  ·
    refine ⟨1790511822089007620986747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9549396384474707311929317 1790511822089007620986747)
    ·
      refine ⟨2685767733133511431480121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1790511822089007620986747 2685767733133511431480121)
      ·
        refine ⟨2014325799850133573610091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2685767733133511431480121 2014325799850133573610091)
        ·
          refine ⟨3021488699775200360415137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014325799850133573610091 3021488699775200360415137)
          ·
            refine ⟨2266116524831400270311353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3021488699775200360415137 2266116524831400270311353)
            ·
              refine ⟨1699587393623550202733515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2266116524831400270311353 1699587393623550202733515)
              ·
                refine ⟨2549381090435325304100273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699587393623550202733515 2549381090435325304100273)
                ·
                  refine ⟨1912035817826493978075205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2549381090435325304100273 1912035817826493978075205)
                  ·
                    refine ⟨358506715842467620889101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1912035817826493978075205 358506715842467620889101)
                    ·
                      refine ⟨134440018440925357833413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 358506715842467620889101 134440018440925357833413)
                      ·
                        rfl

theorem cell23_261821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_261821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261821 prefixEnd_261821 := by exact prefixLift 261821
  have htrace : WordTrace (prefixWord ++ tailWord_261821) baseStart_261821 baseEnd_261821 := by
    simpa [prefixWord, tailWord_261821, baseEnd_261821] using wordTrace_append hprefix tailTrace_261821
  have hstable : (prefixWord ++ tailWord_261821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261821).length < 2 ^ (prefixWord ++ tailWord_261821).sum := by decide
  have hdescent : baseEnd_261821 < baseStart_261821 := by decide
  rcases family_descends (prefixWord ++ tailWord_261821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261852 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_261852 : Nat := 118140960795 + 261852 * 2 ^ 59
def prefixEnd_261852 : Nat := 4983230072969 + 3 ^ 40 * 261852 * 2
def baseEnd_261852 : Nat := 134455936341214736545771

theorem tailTrace_261852 : CollatzResearch.WordTrace tailWord_261852 prefixEnd_261852 134455936341214736545771 := by
  unfold tailWord_261852
  simp only [CollatzResearch.WordTrace]
  refine ⟨4775263523681199803153905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6367018031574933070871873 4775263523681199803153905)
  ·
    refine ⟨3581447642760899852365429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4775263523681199803153905 3581447642760899852365429)
    ·
      refine ⟨335760716508834361159259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3581447642760899852365429 335760716508834361159259)
      ·
        refine ⟨503641074763251541738889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335760716508834361159259 503641074763251541738889)
        ·
          refine ⟨377730806072438656304167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503641074763251541738889 377730806072438656304167)
          ·
            refine ⟨566596209108657984456251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377730806072438656304167 566596209108657984456251)
            ·
              refine ⟨849894313662986976684377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566596209108657984456251 849894313662986976684377)
              ·
                refine ⟨637420735247240232513283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849894313662986976684377 637420735247240232513283)
                ·
                  refine ⟨956131102870860348769925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637420735247240232513283 956131102870860348769925)
                  ·
                    refine ⟨179274581788286315394361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956131102870860348769925 179274581788286315394361)
                    ·
                      refine ⟨134455936341214736545771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179274581788286315394361 134455936341214736545771)
                      ·
                        rfl

theorem cell23_261852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_261852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261852 prefixEnd_261852 := by exact prefixLift 261852
  have htrace : WordTrace (prefixWord ++ tailWord_261852) baseStart_261852 baseEnd_261852 := by
    simpa [prefixWord, tailWord_261852, baseEnd_261852] using wordTrace_append hprefix tailTrace_261852
  have hstable : (prefixWord ++ tailWord_261852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261852).length < 2 ^ (prefixWord ++ tailWord_261852).sum := by decide
  have hdescent : baseEnd_261852 < baseStart_261852 := by decide
  rcases family_descends (prefixWord ++ tailWord_261852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261871 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 2, 5]
def baseStart_261871 : Nat := 118140960795 + 261871 * 2 ^ 59
def prefixEnd_261871 : Nat := 4983230072969 + 3 ^ 40 * 261871 * 2
def baseEnd_261871 : Nat := 44821897491216720736061

theorem tailTrace_261871 : CollatzResearch.WordTrace tailWord_261871 prefixEnd_261871 44821897491216720736061 := by
  unfold tailWord_261871
  simp only [CollatzResearch.WordTrace]
  refine ⟨9551220034293565851249467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6367480022862377234166311 9551220034293565851249467)
  ·
    refine ⟨14326830051440348776874201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9551220034293565851249467 14326830051440348776874201)
    ·
      refine ⟨10745122538580261582655651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14326830051440348776874201 10745122538580261582655651)
      ·
        refine ⟨16117683807870392373983477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10745122538580261582655651 16117683807870392373983477)
        ·
          refine ⟨1511032856987849285060951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16117683807870392373983477 1511032856987849285060951)
          ·
            refine ⟨2266549285481773927591427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511032856987849285060951 2266549285481773927591427)
            ·
              refine ⟨3399823928222660891387141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266549285481773927591427 3399823928222660891387141)
              ·
                refine ⟨637466986541748917135089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3399823928222660891387141 637466986541748917135089)
                ·
                  refine ⟨478100239906311687851317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637466986541748917135089 478100239906311687851317)
                  ·
                    refine ⟨44821897491216720736061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 478100239906311687851317 44821897491216720736061)
                    ·
                      rfl

theorem cell23_261871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_261871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261871 prefixEnd_261871 := by exact prefixLift 261871
  have htrace : WordTrace (prefixWord ++ tailWord_261871) baseStart_261871 baseEnd_261871 := by
    simpa [prefixWord, tailWord_261871, baseEnd_261871] using wordTrace_append hprefix tailTrace_261871
  have hstable : (prefixWord ++ tailWord_261871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261871).length < 2 ^ (prefixWord ++ tailWord_261871).sum := by decide
  have hdescent : baseEnd_261871 < baseStart_261871 := by decide
  rcases family_descends (prefixWord ++ tailWord_261871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261891 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 4]
def baseStart_261891 : Nat := 118140960795 + 261891 * 2 ^ 59
def prefixEnd_261891 : Nat := 4983230072969 + 3 ^ 40 * 261891 * 2
def baseEnd_261891 : Nat := 134475962086740083958091

theorem tailTrace_261891 : CollatzResearch.WordTrace tailWord_261891 prefixEnd_261891 134475962086740083958091 := by
  unfold tailWord_261891
  simp only [CollatzResearch.WordTrace]
  refine ⟨9551949494221109266977527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6367966329480739511318351 9551949494221109266977527)
  ·
    refine ⟨14327924241331663900466291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9551949494221109266977527 14327924241331663900466291)
    ·
      refine ⟨21491886361997495850699437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14327924241331663900466291 21491886361997495850699437)
      ·
        refine ⟨8059457385749060944012289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21491886361997495850699437 8059457385749060944012289)
        ·
          refine ⟨6044593039311795708009217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8059457385749060944012289 6044593039311795708009217)
          ·
            refine ⟨4533444779483846781006913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6044593039311795708009217 4533444779483846781006913)
            ·
              refine ⟨3400083584612885085755185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4533444779483846781006913 3400083584612885085755185)
              ·
                refine ⟨2550062688459663814316389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400083584612885085755185 2550062688459663814316389)
                ·
                  refine ⟨478136754086186965184323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2550062688459663814316389 478136754086186965184323)
                  ·
                    refine ⟨717205131129280447776485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 478136754086186965184323 717205131129280447776485)
                    ·
                      refine ⟨134475962086740083958091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 717205131129280447776485 134475962086740083958091)
                      ·
                        rfl

theorem cell23_261891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_261891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261891 prefixEnd_261891 := by exact prefixLift 261891
  have htrace : WordTrace (prefixWord ++ tailWord_261891) baseStart_261891 baseEnd_261891 := by
    simpa [prefixWord, tailWord_261891, baseEnd_261891] using wordTrace_append hprefix tailTrace_261891
  have hstable : (prefixWord ++ tailWord_261891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261891).length < 2 ^ (prefixWord ++ tailWord_261891).sum := by decide
  have hdescent : baseEnd_261891 < baseStart_261891 := by decide
  rcases family_descends (prefixWord ++ tailWord_261891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261921 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_261921 : Nat := 118140960795 + 261921 * 2 ^ 59
def prefixEnd_261921 : Nat := 4983230072969 + 3 ^ 40 * 261921 * 2
def baseEnd_261921 : Nat := 134491366506374966582953

theorem tailTrace_261921 : CollatzResearch.WordTrace tailWord_261921 prefixEnd_261921 134491366506374966582953 := by
  unfold tailWord_261921
  simp only [CollatzResearch.WordTrace]
  refine ⟨9553043684112424390569617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6368695789408282927046411 9553043684112424390569617)
  ·
    refine ⟨7164782763084318292927213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9553043684112424390569617 7164782763084318292927213)
    ·
      refine ⟨2686793536156619359847705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7164782763084318292927213 2686793536156619359847705)
      ·
        refine ⟨2015095152117464519885779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2686793536156619359847705 2015095152117464519885779)
        ·
          refine ⟨3022642728176196779828669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015095152117464519885779 3022642728176196779828669)
          ·
            refine ⟨1133491023066073792435751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3022642728176196779828669 1133491023066073792435751)
            ·
              refine ⟨1700236534599110688653627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133491023066073792435751 1700236534599110688653627)
              ·
                refine ⟨2550354801898666032980441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700236534599110688653627 2550354801898666032980441)
                ·
                  refine ⟨1912766101423999524735331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2550354801898666032980441 1912766101423999524735331)
                  ·
                    refine ⟨2869149152135999287102997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1912766101423999524735331 2869149152135999287102997)
                    ·
                      refine ⟨134491366506374966582953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2869149152135999287102997 134491366506374966582953)
                      ·
                        rfl

theorem cell23_261921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_261921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261921 prefixEnd_261921 := by exact prefixLift 261921
  have htrace : WordTrace (prefixWord ++ tailWord_261921) baseStart_261921 baseEnd_261921 := by
    simpa [prefixWord, tailWord_261921, baseEnd_261921] using wordTrace_append hprefix tailTrace_261921
  have hstable : (prefixWord ++ tailWord_261921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261921).length < 2 ^ (prefixWord ++ tailWord_261921).sum := by decide
  have hdescent : baseEnd_261921 < baseStart_261921 := by decide
  rcases family_descends (prefixWord ++ tailWord_261921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261942 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_261942 : Nat := 118140960795 + 261942 * 2 ^ 59
def prefixEnd_261942 : Nat := 4983230072969 + 3 ^ 40 * 261942 * 2
def baseEnd_261942 : Nat := 134502149600119384420357

theorem tailTrace_261942 : CollatzResearch.WordTrace tailWord_261942 prefixEnd_261942 134502149600119384420357 := by
  unfold tailWord_261942
  simp only [CollatzResearch.WordTrace]
  refine ⟨597113101064771561067755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6369206411357563318056053 597113101064771561067755)
  ·
    refine ⟨895669651597157341601633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 597113101064771561067755 895669651597157341601633)
    ·
      refine ⟨671752238697868006201225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 895669651597157341601633 671752238697868006201225)
      ·
        refine ⟨503814179023401004650919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671752238697868006201225 503814179023401004650919)
        ·
          refine ⟨755721268535101506976379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503814179023401004650919 755721268535101506976379)
          ·
            refine ⟨1133581902802652260464569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755721268535101506976379 1133581902802652260464569)
            ·
              refine ⟨850186427101989195348427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133581902802652260464569 850186427101989195348427)
              ·
                refine ⟨1275279640652983793022641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850186427101989195348427 1275279640652983793022641)
                ·
                  refine ⟨956459730489737844766981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1275279640652983793022641 956459730489737844766981)
                  ·
                    refine ⟨179336199466825845893809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 956459730489737844766981 179336199466825845893809)
                    ·
                      refine ⟨134502149600119384420357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179336199466825845893809 134502149600119384420357)
                      ·
                        rfl

theorem cell23_261942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_261942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261942 prefixEnd_261942 := by exact prefixLift 261942
  have htrace : WordTrace (prefixWord ++ tailWord_261942) baseStart_261942 baseEnd_261942 := by
    simpa [prefixWord, tailWord_261942, baseEnd_261942] using wordTrace_append hprefix tailTrace_261942
  have hstable : (prefixWord ++ tailWord_261942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261942).length < 2 ^ (prefixWord ++ tailWord_261942).sum := by decide
  have hdescent : baseEnd_261942 < baseStart_261942 := by decide
  rcases family_descends (prefixWord ++ tailWord_261942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261978 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 1, 5]
def baseStart_261978 : Nat := 118140960795 + 261978 * 2 ^ 59
def prefixEnd_261978 : Nat := 4983230072969 + 3 ^ 40 * 261978 * 2
def baseEnd_261978 : Nat := 44840211634560414523397

theorem tailTrace_261978 : CollatzResearch.WordTrace tailWord_261978 prefixEnd_261978 44840211634560414523397 := by
  unfold tailWord_261978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388780661226480781348647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6370081763270615416929725 2388780661226480781348647)
  ·
    refine ⟨3583170991839721172022971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2388780661226480781348647 3583170991839721172022971)
    ·
      refine ⟨5374756487759581758034457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3583170991839721172022971 5374756487759581758034457)
      ·
        refine ⟨4031067365819686318525843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5374756487759581758034457 4031067365819686318525843)
        ·
          refine ⟨6046601048729529477788765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031067365819686318525843 6046601048729529477788765)
          ·
            refine ⟨2267475393273573554170787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6046601048729529477788765 2267475393273573554170787)
            ·
              refine ⟨3401213089910360331256181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267475393273573554170787 3401213089910360331256181)
              ·
                refine ⟨318863727179096281055267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3401213089910360331256181 318863727179096281055267)
                ·
                  refine ⟨478295590768644421582901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318863727179096281055267 478295590768644421582901)
                  ·
                    refine ⟨44840211634560414523397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 478295590768644421582901 44840211634560414523397)
                    ·
                      rfl

theorem cell23_261978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_261978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261978 prefixEnd_261978 := by exact prefixLift 261978
  have htrace : WordTrace (prefixWord ++ tailWord_261978) baseStart_261978 baseEnd_261978 := by
    simpa [prefixWord, tailWord_261978, baseEnd_261978] using wordTrace_append hprefix tailTrace_261978
  have hstable : (prefixWord ++ tailWord_261978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261978).length < 2 ^ (prefixWord ++ tailWord_261978).sum := by decide
  have hdescent : baseEnd_261978 < baseStart_261978 := by decide
  rcases family_descends (prefixWord ++ tailWord_261978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261985 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 2, 3, 2]
def baseStart_261985 : Nat := 118140960795 + 261985 * 2 ^ 59
def prefixEnd_261985 : Nat := 4983230072969 + 3 ^ 40 * 261985 * 2
def baseEnd_261985 : Nat := 134524229268262716182659

theorem tailTrace_261985 : CollatzResearch.WordTrace tailWord_261985 prefixEnd_261985 134524229268262716182659 := by
  unfold tailWord_261985
  simp only [CollatzResearch.WordTrace]
  refine ⟨9555377955880563320899409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6370251970587042213932939 9555377955880563320899409)
  ·
    refine ⟨7166533466910422490674557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9555377955880563320899409 7166533466910422490674557)
    ·
      refine ⟨2687450050091408434002959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7166533466910422490674557 2687450050091408434002959)
      ·
        refine ⟨4031175075137112651004439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2687450050091408434002959 4031175075137112651004439)
        ·
          refine ⟨6046762612705668976506659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031175075137112651004439 6046762612705668976506659)
          ·
            refine ⟨9070143919058503464759989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6046762612705668976506659 9070143919058503464759989)
            ·
              refine ⟨850325992411734699821249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9070143919058503464759989 850325992411734699821249)
              ·
                refine ⟨637744494308801024865937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850325992411734699821249 637744494308801024865937)
                ·
                  refine ⟨478308370731600768649453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637744494308801024865937 478308370731600768649453)
                  ·
                    refine ⟨179365639024350288243545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 478308370731600768649453 179365639024350288243545)
                    ·
                      refine ⟨134524229268262716182659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179365639024350288243545 134524229268262716182659)
                      ·
                        rfl

theorem cell23_261985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_261985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_261985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_261985 prefixEnd_261985 := by exact prefixLift 261985
  have htrace : WordTrace (prefixWord ++ tailWord_261985) baseStart_261985 baseEnd_261985 := by
    simpa [prefixWord, tailWord_261985, baseEnd_261985] using wordTrace_append hprefix tailTrace_261985
  have hstable : (prefixWord ++ tailWord_261985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261985).length < 2 ^ (prefixWord ++ tailWord_261985).sum := by decide
  have hdescent : baseEnd_261985 < baseStart_261985 := by decide
  rcases family_descends (prefixWord ++ tailWord_261985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262015 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 5, 2, 2]
def baseStart_262015 : Nat := 118140960795 + 262015 * 2 ^ 59
def prefixEnd_262015 : Nat := 4983230072969 + 3 ^ 40 * 262015 * 2
def baseEnd_262015 : Nat := 134539633687897598807521

theorem tailTrace_262015 : CollatzResearch.WordTrace tailWord_262015 prefixEnd_262015 134539633687897598807521 := by
  unfold tailWord_262015
  simp only [CollatzResearch.WordTrace]
  refine ⟨9556472145771878444491499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6370981430514585629660999 9556472145771878444491499)
  ·
    refine ⟨14334708218657817666737249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9556472145771878444491499 14334708218657817666737249)
    ·
      refine ⟨10751031163993363250052937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14334708218657817666737249 10751031163993363250052937)
      ·
        refine ⟨8063273372995022437539703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10751031163993363250052937 8063273372995022437539703)
        ·
          refine ⟨12094910059492533656309555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8063273372995022437539703 12094910059492533656309555)
          ·
            refine ⟨18142365089238800484464333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12094910059492533656309555 18142365089238800484464333)
            ·
              refine ⟨6803386908464550181674125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18142365089238800484464333 6803386908464550181674125)
              ·
                refine ⟨2551270090674206318127797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6803386908464550181674125 2551270090674206318127797)
                ·
                  refine ⟨239181571000706842324481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2551270090674206318127797 239181571000706842324481)
                  ·
                    refine ⟨179386178250530131743361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239181571000706842324481 179386178250530131743361)
                    ·
                      refine ⟨134539633687897598807521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179386178250530131743361 134539633687897598807521)
                      ·
                        rfl

theorem cell23_262015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 2, 2].length) (baseStart_262015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262015 prefixEnd_262015 := by exact prefixLift 262015
  have htrace : WordTrace (prefixWord ++ tailWord_262015) baseStart_262015 baseEnd_262015 := by
    simpa [prefixWord, tailWord_262015, baseEnd_262015] using wordTrace_append hprefix tailTrace_262015
  have hstable : (prefixWord ++ tailWord_262015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262015).length < 2 ^ (prefixWord ++ tailWord_262015).sum := by decide
  have hdescent : baseEnd_262015 < baseStart_262015 := by decide
  rcases family_descends (prefixWord ++ tailWord_262015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262021 : List Nat := [1, 3, 1, 1, 3, 2, 1, 11]
def baseStart_262021 : Nat := 118140960795 + 262021 * 2 ^ 59
def prefixEnd_262021 : Nat := 4983230072969 + 3 ^ 40 * 262021 * 2
def baseEnd_262021 : Nat := 4983063502660169456759

theorem tailTrace_262021 : CollatzResearch.WordTrace tailWord_262021 prefixEnd_262021 4983063502660169456759 := by
  unfold tailWord_262021
  simp only [CollatzResearch.WordTrace]
  refine ⟨9556690983750141469209917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6371127322500094312806611 9556690983750141469209917)
  ·
    refine ⟨3583759118906303050953719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9556690983750141469209917 3583759118906303050953719)
    ·
      refine ⟨5375638678359454576430579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3583759118906303050953719 5375638678359454576430579)
      ·
        refine ⟨8063458017539181864645869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5375638678359454576430579 8063458017539181864645869)
        ·
          refine ⟨3023796756577193199242201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8063458017539181864645869 3023796756577193199242201)
          ·
            refine ⟨2267847567432894899431651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3023796756577193199242201 2267847567432894899431651)
            ·
              refine ⟨3401771351149342349147477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267847567432894899431651 3401771351149342349147477)
              ·
                refine ⟨4983063502660169456759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 3401771351149342349147477 4983063502660169456759)
                ·
                  rfl

theorem cell23_262021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 11].length) (baseStart_262021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262021 prefixEnd_262021 := by exact prefixLift 262021
  have htrace : WordTrace (prefixWord ++ tailWord_262021) baseStart_262021 baseEnd_262021 := by
    simpa [prefixWord, tailWord_262021, baseEnd_262021] using wordTrace_append hprefix tailTrace_262021
  have hstable : (prefixWord ++ tailWord_262021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262021).length < 2 ^ (prefixWord ++ tailWord_262021).sum := by decide
  have hdescent : baseEnd_262021 < baseStart_262021 := by decide
  rcases family_descends (prefixWord ++ tailWord_262021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262042 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 2, 4]
def baseStart_262042 : Nat := 118140960795 + 262042 * 2 ^ 59
def prefixEnd_262042 : Nat := 4983230072969 + 3 ^ 40 * 262042 * 2
def baseEnd_262042 : Nat := 44851165888522997723299

theorem tailTrace_262042 : CollatzResearch.WordTrace tailWord_262042 prefixEnd_262042 44851165888522997723299 := by
  unfold tailWord_262042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2389364229168515513931095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6371637944449374703816253 2389364229168515513931095)
  ·
    refine ⟨3584046343752773270896643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2389364229168515513931095 3584046343752773270896643)
    ·
      refine ⟨5376069515629159906344965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3584046343752773270896643 5376069515629159906344965)
      ·
        refine ⟨1008013034180467482439681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5376069515629159906344965 1008013034180467482439681)
        ·
          refine ⟨756009775635350611829761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008013034180467482439681 756009775635350611829761)
          ·
            refine ⟨567007331726512958872321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756009775635350611829761 567007331726512958872321)
            ·
              refine ⟨425255498794884719154241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567007331726512958872321 425255498794884719154241)
              ·
                refine ⟨318941624096163539365681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425255498794884719154241 318941624096163539365681)
                ·
                  refine ⟨239206218072122654524261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318941624096163539365681 239206218072122654524261)
                  ·
                    refine ⟨44851165888522997723299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239206218072122654524261 44851165888522997723299)
                    ·
                      rfl

theorem cell23_262042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_262042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262042 prefixEnd_262042 := by exact prefixLift 262042
  have htrace : WordTrace (prefixWord ++ tailWord_262042) baseStart_262042 baseEnd_262042 := by
    simpa [prefixWord, tailWord_262042, baseEnd_262042] using wordTrace_append hprefix tailTrace_262042
  have hstable : (prefixWord ++ tailWord_262042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262042).length < 2 ^ (prefixWord ++ tailWord_262042).sum := by decide
  have hdescent : baseEnd_262042 < baseStart_262042 := by decide
  rcases family_descends (prefixWord ++ tailWord_262042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262048 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 3]
def baseStart_262048 : Nat := 118140960795 + 262048 * 2 ^ 59
def prefixEnd_262048 : Nat := 4983230072969 + 3 ^ 40 * 262048 * 2
def baseEnd_262048 : Nat := 134556578549495969694869

theorem tailTrace_262048 : CollatzResearch.WordTrace tailWord_262048 prefixEnd_262048 134556578549495969694869 := by
  unfold tailWord_262048
  simp only [CollatzResearch.WordTrace]
  refine ⟨4778837877326162540221399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6371783836434883386961865 4778837877326162540221399)
  ·
    refine ⟨7168256815989243810332099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4778837877326162540221399 7168256815989243810332099)
    ·
      refine ⟨10752385223983865715498149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7168256815989243810332099 10752385223983865715498149)
      ·
        refine ⟨2016072229496974821655903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10752385223983865715498149 2016072229496974821655903)
        ·
          refine ⟨3024108344245462232483855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2016072229496974821655903 3024108344245462232483855)
          ·
            refine ⟨4536162516368193348725783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024108344245462232483855 4536162516368193348725783)
            ·
              refine ⟨6804243774552290023088675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536162516368193348725783 6804243774552290023088675)
              ·
                refine ⟨10206365661828435034633013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6804243774552290023088675 10206365661828435034633013)
                ·
                  refine ⟨956846780796415784496845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10206365661828435034633013 956846780796415784496845)
                  ·
                    refine ⟨358817542798655919186317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 956846780796415784496845 358817542798655919186317)
                    ·
                      refine ⟨134556578549495969694869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 358817542798655919186317 134556578549495969694869)
                      ·
                        rfl

theorem cell23_262048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_262048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262048 prefixEnd_262048 := by exact prefixLift 262048
  have htrace : WordTrace (prefixWord ++ tailWord_262048) baseStart_262048 baseEnd_262048 := by
    simpa [prefixWord, tailWord_262048, baseEnd_262048] using wordTrace_append hprefix tailTrace_262048
  have hstable : (prefixWord ++ tailWord_262048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262048).length < 2 ^ (prefixWord ++ tailWord_262048).sum := by decide
  have hdescent : baseEnd_262048 < baseStart_262048 := by decide
  rcases family_descends (prefixWord ++ tailWord_262048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262055 : List Nat := [1, 1, 6, 1, 2, 3, 1, 8]
def baseStart_262055 : Nat := 118140960795 + 262055 * 2 ^ 59
def prefixEnd_262055 : Nat := 4983230072969 + 3 ^ 40 * 262055 * 2
def baseEnd_262055 : Nat := 4983710107928794159531

theorem tailTrace_262055 : CollatzResearch.WordTrace tailWord_262055 prefixEnd_262055 4983710107928794159531 := by
  unfold tailWord_262055
  simp only [CollatzResearch.WordTrace]
  refine ⟨9557931065626965275947619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6371954043751310183965079 9557931065626965275947619)
  ·
    refine ⟨14336896598440447913921429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9557931065626965275947619 14336896598440447913921429)
    ·
      refine ⟨672042028051895995965067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14336896598440447913921429 672042028051895995965067)
      ·
        refine ⟨1008063042077843993947601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672042028051895995965067 1008063042077843993947601)
        ·
          refine ⟨756047281558382995460701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008063042077843993947601 756047281558382995460701)
          ·
            refine ⟨283517730584393623297763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 756047281558382995460701 283517730584393623297763)
            ·
              refine ⟨425276595876590434946645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283517730584393623297763 425276595876590434946645)
              ·
                refine ⟨4983710107928794159531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 425276595876590434946645 4983710107928794159531)
                ·
                  rfl

theorem cell23_262055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 8].length) (baseStart_262055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262055 prefixEnd_262055 := by exact prefixLift 262055
  have htrace : WordTrace (prefixWord ++ tailWord_262055) baseStart_262055 baseEnd_262055 := by
    simpa [prefixWord, tailWord_262055, baseEnd_262055] using wordTrace_append hprefix tailTrace_262055
  have hstable : (prefixWord ++ tailWord_262055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262055).length < 2 ^ (prefixWord ++ tailWord_262055).sum := by decide
  have hdescent : baseEnd_262055 < baseStart_262055 := by decide
  rcases family_descends (prefixWord ++ tailWord_262055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262065 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 1, 3, 3]
def baseStart_262065 : Nat := 118140960795 + 262065 * 2 ^ 59
def prefixEnd_262065 : Nat := 4983230072969 + 3 ^ 40 * 262065 * 2
def baseEnd_262065 : Nat := 134565307720622403182291

theorem tailTrace_262065 : CollatzResearch.WordTrace tailWord_262065 prefixEnd_262065 134565307720622403182291 := by
  unfold tailWord_262065
  simp only [CollatzResearch.WordTrace]
  refine ⟨9558295795590736983811649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6372197197060491322541099 9558295795590736983811649)
  ·
    refine ⟨7168721846693052737858737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9558295795590736983811649 7168721846693052737858737)
    ·
      refine ⟨5376541385019789553394053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7168721846693052737858737 5376541385019789553394053)
      ·
        refine ⟨1008101509691210541261385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5376541385019789553394053 1008101509691210541261385)
        ·
          refine ⟨756076132268407905946039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008101509691210541261385 756076132268407905946039)
          ·
            refine ⟨1134114198402611858919059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756076132268407905946039 1134114198402611858919059)
            ·
              refine ⟨1701171297603917788378589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134114198402611858919059 1701171297603917788378589)
              ·
                refine ⟨637939236601469170641971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1701171297603917788378589 637939236601469170641971)
                ·
                  refine ⟨956908854902203755962957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637939236601469170641971 956908854902203755962957)
                  ·
                    refine ⟨358840820588326408486109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 956908854902203755962957 358840820588326408486109)
                    ·
                      refine ⟨134565307720622403182291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 358840820588326408486109 134565307720622403182291)
                      ·
                        rfl

theorem cell23_262065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_262065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262065 prefixEnd_262065 := by exact prefixLift 262065
  have htrace : WordTrace (prefixWord ++ tailWord_262065) baseStart_262065 baseEnd_262065 := by
    simpa [prefixWord, tailWord_262065, baseEnd_262065] using wordTrace_append hprefix tailTrace_262065
  have hstable : (prefixWord ++ tailWord_262065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262065).length < 2 ^ (prefixWord ++ tailWord_262065).sum := by decide
  have hdescent : baseEnd_262065 < baseStart_262065 := by decide
  rcases family_descends (prefixWord ++ tailWord_262065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262128 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 7]
def baseStart_262128 : Nat := 118140960795 + 262128 * 2 ^ 59
def prefixEnd_262128 : Nat := 4983230072969 + 3 ^ 40 * 262128 * 2
def baseEnd_262128 : Nat := 14955295222428406299389

theorem tailTrace_262128 : CollatzResearch.WordTrace tailWord_262128 prefixEnd_262128 14955295222428406299389 := by
  unfold tailWord_262128
  simp only [CollatzResearch.WordTrace]
  refine ⟨4780296797181249371677519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6373729062908332495570025 4780296797181249371677519)
  ·
    refine ⟨7170445195771874057516279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4780296797181249371677519 7170445195771874057516279)
    ·
      refine ⟨10755667793657811086274419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7170445195771874057516279 10755667793657811086274419)
      ·
        refine ⟨16133501690486716629411629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10755667793657811086274419 16133501690486716629411629)
        ·
          refine ⟨6050063133932518736029361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16133501690486716629411629 6050063133932518736029361)
          ·
            refine ⟨4537547350449389052022021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6050063133932518736029361 4537547350449389052022021)
            ·
              refine ⟨850790128209260447254129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4537547350449389052022021 850790128209260447254129)
              ·
                refine ⟨638092596156945335440597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850790128209260447254129 638092596156945335440597)
                ·
                  refine ⟨14955295222428406299389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 638092596156945335440597 14955295222428406299389)
                  ·
                    rfl

theorem cell23_262128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 7].length) (baseStart_262128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262128 prefixEnd_262128 := by exact prefixLift 262128
  have htrace : WordTrace (prefixWord ++ tailWord_262128) baseStart_262128 baseEnd_262128 := by
    simpa [prefixWord, tailWord_262128, baseEnd_262128] using wordTrace_append hprefix tailTrace_262128
  have hstable : (prefixWord ++ tailWord_262128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262128).length < 2 ^ (prefixWord ++ tailWord_262128).sum := by decide
  have hdescent : baseEnd_262128 < baseStart_262128 := by decide
  rcases family_descends (prefixWord ++ tailWord_262128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262142 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_262142 : Nat := 118140960795 + 262142 * 2 ^ 59
def prefixEnd_262142 : Nat := 4983230072969 + 3 ^ 40 * 262142 * 2
def baseEnd_262142 : Nat := 134604845731018601919437

theorem tailTrace_262142 : CollatzResearch.WordTrace tailWord_262142 prefixEnd_262142 134604845731018601919437 := by
  unfold tailWord_262142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195138027038972391795585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6374069477541186089576453 1195138027038972391795585)
  ·
    refine ⟨896353520279229293846689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1195138027038972391795585 896353520279229293846689)
    ·
      refine ⟨672265140209421970385017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 896353520279229293846689 672265140209421970385017)
      ·
        refine ⟨504198855157066477788763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672265140209421970385017 504198855157066477788763)
        ·
          refine ⟨756298282735599716683145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504198855157066477788763 756298282735599716683145)
          ·
            refine ⟨567223712051699787512359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756298282735599716683145 567223712051699787512359)
            ·
              refine ⟨850835568077549681268539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567223712051699787512359 850835568077549681268539)
              ·
                refine ⟨1276253352116324521902809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850835568077549681268539 1276253352116324521902809)
                ·
                  refine ⟨957190014087243391427107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1276253352116324521902809 957190014087243391427107)
                  ·
                    refine ⟨1435785021130865087140661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 957190014087243391427107 1435785021130865087140661)
                    ·
                      refine ⟨134604845731018601919437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1435785021130865087140661 134604845731018601919437)
                      ·
                        rfl

theorem cell23_262142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_262142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262142 prefixEnd_262142 := by exact prefixLift 262142
  have htrace : WordTrace (prefixWord ++ tailWord_262142) baseStart_262142 baseEnd_262142 := by
    simpa [prefixWord, tailWord_262142, baseEnd_262142] using wordTrace_append hprefix tailTrace_262142
  have hstable : (prefixWord ++ tailWord_262142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262142).length < 2 ^ (prefixWord ++ tailWord_262142).sum := by decide
  have hdescent : baseEnd_262142 < baseStart_262142 := by decide
  rcases family_descends (prefixWord ++ tailWord_262142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262173 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_262173 : Nat := 118140960795 + 262173 * 2 ^ 59
def prefixEnd_262173 : Nat := 4983230072969 + 3 ^ 40 * 262173 * 2
def baseEnd_262173 : Nat := 134620763631307980631795

theorem tailTrace_262173 : CollatzResearch.WordTrace tailWord_262173 prefixEnd_262173 134620763631307980631795 := by
  unfold tailWord_262173
  simp only [CollatzResearch.WordTrace]
  refine ⟨9562234879199471428743173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6374823252799647619162115 9562234879199471428743173)
  ·
    refine ⟨1792919039849900892889345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9562234879199471428743173 1792919039849900892889345)
    ·
      refine ⟨1344689279887425669667009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1792919039849900892889345 1344689279887425669667009)
      ·
        refine ⟨1008516959915569252250257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1344689279887425669667009 1008516959915569252250257)
        ·
          refine ⟨756387719936676939187693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008516959915569252250257 756387719936676939187693)
          ·
            refine ⟨283645394976253852195385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 756387719936676939187693 283645394976253852195385)
            ·
              refine ⟨212734046232190389146539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283645394976253852195385 212734046232190389146539)
              ·
                refine ⟨319101069348285583719809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212734046232190389146539 319101069348285583719809)
                ·
                  refine ⟨239325802011214187789857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319101069348285583719809 239325802011214187789857)
                  ·
                    refine ⟨179494351508410640842393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239325802011214187789857 179494351508410640842393)
                    ·
                      refine ⟨134620763631307980631795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179494351508410640842393 134620763631307980631795)
                      ·
                        rfl

theorem cell23_262173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_262173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262173 prefixEnd_262173 := by exact prefixLift 262173
  have htrace : WordTrace (prefixWord ++ tailWord_262173) baseStart_262173 baseEnd_262173 := by
    simpa [prefixWord, tailWord_262173, baseEnd_262173] using wordTrace_append hprefix tailTrace_262173
  have hstable : (prefixWord ++ tailWord_262173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262173).length < 2 ^ (prefixWord ++ tailWord_262173).sum := by decide
  have hdescent : baseEnd_262173 < baseStart_262173 := by decide
  rcases family_descends (prefixWord ++ tailWord_262173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262195 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 4]
def baseStart_262195 : Nat := 118140960795 + 262195 * 2 ^ 59
def prefixEnd_262195 : Nat := 4983230072969 + 3 ^ 40 * 262195 * 2
def baseEnd_262195 : Nat := 134632060205706894556693

theorem tailTrace_262195 : CollatzResearch.WordTrace tailWord_262195 prefixEnd_262195 134632060205706894556693 := by
  unfold tailWord_262195
  simp only [CollatzResearch.WordTrace]
  refine ⟨9563037285119769186044039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6375358190079846124029359 9563037285119769186044039)
  ·
    refine ⟨14344555927679653779066059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9563037285119769186044039 14344555927679653779066059)
    ·
      refine ⟨21516833891519480668599089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14344555927679653779066059 21516833891519480668599089)
      ·
        refine ⟨16137625418639610501449317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21516833891519480668599089 16137625418639610501449317)
        ·
          refine ⟨3025804765994926969021747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16137625418639610501449317 3025804765994926969021747)
          ·
            refine ⟨4538707148992390453532621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025804765994926969021747 4538707148992390453532621)
            ·
              refine ⟨1702015180872146420074733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4538707148992390453532621 1702015180872146420074733)
              ·
                refine ⟨638255692827054907528025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1702015180872146420074733 638255692827054907528025)
                ·
                  refine ⟨478691769620291180646019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 638255692827054907528025 478691769620291180646019)
                  ·
                    refine ⟨718037654430436770969029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 478691769620291180646019 718037654430436770969029)
                    ·
                      refine ⟨134632060205706894556693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 718037654430436770969029 134632060205706894556693)
                      ·
                        rfl

theorem cell23_262195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_262195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262195 prefixEnd_262195 := by exact prefixLift 262195
  have htrace : WordTrace (prefixWord ++ tailWord_262195) baseStart_262195 baseEnd_262195 := by
    simpa [prefixWord, tailWord_262195, baseEnd_262195] using wordTrace_append hprefix tailTrace_262195
  have hstable : (prefixWord ++ tailWord_262195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262195).length < 2 ^ (prefixWord ++ tailWord_262195).sum := by decide
  have hdescent : baseEnd_262195 < baseStart_262195 := by decide
  rcases family_descends (prefixWord ++ tailWord_262195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262272 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 4, 3, 2]
def baseStart_262272 : Nat := 118140960795 + 262272 * 2 ^ 59
def prefixEnd_262272 : Nat := 4983230072969 + 3 ^ 40 * 262272 * 2
def baseEnd_262272 : Nat := 134671598216103093293839

theorem tailTrace_262272 : CollatzResearch.WordTrace tailWord_262272 prefixEnd_262272 134671598216103093293839 := by
  unfold tailWord_262272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4782922852920405668298535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6377230470560540891064713 4782922852920405668298535)
  ·
    refine ⟨7174384279380608502447803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4782922852920405668298535 7174384279380608502447803)
    ·
      refine ⟨10761576419070912753671705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7174384279380608502447803 10761576419070912753671705)
      ·
        refine ⟨8071182314303184565253779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10761576419070912753671705 8071182314303184565253779)
        ·
          refine ⟨12106773471454776847880669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8071182314303184565253779 12106773471454776847880669)
          ·
            refine ⟨4540040051795541317955251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12106773471454776847880669 4540040051795541317955251)
            ·
              refine ⟨6810060077693311976932877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4540040051795541317955251 6810060077693311976932877)
              ·
                refine ⟨2553772529134991991349829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6810060077693311976932877 2553772529134991991349829)
                ·
                  refine ⟨478832349212810998378093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2553772529134991991349829 478832349212810998378093)
                  ·
                    refine ⟨179562130954804124391785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 478832349212810998378093 179562130954804124391785)
                    ·
                      refine ⟨134671598216103093293839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179562130954804124391785 134671598216103093293839)
                      ·
                        rfl

theorem cell23_262272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 3, 2].length) (baseStart_262272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262272 prefixEnd_262272 := by exact prefixLift 262272
  have htrace : WordTrace (prefixWord ++ tailWord_262272) baseStart_262272 baseEnd_262272 := by
    simpa [prefixWord, tailWord_262272, baseEnd_262272] using wordTrace_append hprefix tailTrace_262272
  have hstable : (prefixWord ++ tailWord_262272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262272).length < 2 ^ (prefixWord ++ tailWord_262272).sum := by decide
  have hdescent : baseEnd_262272 < baseStart_262272 := by decide
  rcases family_descends (prefixWord ++ tailWord_262272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262322 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_262322 : Nat := 118140960795 + 262322 * 2 ^ 59
def prefixEnd_262322 : Nat := 4983230072969 + 3 ^ 40 * 262322 * 2
def baseEnd_262322 : Nat := 134697272248827897668609

theorem tailTrace_262322 : CollatzResearch.WordTrace tailWord_262322 prefixEnd_262322 134697272248827897668609 := by
  unfold tailWord_262322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2391917338914917468979305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6378446237106446583944813 2391917338914917468979305)
  ·
    refine ⟨1793938004186188101734479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2391917338914917468979305 1793938004186188101734479)
    ·
      refine ⟨2690907006279282152601719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1793938004186188101734479 2690907006279282152601719)
      ·
        refine ⟨4036360509418923228902579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690907006279282152601719 4036360509418923228902579)
        ·
          refine ⟨6054540764128384843353869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4036360509418923228902579 6054540764128384843353869)
          ·
            refine ⟨2270452786548144316257701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6054540764128384843353869 2270452786548144316257701)
            ·
              refine ⟨425709897477777059298319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2270452786548144316257701 425709897477777059298319)
              ·
                refine ⟨638564846216665588947479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425709897477777059298319 638564846216665588947479)
                ·
                  refine ⟨957847269324998383421219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638564846216665588947479 957847269324998383421219)
                  ·
                    refine ⟨1436770903987497575131829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 957847269324998383421219 1436770903987497575131829)
                    ·
                      refine ⟨134697272248827897668609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1436770903987497575131829 134697272248827897668609)
                      ·
                        rfl

theorem cell23_262322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_262322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262322 prefixEnd_262322 := by exact prefixLift 262322
  have htrace : WordTrace (prefixWord ++ tailWord_262322) baseStart_262322 baseEnd_262322 := by
    simpa [prefixWord, tailWord_262322, baseEnd_262322] using wordTrace_append hprefix tailTrace_262322
  have hstable : (prefixWord ++ tailWord_262322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262322).length < 2 ^ (prefixWord ++ tailWord_262322).sum := by decide
  have hdescent : baseEnd_262322 < baseStart_262322 := by decide
  rcases family_descends (prefixWord ++ tailWord_262322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262336 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 3, 2, 2]
def baseStart_262336 : Nat := 118140960795 + 262336 * 2 ^ 59
def prefixEnd_262336 : Nat := 4983230072969 + 3 ^ 40 * 262336 * 2
def baseEnd_262336 : Nat := 134704460977990842893545

theorem tailTrace_262336 : CollatzResearch.WordTrace tailWord_262336 prefixEnd_262336 134704460977990842893545 := by
  unfold tailWord_262336
  simp only [CollatzResearch.WordTrace]
  refine ⟨4784089988804475133463431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6378786651739300177951241 4784089988804475133463431)
  ·
    refine ⟨7176134983206712700195147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4784089988804475133463431 7176134983206712700195147)
    ·
      refine ⟨10764202474810069050292721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7176134983206712700195147 10764202474810069050292721)
      ·
        refine ⟨8073151856107551787719541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10764202474810069050292721 8073151856107551787719541)
        ·
          refine ⟨756857986510082980098707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8073151856107551787719541 756857986510082980098707)
          ·
            refine ⟨1135286979765124470148061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756857986510082980098707 1135286979765124470148061)
            ·
              refine ⟨425732617411921676305523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1135286979765124470148061 425732617411921676305523)
              ·
                refine ⟨638598926117882514458285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425732617411921676305523 638598926117882514458285)
                ·
                  refine ⟨239474597294205942921857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638598926117882514458285 239474597294205942921857)
                  ·
                    refine ⟨179605947970654457191393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239474597294205942921857 179605947970654457191393)
                    ·
                      refine ⟨134704460977990842893545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179605947970654457191393 134704460977990842893545)
                      ·
                        rfl

theorem cell23_262336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3, 2, 2].length) (baseStart_262336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262336 prefixEnd_262336 := by exact prefixLift 262336
  have htrace : WordTrace (prefixWord ++ tailWord_262336) baseStart_262336 baseEnd_262336 := by
    simpa [prefixWord, tailWord_262336, baseEnd_262336] using wordTrace_append hprefix tailTrace_262336
  have hstable : (prefixWord ++ tailWord_262336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262336).length < 2 ^ (prefixWord ++ tailWord_262336).sum := by decide
  have hdescent : baseEnd_262336 < baseStart_262336 := by decide
  rcases family_descends (prefixWord ++ tailWord_262336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262386 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_262386 : Nat := 118140960795 + 262386 * 2 ^ 59
def prefixEnd_262386 : Nat := 4983230072969 + 3 ^ 40 * 262386 * 2
def baseEnd_262386 : Nat := 134730135010715647268315

theorem tailTrace_262386 : CollatzResearch.WordTrace tailWord_262386 prefixEnd_262386 134730135010715647268315 := by
  unfold tailWord_262386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2392500906856952201561753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6380002418285205870831341 2392500906856952201561753)
  ·
    refine ⟨1794375680142714151171315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2392500906856952201561753 1794375680142714151171315)
    ·
      refine ⟨2691563520214071226756973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1794375680142714151171315 2691563520214071226756973)
      ·
        refine ⟨1009336320080276710033865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2691563520214071226756973 1009336320080276710033865)
        ·
          refine ⟨757002240060207532525399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1009336320080276710033865 757002240060207532525399)
          ·
            refine ⟨1135503360090311298788099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757002240060207532525399 1135503360090311298788099)
            ·
              refine ⟨1703255040135466948182149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135503360090311298788099 1703255040135466948182149)
              ·
                refine ⟨319360320025400052784153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1703255040135466948182149 319360320025400052784153)
                ·
                  refine ⟨239520240019050039588115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319360320025400052784153 239520240019050039588115)
                  ·
                    refine ⟨359280360028575059382173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 239520240019050039588115 359280360028575059382173)
                    ·
                      refine ⟨134730135010715647268315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 359280360028575059382173 134730135010715647268315)
                      ·
                        rfl

theorem cell23_262386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_262386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262386 prefixEnd_262386 := by exact prefixLift 262386
  have htrace : WordTrace (prefixWord ++ tailWord_262386) baseStart_262386 baseEnd_262386 := by
    simpa [prefixWord, tailWord_262386, baseEnd_262386] using wordTrace_append hprefix tailTrace_262386
  have hstable : (prefixWord ++ tailWord_262386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262386).length < 2 ^ (prefixWord ++ tailWord_262386).sum := by decide
  have hdescent : baseEnd_262386 < baseStart_262386 := by decide
  rcases family_descends (prefixWord ++ tailWord_262386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262409 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 1, 4, 2]
def baseStart_262409 : Nat := 118140960795 + 262409 * 2 ^ 59
def prefixEnd_262409 : Nat := 4983230072969 + 3 ^ 40 * 262409 * 2
def baseEnd_262409 : Nat := 134741945065769057280709

theorem tailTrace_262409 : CollatzResearch.WordTrace tailWord_262409 prefixEnd_262409 134741945065769057280709 := by
  unfold tailWord_262409
  simp only [CollatzResearch.WordTrace]
  refine ⟨9570842506344483734334281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6380561670896322489556187 9570842506344483734334281)
  ·
    refine ⟨7178131879758362800750711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9570842506344483734334281 7178131879758362800750711)
    ·
      refine ⟨10767197819637544201126067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7178131879758362800750711 10767197819637544201126067)
      ·
        refine ⟨16150796729456316301689101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10767197819637544201126067 16150796729456316301689101)
        ·
          refine ⟨6056548773546118613133413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16150796729456316301689101 6056548773546118613133413)
          ·
            refine ⟨1135602895039897239962515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6056548773546118613133413 1135602895039897239962515)
            ·
              refine ⟨1703404342559845859943773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135602895039897239962515 1703404342559845859943773)
              ·
                refine ⟨638776628459942197478915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1703404342559845859943773 638776628459942197478915)
                ·
                  refine ⟨958164942689913296218373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638776628459942197478915 958164942689913296218373)
                  ·
                    refine ⟨179655926754358743040945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 958164942689913296218373 179655926754358743040945)
                    ·
                      refine ⟨134741945065769057280709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179655926754358743040945 134741945065769057280709)
                      ·
                        rfl

theorem cell23_262409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 4, 2].length) (baseStart_262409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262409 prefixEnd_262409 := by exact prefixLift 262409
  have htrace : WordTrace (prefixWord ++ tailWord_262409) baseStart_262409 baseEnd_262409 := by
    simpa [prefixWord, tailWord_262409, baseEnd_262409] using wordTrace_append hprefix tailTrace_262409
  have hstable : (prefixWord ++ tailWord_262409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262409).length < 2 ^ (prefixWord ++ tailWord_262409).sum := by decide
  have hdescent : baseEnd_262409 < baseStart_262409 := by decide
  rcases family_descends (prefixWord ++ tailWord_262409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262412 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 2, 4, 3]
def baseStart_262412 : Nat := 118140960795 + 262412 * 2 ^ 59
def prefixEnd_262412 : Nat := 4983230072969 + 3 ^ 40 * 262412 * 2
def baseEnd_262412 : Nat := 134743485507732545543195

theorem tailTrace_262412 : CollatzResearch.WordTrace tailWord_262412 prefixEnd_262412 134743485507732545543195 := by
  unfold tailWord_262412
  simp only [CollatzResearch.WordTrace]
  refine ⟨4785475962666807623346745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6380634616889076831128993 4785475962666807623346745)
  ·
    refine ⟨3589106972000105717510059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4785475962666807623346745 3589106972000105717510059)
    ·
      refine ⟨5383660458000158576265089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3589106972000105717510059 5383660458000158576265089)
      ·
        refine ⟨4037745343500118932198817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5383660458000158576265089 4037745343500118932198817)
        ·
          refine ⟨3028309007625089199149113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4037745343500118932198817 3028309007625089199149113)
          ·
            refine ⟨2271231755718816899361835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3028309007625089199149113 2271231755718816899361835)
            ·
              refine ⟨3406847633578225349042753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2271231755718816899361835 3406847633578225349042753)
              ·
                refine ⟨2555135725183669011782065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3406847633578225349042753 2555135725183669011782065)
                ·
                  refine ⟨1916351793887751758836549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2555135725183669011782065 1916351793887751758836549)
                  ·
                    refine ⟨359315961353953454781853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1916351793887751758836549 359315961353953454781853)
                    ·
                      refine ⟨134743485507732545543195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 359315961353953454781853 134743485507732545543195)
                      ·
                        rfl

theorem cell23_262412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_262412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262412 prefixEnd_262412 := by exact prefixLift 262412
  have htrace : WordTrace (prefixWord ++ tailWord_262412) baseStart_262412 baseEnd_262412 := by
    simpa [prefixWord, tailWord_262412, baseEnd_262412] using wordTrace_append hprefix tailTrace_262412
  have hstable : (prefixWord ++ tailWord_262412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262412).length < 2 ^ (prefixWord ++ tailWord_262412).sum := by decide
  have hdescent : baseEnd_262412 < baseStart_262412 := by decide
  rcases family_descends (prefixWord ++ tailWord_262412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262430 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_262430 : Nat := 118140960795 + 262430 * 2 ^ 59
def prefixEnd_262430 : Nat := 4983230072969 + 3 ^ 40 * 262430 * 2
def baseEnd_262430 : Nat := 134752728159513475118113

theorem tailTrace_262430 : CollatzResearch.WordTrace tailWord_262430 prefixEnd_262430 134752728159513475118113 := by
  unfold tailWord_262430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1196451054908550540106093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6381072292845602880565829 1196451054908550540106093)
  ·
    refine ⟨448669145590706452539785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1196451054908550540106093 448669145590706452539785)
    ·
      refine ⟨336501859193029839404839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448669145590706452539785 336501859193029839404839)
      ·
        refine ⟨504752788789544759107259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336501859193029839404839 504752788789544759107259)
        ·
          refine ⟨757129183184317138660889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504752788789544759107259 757129183184317138660889)
          ·
            refine ⟨567846887388237853995667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757129183184317138660889 567846887388237853995667)
            ·
              refine ⟨851770331082356780993501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567846887388237853995667 851770331082356780993501)
              ·
                refine ⟨319413874155883792872563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 851770331082356780993501 319413874155883792872563)
                ·
                  refine ⟨479120811233825689308845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319413874155883792872563 479120811233825689308845)
                  ·
                    refine ⟨179670304212684633490817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 479120811233825689308845 179670304212684633490817)
                    ·
                      refine ⟨134752728159513475118113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179670304212684633490817 134752728159513475118113)
                      ·
                        rfl

theorem cell23_262430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_262430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262430 prefixEnd_262430 := by exact prefixLift 262430
  have htrace : WordTrace (prefixWord ++ tailWord_262430) baseStart_262430 baseEnd_262430 := by
    simpa [prefixWord, tailWord_262430, baseEnd_262430] using wordTrace_append hprefix tailTrace_262430
  have hstable : (prefixWord ++ tailWord_262430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262430).length < 2 ^ (prefixWord ++ tailWord_262430).sum := by decide
  have hdescent : baseEnd_262430 < baseStart_262430 := by decide
  rcases family_descends (prefixWord ++ tailWord_262430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262449 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 7]
def baseStart_262449 : Nat := 118140960795 + 262449 * 2 ^ 59
def prefixEnd_262449 : Nat := 4983230072969 + 3 ^ 40 * 262449 * 2
def baseEnd_262449 : Nat := 14973609365772100086725

theorem tailTrace_262449 : CollatzResearch.WordTrace tailWord_262449 prefixEnd_262449 14973609365772100086725 := by
  unfold tailWord_262449
  simp only [CollatzResearch.WordTrace]
  refine ⟨9572301426199570565790401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6381534284133047043860267 9572301426199570565790401)
  ·
    refine ⟨7179226069649677924342801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9572301426199570565790401 7179226069649677924342801)
    ·
      refine ⟨5384419552237258443257101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7179226069649677924342801 5384419552237258443257101)
      ·
        refine ⟨2019157332088971916221413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5384419552237258443257101 2019157332088971916221413)
        ·
          refine ⟨378591999766682234291515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2019157332088971916221413 378591999766682234291515)
          ·
            refine ⟨567887999650023351437273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378591999766682234291515 567887999650023351437273)
            ·
              refine ⟨425915999737517513577955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567887999650023351437273 425915999737517513577955)
              ·
                refine ⟨638873999606276270366933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425915999737517513577955 638873999606276270366933)
                ·
                  refine ⟨14973609365772100086725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 638873999606276270366933 14973609365772100086725)
                  ·
                    rfl

theorem cell23_262449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 7].length) (baseStart_262449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262449 prefixEnd_262449 := by exact prefixLift 262449
  have htrace : WordTrace (prefixWord ++ tailWord_262449) baseStart_262449 baseEnd_262449 := by
    simpa [prefixWord, tailWord_262449, baseEnd_262449] using wordTrace_append hprefix tailTrace_262449
  have hstable : (prefixWord ++ tailWord_262449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262449).length < 2 ^ (prefixWord ++ tailWord_262449).sum := by decide
  have hdescent : baseEnd_262449 < baseStart_262449 := by decide
  rcases family_descends (prefixWord ++ tailWord_262449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262499 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 4]
def baseStart_262499 : Nat := 118140960795 + 262499 * 2 ^ 59
def prefixEnd_262499 : Nat := 4983230072969 + 3 ^ 40 * 262499 * 2
def baseEnd_262499 : Nat := 134788158324673705155295

theorem tailTrace_262499 : CollatzResearch.WordTrace tailWord_262499 prefixEnd_262499 134788158324673705155295 := by
  unfold tailWord_262499
  simp only [CollatzResearch.WordTrace]
  refine ⟨9574125076018429105110551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6382750050678952736740367 9574125076018429105110551)
  ·
    refine ⟨14361187614027643657665827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9574125076018429105110551 14361187614027643657665827)
    ·
      refine ⟨21541781421041465486498741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14361187614027643657665827 21541781421041465486498741)
      ·
        refine ⟨2019542008222637389359257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21541781421041465486498741 2019542008222637389359257)
        ·
          refine ⟨1514656506166978042019443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2019542008222637389359257 1514656506166978042019443)
          ·
            refine ⟨2271984759250467063029165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514656506166978042019443 2271984759250467063029165)
            ·
              refine ⟨851994284718925148635937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2271984759250467063029165 851994284718925148635937)
              ·
                refine ⟨638995713539193861476953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851994284718925148635937 638995713539193861476953)
                ·
                  refine ⟨479246785154395396107715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 638995713539193861476953 479246785154395396107715)
                  ·
                    refine ⟨718870177731593094161573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 479246785154395396107715 718870177731593094161573)
                    ·
                      refine ⟨134788158324673705155295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 718870177731593094161573 134788158324673705155295)
                      ·
                        rfl

theorem cell23_262499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_262499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262499 prefixEnd_262499 := by exact prefixLift 262499
  have htrace : WordTrace (prefixWord ++ tailWord_262499) baseStart_262499 baseEnd_262499 := by
    simpa [prefixWord, tailWord_262499, baseEnd_262499] using wordTrace_append hprefix tailTrace_262499
  have hstable : (prefixWord ++ tailWord_262499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262499).length < 2 ^ (prefixWord ++ tailWord_262499).sum := by decide
  have hdescent : baseEnd_262499 < baseStart_262499 := by decide
  rcases family_descends (prefixWord ++ tailWord_262499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262536 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_262536 : Nat := 118140960795 + 262536 * 2 ^ 59
def prefixEnd_262536 : Nat := 4983230072969 + 3 ^ 40 * 262536 * 2
def baseEnd_262536 : Nat := 134807157108890060392625

theorem tailTrace_262536 : CollatzResearch.WordTrace tailWord_262536 prefixEnd_262536 134807157108890060392625 := by
  unfold tailWord_262536
  simp only [CollatzResearch.WordTrace]
  refine ⟨4787737288442192212103731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6383649717922922949471641 4787737288442192212103731)
  ·
    refine ⟨7181605932663288318155597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4787737288442192212103731 7181605932663288318155597)
    ·
      refine ⟨2693102224748733119308349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7181605932663288318155597 2693102224748733119308349)
      ·
        refine ⟨1009913334280774919740631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2693102224748733119308349 1009913334280774919740631)
        ·
          refine ⟨1514870001421162379610947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009913334280774919740631 1514870001421162379610947)
          ·
            refine ⟨2272305002131743569416421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514870001421162379610947 2272305002131743569416421)
            ·
              refine ⟨426057187899701919265579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2272305002131743569416421 426057187899701919265579)
              ·
                refine ⟨639085781849552878898369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426057187899701919265579 639085781849552878898369)
                ·
                  refine ⟨479314336387164659173777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 639085781849552878898369 479314336387164659173777)
                  ·
                    refine ⟨359485752290373494380333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 479314336387164659173777 359485752290373494380333)
                    ·
                      refine ⟨134807157108890060392625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 359485752290373494380333 134807157108890060392625)
                      ·
                        rfl

theorem cell23_262536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_262536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262536 prefixEnd_262536 := by exact prefixLift 262536
  have htrace : WordTrace (prefixWord ++ tailWord_262536) baseStart_262536 baseEnd_262536 := by
    simpa [prefixWord, tailWord_262536, baseEnd_262536] using wordTrace_append hprefix tailTrace_262536
  have hstable : (prefixWord ++ tailWord_262536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262536).length < 2 ^ (prefixWord ++ tailWord_262536).sum := by decide
  have hdescent : baseEnd_262536 < baseStart_262536 := by decide
  rcases family_descends (prefixWord ++ tailWord_262536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262560 : List Nat := [2, 1, 1, 4, 1, 5, 2, 2, 1, 4]
def baseStart_262560 : Nat := 118140960795 + 262560 * 2 ^ 59
def prefixEnd_262560 : Nat := 4983230072969 + 3 ^ 40 * 262560 * 2
def baseEnd_262560 : Nat := 44939826881532655497505

theorem tailTrace_262560 : CollatzResearch.WordTrace tailWord_262560 prefixEnd_262560 44939826881532655497505 := by
  unfold tailWord_262560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788174964398718261540567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6384233285864957682054089 4788174964398718261540567)
  ·
    refine ⟨7182262446598077392310851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4788174964398718261540567 7182262446598077392310851)
    ·
      refine ⟨10773393669897116088466277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7182262446598077392310851 10773393669897116088466277)
      ·
        refine ⟨2020011313105709266587427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10773393669897116088466277 2020011313105709266587427)
        ·
          refine ⟨3030016969658563899881141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020011313105709266587427 3030016969658563899881141)
          ·
            refine ⟨284064090905490365613857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3030016969658563899881141 284064090905490365613857)
            ·
              refine ⟨213048068179117774210393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284064090905490365613857 213048068179117774210393)
              ·
                refine ⟨159786051134338330657795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213048068179117774210393 159786051134338330657795)
                ·
                  refine ⟨239679076701507495986693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159786051134338330657795 239679076701507495986693)
                  ·
                    refine ⟨44939826881532655497505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239679076701507495986693 44939826881532655497505)
                    ·
                      rfl

theorem cell23_262560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 1, 4].length) (baseStart_262560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262560 prefixEnd_262560 := by exact prefixLift 262560
  have htrace : WordTrace (prefixWord ++ tailWord_262560) baseStart_262560 baseEnd_262560 := by
    simpa [prefixWord, tailWord_262560, baseEnd_262560] using wordTrace_append hprefix tailTrace_262560
  have hstable : (prefixWord ++ tailWord_262560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262560).length < 2 ^ (prefixWord ++ tailWord_262560).sum := by decide
  have hdescent : baseEnd_262560 < baseStart_262560 := by decide
  rcases family_descends (prefixWord ++ tailWord_262560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262599 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 1, 6]
def baseStart_262599 : Nat := 118140960795 + 262599 * 2 ^ 59
def prefixEnd_262599 : Nat := 4983230072969 + 3 ^ 40 * 262599 * 2
def baseEnd_262599 : Nat := 44946502130041104634945

theorem tailTrace_262599 : CollatzResearch.WordTrace tailWord_262599 prefixEnd_262599 44946502130041104634945 := by
  unfold tailWord_262599
  simp only [CollatzResearch.WordTrace]
  refine ⟨9577772375656146183750851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6385181583770764122500567 9577772375656146183750851)
  ·
    refine ⟨14366658563484219275626277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9577772375656146183750851 14366658563484219275626277)
    ·
      refine ⟨2693748480653291114179927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14366658563484219275626277 2693748480653291114179927)
      ·
        refine ⟨4040622720979936671269891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2693748480653291114179927 4040622720979936671269891)
        ·
          refine ⟨6060934081469905006904837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040622720979936671269891 6060934081469905006904837)
          ·
            refine ⟨1136425140275607188794657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6060934081469905006904837 1136425140275607188794657)
            ·
              refine ⟨852318855206705391595993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1136425140275607188794657 852318855206705391595993)
              ·
                refine ⟨639239141405029043696995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852318855206705391595993 639239141405029043696995)
                ·
                  refine ⟨958858712107543565545493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639239141405029043696995 958858712107543565545493)
                  ·
                    refine ⟨44946502130041104634945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 958858712107543565545493 44946502130041104634945)
                    ·
                      rfl

theorem cell23_262599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_262599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262599 prefixEnd_262599 := by exact prefixLift 262599
  have htrace : WordTrace (prefixWord ++ tailWord_262599) baseStart_262599 baseEnd_262599 := by
    simpa [prefixWord, tailWord_262599, baseEnd_262599] using wordTrace_append hprefix tailTrace_262599
  have hstable : (prefixWord ++ tailWord_262599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262599).length < 2 ^ (prefixWord ++ tailWord_262599).sum := by decide
  have hdescent : baseEnd_262599 < baseStart_262599 := by decide
  rcases family_descends (prefixWord ++ tailWord_262599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262600 : List Nat := [2, 1, 3, 1, 3, 3, 2, 3, 1, 1, 3]
def baseStart_262600 : Nat := 118140960795 + 262600 * 2 ^ 59
def prefixEnd_262600 : Nat := 4983230072969 + 3 ^ 40 * 262600 * 2
def baseEnd_262600 : Nat := 134840019870777809992331

theorem tailTrace_262600 : CollatzResearch.WordTrace tailWord_262600 prefixEnd_262600 134840019870777809992331 := by
  unfold tailWord_262600
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788904424326261677268627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6385205899101682236358169 4788904424326261677268627)
  ·
    refine ⟨7183356636489392515902941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4788904424326261677268627 7183356636489392515902941)
    ·
      refine ⟨2693758738683522193463603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7183356636489392515902941 2693758738683522193463603)
      ·
        refine ⟨4040638108025283290195405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2693758738683522193463603 4040638108025283290195405)
        ·
          refine ⟨1515239290509481233823277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4040638108025283290195405 1515239290509481233823277)
          ·
            refine ⟨568214733941055462683729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1515239290509481233823277 568214733941055462683729)
            ·
              refine ⟨426161050455791597012797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568214733941055462683729 426161050455791597012797)
              ·
                refine ⟨159810393920921848879799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426161050455791597012797 159810393920921848879799)
                ·
                  refine ⟨239715590881382773319699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159810393920921848879799 239715590881382773319699)
                  ·
                    refine ⟨359573386322074159979549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 239715590881382773319699 359573386322074159979549)
                    ·
                      refine ⟨134840019870777809992331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 359573386322074159979549 134840019870777809992331)
                      ·
                        rfl

theorem cell23_262600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_262600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262600 prefixEnd_262600 := by exact prefixLift 262600
  have htrace : WordTrace (prefixWord ++ tailWord_262600) baseStart_262600 baseEnd_262600 := by
    simpa [prefixWord, tailWord_262600, baseEnd_262600] using wordTrace_append hprefix tailTrace_262600
  have hstable : (prefixWord ++ tailWord_262600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262600).length < 2 ^ (prefixWord ++ tailWord_262600).sum := by decide
  have hdescent : baseEnd_262600 < baseStart_262600 := by decide
  rcases family_descends (prefixWord ++ tailWord_262600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262623 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 3, 2, 2]
def baseStart_262623 : Nat := 118140960795 + 262623 * 2 ^ 59
def prefixEnd_262623 : Nat := 4983230072969 + 3 ^ 40 * 262623 * 2
def baseEnd_262623 : Nat := 134851829925831220004725

theorem tailTrace_262623 : CollatzResearch.WordTrace tailWord_262623 prefixEnd_262623 134851829925831220004725 := by
  unfold tailWord_262623
  simp only [CollatzResearch.WordTrace]
  refine ⟨9578647727569198282624523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6385765151712798855083015 9578647727569198282624523)
  ·
    refine ⟨14367971591353797423936785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9578647727569198282624523 14367971591353797423936785)
    ·
      refine ⟨10775978693515348067952589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14367971591353797423936785 10775978693515348067952589)
      ·
        refine ⟨4040992010068255525482221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10775978693515348067952589 4040992010068255525482221)
        ·
          refine ⟨1515372003775595822055833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4040992010068255525482221 1515372003775595822055833)
          ·
            refine ⟨1136529002831696866541875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515372003775595822055833 1136529002831696866541875)
            ·
              refine ⟨1704793504247545299812813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136529002831696866541875 1704793504247545299812813)
              ·
                refine ⟨639297564092829487429805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1704793504247545299812813 639297564092829487429805)
                ·
                  refine ⟨239736586534811057786177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639297564092829487429805 239736586534811057786177)
                  ·
                    refine ⟨179802439901108293339633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239736586534811057786177 179802439901108293339633)
                    ·
                      refine ⟨134851829925831220004725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179802439901108293339633 134851829925831220004725)
                      ·
                        rfl

theorem cell23_262623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_262623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262623 prefixEnd_262623 := by exact prefixLift 262623
  have htrace : WordTrace (prefixWord ++ tailWord_262623) baseStart_262623 baseEnd_262623 := by
    simpa [prefixWord, tailWord_262623, baseEnd_262623] using wordTrace_append hprefix tailTrace_262623
  have hstable : (prefixWord ++ tailWord_262623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262623).length < 2 ^ (prefixWord ++ tailWord_262623).sum := by decide
  have hdescent : baseEnd_262623 < baseStart_262623 := by decide
  rcases family_descends (prefixWord ++ tailWord_262623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262657 : List Nat := [1, 2, 4, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_262657 : Nat := 118140960795 + 262657 * 2 ^ 59
def prefixEnd_262657 : Nat := 4983230072969 + 3 ^ 40 * 262657 * 2
def baseEnd_262657 : Nat := 134869288268084086979569

theorem tailTrace_262657 : CollatzResearch.WordTrace tailWord_262657 prefixEnd_262657 134869288268084086979569 := by
  unfold tailWord_262657
  simp only [CollatzResearch.WordTrace]
  refine ⟨9579887809446022089362225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6386591872964014726241483 9579887809446022089362225)
  ·
    refine ⟨7184915857084516567021669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9579887809446022089362225 7184915857084516567021669)
    ·
      refine ⟨1347171723203346856316563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7184915857084516567021669 1347171723203346856316563)
      ·
        refine ⟨2020757584805020284474845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1347171723203346856316563 2020757584805020284474845)
        ·
          refine ⟨757784094301882606678067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2020757584805020284474845 757784094301882606678067)
          ·
            refine ⟨1136676141452823910017101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757784094301882606678067 1136676141452823910017101)
            ·
              refine ⟨426253553044808966256413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1136676141452823910017101 426253553044808966256413)
              ·
                refine ⟨159845082391803362346155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426253553044808966256413 159845082391803362346155)
                ·
                  refine ⟨239767623587705043519233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159845082391803362346155 239767623587705043519233)
                  ·
                    refine ⟨179825717690778782639425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239767623587705043519233 179825717690778782639425)
                    ·
                      refine ⟨134869288268084086979569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179825717690778782639425 134869288268084086979569)
                      ·
                        rfl

theorem cell23_262657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_262657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262657 prefixEnd_262657 := by exact prefixLift 262657
  have htrace : WordTrace (prefixWord ++ tailWord_262657) baseStart_262657 baseEnd_262657 := by
    simpa [prefixWord, tailWord_262657, baseEnd_262657] using wordTrace_append hprefix tailTrace_262657
  have hstable : (prefixWord ++ tailWord_262657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262657).length < 2 ^ (prefixWord ++ tailWord_262657).sum := by decide
  have hdescent : baseEnd_262657 < baseStart_262657 := by decide
  rcases family_descends (prefixWord ++ tailWord_262657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262689 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 1, 8]
def baseStart_262689 : Nat := 118140960795 + 262689 * 2 ^ 59
def prefixEnd_262689 : Nat := 4983230072969 + 3 ^ 40 * 262689 * 2
def baseEnd_262689 : Nat := 44961906549675987259807

theorem tailTrace_262689 : CollatzResearch.WordTrace tailWord_262689 prefixEnd_262689 44961906549675987259807 := by
  unfold tailWord_262689
  simp only [CollatzResearch.WordTrace]
  refine ⟨9581054945330091554527121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6387369963553394369684747 9581054945330091554527121)
  ·
    refine ⟨7185791208997568665895341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9581054945330091554527121 7185791208997568665895341)
    ·
      refine ⟨2694671703374088249710753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7185791208997568665895341 2694671703374088249710753)
      ·
        refine ⟨2021003777530566187283065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2694671703374088249710753 2021003777530566187283065)
        ·
          refine ⟨1515752833147924640462299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2021003777530566187283065 1515752833147924640462299)
          ·
            refine ⟨2273629249721886960693449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515752833147924640462299 2273629249721886960693449)
            ·
              refine ⟨1705221937291415220520087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2273629249721886960693449 1705221937291415220520087)
              ·
                refine ⟨2557832905937122830780131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705221937291415220520087 2557832905937122830780131)
                ·
                  refine ⟨3836749358905684246170197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2557832905937122830780131 3836749358905684246170197)
                  ·
                    refine ⟨44961906549675987259807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3836749358905684246170197 44961906549675987259807)
                    ·
                      rfl

theorem cell23_262689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_262689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262689 prefixEnd_262689 := by exact prefixLift 262689
  have htrace : WordTrace (prefixWord ++ tailWord_262689) baseStart_262689 baseEnd_262689 := by
    simpa [prefixWord, tailWord_262689, baseEnd_262689] using wordTrace_append hprefix tailTrace_262689
  have hstable : (prefixWord ++ tailWord_262689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262689).length < 2 ^ (prefixWord ++ tailWord_262689).sum := by decide
  have hdescent : baseEnd_262689 < baseStart_262689 := by decide
  rcases family_descends (prefixWord ++ tailWord_262689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262713 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 1, 4, 2]
def baseStart_262713 : Nat := 118140960795 + 262713 * 2 ^ 59
def prefixEnd_262713 : Nat := 4983230072969 + 3 ^ 40 * 262713 * 2
def baseEnd_262713 : Nat := 134898043184735867879311

theorem tailTrace_262713 : CollatzResearch.WordTrace tailWord_262713 prefixEnd_262713 134898043184735867879311 := by
  unfold tailWord_262713
  simp only [CollatzResearch.WordTrace]
  refine ⟨9581930297243143653400793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6387953531495429102267195 9581930297243143653400793)
  ·
    refine ⟨7186447722932357740050595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9581930297243143653400793 7186447722932357740050595)
    ·
      refine ⟨10779671584398536610075893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7186447722932357740050595 10779671584398536610075893)
      ·
        refine ⟨1010594211037362807194615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10779671584398536610075893 1010594211037362807194615)
        ·
          refine ⟨1515891316556044210791923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010594211037362807194615 1515891316556044210791923)
          ·
            refine ⟨2273836974834066316187885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515891316556044210791923 2273836974834066316187885)
            ·
              refine ⟨852688865562774868570457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2273836974834066316187885 852688865562774868570457)
              ·
                refine ⟨639516649172081151427843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 852688865562774868570457 639516649172081151427843)
                ·
                  refine ⟨959274973758121727141765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639516649172081151427843 959274973758121727141765)
                  ·
                    refine ⟨179864057579647823839081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 959274973758121727141765 179864057579647823839081)
                    ·
                      refine ⟨134898043184735867879311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179864057579647823839081 134898043184735867879311)
                      ·
                        rfl

theorem cell23_262713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_262713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262713 prefixEnd_262713 := by exact prefixLift 262713
  have htrace : WordTrace (prefixWord ++ tailWord_262713) baseStart_262713 baseEnd_262713 := by
    simpa [prefixWord, tailWord_262713, baseEnd_262713] using wordTrace_append hprefix tailTrace_262713
  have hstable : (prefixWord ++ tailWord_262713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262713).length < 2 ^ (prefixWord ++ tailWord_262713).sum := by decide
  have hdescent : baseEnd_262713 < baseStart_262713 := by decide
  rcases family_descends (prefixWord ++ tailWord_262713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262716 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_262716 : Nat := 118140960795 + 262716 * 2 ^ 59
def prefixEnd_262716 : Nat := 4983230072969 + 3 ^ 40 * 262716 * 2
def baseEnd_262716 : Nat := 134899583626699356141797

theorem tailTrace_262716 : CollatzResearch.WordTrace tailWord_262716 prefixEnd_262716 134899583626699356141797 := by
  unfold tailWord_262716
  simp only [CollatzResearch.WordTrace]
  refine ⟨4791019858116137582880001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6388026477488183443840001 4791019858116137582880001)
  ·
    refine ⟨3593264893587103187160001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4791019858116137582880001 3593264893587103187160001)
    ·
      refine ⟨2694948670190327390370001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3593264893587103187160001 2694948670190327390370001)
      ·
        refine ⟨2021211502642745542777501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2694948670190327390370001 2021211502642745542777501)
        ·
          refine ⟨757954313491029578541563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2021211502642745542777501 757954313491029578541563)
          ·
            refine ⟨1136931470236544367812345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757954313491029578541563 1136931470236544367812345)
            ·
              refine ⟨852698602677408275859259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1136931470236544367812345 852698602677408275859259)
              ·
                refine ⟨1279047904016112413788889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852698602677408275859259 1279047904016112413788889)
                ·
                  refine ⟨959285928012084310341667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1279047904016112413788889 959285928012084310341667)
                  ·
                    refine ⟨1438928892018126465512501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 959285928012084310341667 1438928892018126465512501)
                    ·
                      refine ⟨134899583626699356141797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1438928892018126465512501 134899583626699356141797)
                      ·
                        rfl

theorem cell23_262716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_262716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262716 prefixEnd_262716 := by exact prefixLift 262716
  have htrace : WordTrace (prefixWord ++ tailWord_262716) baseStart_262716 baseEnd_262716 := by
    simpa [prefixWord, tailWord_262716, baseEnd_262716] using wordTrace_append hprefix tailTrace_262716
  have hstable : (prefixWord ++ tailWord_262716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262716).length < 2 ^ (prefixWord ++ tailWord_262716).sum := by decide
  have hdescent : baseEnd_262716 < baseStart_262716 := by decide
  rcases family_descends (prefixWord ++ tailWord_262716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262717 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 1, 3, 2]
def baseStart_262717 : Nat := 118140960795 + 262717 * 2 ^ 59
def prefixEnd_262717 : Nat := 4983230072969 + 3 ^ 40 * 262717 * 2
def baseEnd_262717 : Nat := 134900097107353852229293

theorem tailTrace_262717 : CollatzResearch.WordTrace tailWord_262717 prefixEnd_262717 134900097107353852229293 := by
  unfold tailWord_262717
  simp only [CollatzResearch.WordTrace]
  refine ⟨9582076189228652336546405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6388050792819101557697603 9582076189228652336546405)
  ·
    refine ⟨1796639285480372313102451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9582076189228652336546405 1796639285480372313102451)
    ·
      refine ⟨2694958928220558469653677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1796639285480372313102451 2694958928220558469653677)
      ·
        refine ⟨1010609598082709426120129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2694958928220558469653677 1010609598082709426120129)
        ·
          refine ⟨757957198562032069590097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1010609598082709426120129 757957198562032069590097)
          ·
            refine ⟨568467898921524052192573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757957198562032069590097 568467898921524052192573)
            ·
              refine ⟨213175462095571519572215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568467898921524052192573 213175462095571519572215)
              ·
                refine ⟨319763193143357279358323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213175462095571519572215 319763193143357279358323)
                ·
                  refine ⟨479644789715035919037485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319763193143357279358323 479644789715035919037485)
                  ·
                    refine ⟨179866796143138469639057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 479644789715035919037485 179866796143138469639057)
                    ·
                      refine ⟨134900097107353852229293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179866796143138469639057 134900097107353852229293)
                      ·
                        rfl

theorem cell23_262717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_262717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262717 prefixEnd_262717 := by exact prefixLift 262717
  have htrace : WordTrace (prefixWord ++ tailWord_262717) baseStart_262717 baseEnd_262717 := by
    simpa [prefixWord, tailWord_262717, baseEnd_262717] using wordTrace_append hprefix tailTrace_262717
  have hstable : (prefixWord ++ tailWord_262717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262717).length < 2 ^ (prefixWord ++ tailWord_262717).sum := by decide
  have hdescent : baseEnd_262717 < baseStart_262717 := by decide
  rcases family_descends (prefixWord ++ tailWord_262717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262730 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2]
def baseStart_262730 : Nat := 118140960795 + 262730 * 2 ^ 59
def prefixEnd_262730 : Nat := 4983230072969 + 3 ^ 40 * 262730 * 2
def baseEnd_262730 : Nat := 134906772355862301366733

theorem tailTrace_262730 : CollatzResearch.WordTrace tailWord_262730 prefixEnd_262730 134906772355862301366733 := by
  unfold tailWord_262730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2395637584545388889192411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6388366892121037037846429 2395637584545388889192411)
  ·
    refine ⟨3593456376818083333788617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2395637584545388889192411 3593456376818083333788617)
    ·
      refine ⟨2695092282613562500341463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3593456376818083333788617 2695092282613562500341463)
      ·
        refine ⟨4042638423920343750512195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2695092282613562500341463 4042638423920343750512195)
        ·
          refine ⟨6063957635880515625768293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4042638423920343750512195 6063957635880515625768293)
          ·
            refine ⟨1136992056727596679831555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6063957635880515625768293 1136992056727596679831555)
            ·
              refine ⟨1705488085091395019747333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136992056727596679831555 1705488085091395019747333)
              ·
                refine ⟨319779015954636566202625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1705488085091395019747333 319779015954636566202625)
                ·
                  refine ⟨239834261965977424651969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319779015954636566202625 239834261965977424651969)
                  ·
                    refine ⟨179875696474483068488977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239834261965977424651969 179875696474483068488977)
                    ·
                      refine ⟨134906772355862301366733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 179875696474483068488977 134906772355862301366733)
                      ·
                        rfl

theorem cell23_262730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_262730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262730 prefixEnd_262730 := by exact prefixLift 262730
  have htrace : WordTrace (prefixWord ++ tailWord_262730) baseStart_262730 baseEnd_262730 := by
    simpa [prefixWord, tailWord_262730, baseEnd_262730] using wordTrace_append hprefix tailTrace_262730
  have hstable : (prefixWord ++ tailWord_262730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262730).length < 2 ^ (prefixWord ++ tailWord_262730).sum := by decide
  have hdescent : baseEnd_262730 < baseStart_262730 := by decide
  rcases family_descends (prefixWord ++ tailWord_262730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262733 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_262733 : Nat := 118140960795 + 262733 * 2 ^ 59
def prefixEnd_262733 : Nat := 4983230072969 + 3 ^ 40 * 262733 * 2
def baseEnd_262733 : Nat := 134908312797825789629219

theorem tailTrace_262733 : CollatzResearch.WordTrace tailWord_262733 prefixEnd_262733 134908312797825789629219 := by
  unfold tailWord_262733
  simp only [CollatzResearch.WordTrace]
  refine ⟨9582659757170687069128853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6388439838113791379419235 9582659757170687069128853)
  ·
    refine ⟨449187176117375956365415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9582659757170687069128853 449187176117375956365415)
    ·
      refine ⟨673780764176063934548123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449187176117375956365415 673780764176063934548123)
      ·
        refine ⟨1010671146264095901822185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673780764176063934548123 1010671146264095901822185)
        ·
          refine ⟨758003359698071926366639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1010671146264095901822185 758003359698071926366639)
          ·
            refine ⟨1137005039547107889549959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758003359698071926366639 1137005039547107889549959)
            ·
              refine ⟨1705507559320661834324939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137005039547107889549959 1705507559320661834324939)
              ·
                refine ⟨2558261338980992751487409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705507559320661834324939 2558261338980992751487409)
                ·
                  refine ⟨1918696004235744563615557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2558261338980992751487409 1918696004235744563615557)
                  ·
                    refine ⟨359755500794202105677917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1918696004235744563615557 359755500794202105677917)
                    ·
                      refine ⟨134908312797825789629219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 359755500794202105677917 134908312797825789629219)
                      ·
                        rfl

theorem cell23_262733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_262733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262733 prefixEnd_262733 := by exact prefixLift 262733
  have htrace : WordTrace (prefixWord ++ tailWord_262733) baseStart_262733 baseEnd_262733 := by
    simpa [prefixWord, tailWord_262733, baseEnd_262733] using wordTrace_append hprefix tailTrace_262733
  have hstable : (prefixWord ++ tailWord_262733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262733).length < 2 ^ (prefixWord ++ tailWord_262733).sum := by decide
  have hdescent : baseEnd_262733 < baseStart_262733 := by decide
  rcases family_descends (prefixWord ++ tailWord_262733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262770 : List Nat := [3, 2, 1, 2, 4, 1, 2, 3, 5]
def baseStart_262770 : Nat := 118140960795 + 262770 * 2 ^ 59
def prefixEnd_262770 : Nat := 4983230072969 + 3 ^ 40 * 262770 * 2
def baseEnd_262770 : Nat := 14991923509115793874061

theorem tailTrace_262770 : CollatzResearch.WordTrace tailWord_262770 prefixEnd_262770 14991923509115793874061 := by
  unfold tailWord_262770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2396002314509160597056441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6389339505357761592150509 2396002314509160597056441)
  ·
    refine ⟨1797001735881870447792331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2396002314509160597056441 1797001735881870447792331)
    ·
      refine ⟨2695502603822805671688497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1797001735881870447792331 2695502603822805671688497)
      ·
        refine ⟨2021626952867104253766373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2695502603822805671688497 2021626952867104253766373)
        ·
          refine ⟨379055053662582047581195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2021626952867104253766373 379055053662582047581195)
          ·
            refine ⟨568582580493873071371793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379055053662582047581195 568582580493873071371793)
            ·
              refine ⟨426436935370404803528845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568582580493873071371793 426436935370404803528845)
              ·
                refine ⟨159913850763901801323317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426436935370404803528845 159913850763901801323317)
                ·
                  refine ⟨14991923509115793874061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159913850763901801323317 14991923509115793874061)
                  ·
                    rfl

theorem cell23_262770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_262770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262770 prefixEnd_262770 := by exact prefixLift 262770
  have htrace : WordTrace (prefixWord ++ tailWord_262770) baseStart_262770 baseEnd_262770 := by
    simpa [prefixWord, tailWord_262770, baseEnd_262770] using wordTrace_append hprefix tailTrace_262770
  have hstable : (prefixWord ++ tailWord_262770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262770).length < 2 ^ (prefixWord ++ tailWord_262770).sum := by decide
  have hdescent : baseEnd_262770 < baseStart_262770 := by decide
  rcases family_descends (prefixWord ++ tailWord_262770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262813 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_262813 : Nat := 118140960795 + 262813 * 2 ^ 59
def prefixEnd_262813 : Nat := 4983230072969 + 3 ^ 40 * 262813 * 2
def baseEnd_262813 : Nat := 44983130416728492209617

theorem tailTrace_262813 : CollatzResearch.WordTrace tailWord_262813 prefixEnd_262813 44983130416728492209617 := by
  unfold tailWord_262813
  simp only [CollatzResearch.WordTrace]
  refine ⟨9585577596880860732041093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6390385064587240488027395 9585577596880860732041093)
  ·
    refine ⟨1797295799415161387257705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9585577596880860732041093 1797295799415161387257705)
    ·
      refine ⟨1347971849561371040443279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1797295799415161387257705 1347971849561371040443279)
      ·
        refine ⟨2021957774342056560664919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1347971849561371040443279 2021957774342056560664919)
        ·
          refine ⟨3032936661513084840997379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2021957774342056560664919 3032936661513084840997379)
          ·
            refine ⟨4549404992269627261496069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3032936661513084840997379 4549404992269627261496069)
            ·
              refine ⟨853013436050555111530513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4549404992269627261496069 853013436050555111530513)
              ·
                refine ⟨639760077037916333647885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853013436050555111530513 639760077037916333647885)
                ·
                  refine ⟨239910028889218625117957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 639760077037916333647885 239910028889218625117957)
                  ·
                    refine ⟨44983130416728492209617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239910028889218625117957 44983130416728492209617)
                    ·
                      rfl

theorem cell23_262813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_262813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262813 prefixEnd_262813 := by exact prefixLift 262813
  have htrace : WordTrace (prefixWord ++ tailWord_262813) baseStart_262813 baseEnd_262813 := by
    simpa [prefixWord, tailWord_262813, baseEnd_262813] using wordTrace_append hprefix tailTrace_262813
  have hstable : (prefixWord ++ tailWord_262813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262813).length < 2 ^ (prefixWord ++ tailWord_262813).sum := by decide
  have hdescent : baseEnd_262813 < baseStart_262813 := by decide
  rcases family_descends (prefixWord ++ tailWord_262813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262847 : List Nat := [1, 1, 2, 2, 2, 5, 3, 2, 1, 4]
def baseStart_262847 : Nat := 118140960795 + 262847 * 2 ^ 59
def prefixEnd_262847 : Nat := 4983230072969 + 3 ^ 40 * 262847 * 2
def baseEnd_262847 : Nat := 44988949864146114534565

theorem tailTrace_262847 : CollatzResearch.WordTrace tailWord_262847 prefixEnd_262847 44988949864146114534565 := by
  unfold tailWord_262847
  simp only [CollatzResearch.WordTrace]
  refine ⟨9586817678757684538778795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6391211785838456359185863 9586817678757684538778795)
  ·
    refine ⟨14380226518136526808168193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9586817678757684538778795 14380226518136526808168193)
    ·
      refine ⟨10785169888602395106126145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14380226518136526808168193 10785169888602395106126145)
      ·
        refine ⟨8088877416451796329594609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10785169888602395106126145 8088877416451796329594609)
        ·
          refine ⟨6066658062338847247195957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8088877416451796329594609 6066658062338847247195957)
          ·
            refine ⟨568749193344266929424621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6066658062338847247195957 568749193344266929424621)
            ·
              refine ⟨213280947504100098534233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568749193344266929424621 213280947504100098534233)
              ·
                refine ⟨159960710628075073900675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213280947504100098534233 159960710628075073900675)
                ·
                  refine ⟨239941065942112610851013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159960710628075073900675 239941065942112610851013)
                  ·
                    refine ⟨44988949864146114534565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239941065942112610851013 44988949864146114534565)
                    ·
                      rfl

theorem cell23_262847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 1, 4].length) (baseStart_262847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262847 prefixEnd_262847 := by exact prefixLift 262847
  have htrace : WordTrace (prefixWord ++ tailWord_262847) baseStart_262847 baseEnd_262847 := by
    simpa [prefixWord, tailWord_262847, baseEnd_262847] using wordTrace_append hprefix tailTrace_262847
  have hstable : (prefixWord ++ tailWord_262847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262847).length < 2 ^ (prefixWord ++ tailWord_262847).sum := by decide
  have hdescent : baseEnd_262847 < baseStart_262847 := by decide
  rcases family_descends (prefixWord ++ tailWord_262847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262860 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 6]
def baseStart_262860 : Nat := 118140960795 + 262860 * 2 ^ 59
def prefixEnd_262860 : Nat := 4983230072969 + 3 ^ 40 * 262860 * 2
def baseEnd_262860 : Nat := 14997058315660754749015

theorem tailTrace_262860 : CollatzResearch.WordTrace tailWord_262860 prefixEnd_262860 14997058315660754749015 := by
  unfold tailWord_262860
  simp only [CollatzResearch.WordTrace]
  refine ⟨4793645913855293879501017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6391527885140391839334689 4793645913855293879501017)
  ·
    refine ⟨3595234435391470409625763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4793645913855293879501017 3595234435391470409625763)
    ·
      refine ⟨5392851653087205614438645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3595234435391470409625763 5392851653087205614438645)
      ·
        refine ⟨505579842476925526353623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5392851653087205614438645 505579842476925526353623)
        ·
          refine ⟨758369763715388289530435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505579842476925526353623 758369763715388289530435)
          ·
            refine ⟨1137554645573082434295653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758369763715388289530435 1137554645573082434295653)
            ·
              refine ⟨213291496044952956430435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1137554645573082434295653 213291496044952956430435)
              ·
                refine ⟨319937244067429434645653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213291496044952956430435 319937244067429434645653)
                ·
                  refine ⟨14997058315660754749015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 319937244067429434645653 14997058315660754749015)
                  ·
                    rfl

theorem cell23_262860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_262860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262860 prefixEnd_262860 := by exact prefixLift 262860
  have htrace : WordTrace (prefixWord ++ tailWord_262860) baseStart_262860 baseEnd_262860 := by
    simpa [prefixWord, tailWord_262860, baseEnd_262860] using wordTrace_append hprefix tailTrace_262860
  have hstable : (prefixWord ++ tailWord_262860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262860).length < 2 ^ (prefixWord ++ tailWord_262860).sum := by decide
  have hdescent : baseEnd_262860 < baseStart_262860 := by decide
  rcases family_descends (prefixWord ++ tailWord_262860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262906 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_262906 : Nat := 118140960795 + 262906 * 2 ^ 59
def prefixEnd_262906 : Nat := 4983230072969 + 3 ^ 40 * 262906 * 2
def baseEnd_262906 : Nat := 134997144951053612765923

theorem tailTrace_262906 : CollatzResearch.WordTrace tailWord_262906 prefixEnd_262906 134997144951053612765923 := by
  unfold tailWord_262906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2397242396385984403794143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6392646390362625076784381 2397242396385984403794143)
  ·
    refine ⟨3595863594578976605691215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2397242396385984403794143 3595863594578976605691215)
    ·
      refine ⟨5393795391868464908536823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3595863594578976605691215 5393795391868464908536823)
      ·
        refine ⟨8090693087802697362805235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5393795391868464908536823 8090693087802697362805235)
        ·
          refine ⟨12136039631704046044207853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8090693087802697362805235 12136039631704046044207853)
          ·
            refine ⟨4551014861889017266577945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12136039631704046044207853 4551014861889017266577945)
            ·
              refine ⟨3413261146416762949933459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4551014861889017266577945 3413261146416762949933459)
              ·
                refine ⟨5119891719625144424900189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3413261146416762949933459 5119891719625144424900189)
                ·
                  refine ⟨1919959394859429159337571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5119891719625144424900189 1919959394859429159337571)
                  ·
                    refine ⟨2879939092289143739006357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1919959394859429159337571 2879939092289143739006357)
                    ·
                      refine ⟨134997144951053612765923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2879939092289143739006357 134997144951053612765923)
                      ·
                        rfl

theorem cell23_262906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_262906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262906 prefixEnd_262906 := by exact prefixLift 262906
  have htrace : WordTrace (prefixWord ++ tailWord_262906) baseStart_262906 baseEnd_262906 := by
    simpa [prefixWord, tailWord_262906, baseEnd_262906] using wordTrace_append hprefix tailTrace_262906
  have hstable : (prefixWord ++ tailWord_262906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262906).length < 2 ^ (prefixWord ++ tailWord_262906).sum := by decide
  have hdescent : baseEnd_262906 < baseStart_262906 := by decide
  rcases family_descends (prefixWord ++ tailWord_262906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262910 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_262910 : Nat := 118140960795 + 262910 * 2 ^ 59
def prefixEnd_262910 : Nat := 4983230072969 + 3 ^ 40 * 262910 * 2
def baseEnd_262910 : Nat := 134999198873671597115905

theorem tailTrace_262910 : CollatzResearch.WordTrace tailWord_262910 prefixEnd_262910 134999198873671597115905 := by
  unfold tailWord_262910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198639434691180787290273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6392743651686297532214789 1198639434691180787290273)
  ·
    refine ⟨898979576018385590467705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1198639434691180787290273 898979576018385590467705)
    ·
      refine ⟨674234682013789192850779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 898979576018385590467705 674234682013789192850779)
      ·
        refine ⟨1011352023020683789276169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674234682013789192850779 1011352023020683789276169)
        ·
          refine ⟨758514017265512841957127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011352023020683789276169 758514017265512841957127)
          ·
            refine ⟨1137771025898269262935691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758514017265512841957127 1137771025898269262935691)
            ·
              refine ⟨1706656538847403894403537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137771025898269262935691 1706656538847403894403537)
              ·
                refine ⟨1279992404135552920802653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1706656538847403894403537 1279992404135552920802653)
                ·
                  refine ⟨479997151550832345300995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1279992404135552920802653 479997151550832345300995)
                  ·
                    refine ⟨719995727326248517951493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 479997151550832345300995 719995727326248517951493)
                    ·
                      refine ⟨134999198873671597115905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 719995727326248517951493 134999198873671597115905)
                      ·
                        rfl

theorem cell23_262910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_262910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262910 prefixEnd_262910 := by exact prefixLift 262910
  have htrace : WordTrace (prefixWord ++ tailWord_262910) baseStart_262910 baseEnd_262910 := by
    simpa [prefixWord, tailWord_262910, baseEnd_262910] using wordTrace_append hprefix tailTrace_262910
  have hstable : (prefixWord ++ tailWord_262910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262910).length < 2 ^ (prefixWord ++ tailWord_262910).sum := by decide
  have hdescent : baseEnd_262910 < baseStart_262910 := by decide
  rcases family_descends (prefixWord ++ tailWord_262910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262920 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 2, 4]
def baseStart_262920 : Nat := 118140960795 + 262920 * 2 ^ 59
def prefixEnd_262920 : Nat := 4983230072969 + 3 ^ 40 * 262920 * 2
def baseEnd_262920 : Nat := 45001444560072185996953

theorem tailTrace_262920 : CollatzResearch.WordTrace tailWord_262920 prefixEnd_262920 45001444560072185996953 := by
  unfold tailWord_262920
  simp only [CollatzResearch.WordTrace]
  refine ⟨4794740103746609003093107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6392986804995478670790809 4794740103746609003093107)
  ·
    refine ⟨7192110155619913504639661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4794740103746609003093107 7192110155619913504639661)
    ·
      refine ⟨2697041308357467564239873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7192110155619913504639661 2697041308357467564239873)
      ·
        refine ⟨2022780981268100673179905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2697041308357467564239873 2022780981268100673179905)
        ·
          refine ⟨1517085735951075504884929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022780981268100673179905 1517085735951075504884929)
          ·
            refine ⟨1137814301963306628663697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1517085735951075504884929 1137814301963306628663697)
            ·
              refine ⟨853360726472479971497773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1137814301963306628663697 853360726472479971497773)
              ·
                refine ⟨320010272427179989311665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 853360726472479971497773 320010272427179989311665)
                ·
                  refine ⟨240007704320384991983749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320010272427179989311665 240007704320384991983749)
                  ·
                    refine ⟨45001444560072185996953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240007704320384991983749 45001444560072185996953)
                    ·
                      rfl

theorem cell23_262920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_262920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262920 prefixEnd_262920 := by exact prefixLift 262920
  have htrace : WordTrace (prefixWord ++ tailWord_262920) baseStart_262920 baseEnd_262920 := by
    simpa [prefixWord, tailWord_262920, baseEnd_262920] using wordTrace_append hprefix tailTrace_262920
  have hstable : (prefixWord ++ tailWord_262920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262920).length < 2 ^ (prefixWord ++ tailWord_262920).sum := by decide
  have hdescent : baseEnd_262920 < baseStart_262920 := by decide
  rcases family_descends (prefixWord ++ tailWord_262920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262933 : List Nat := [1, 3, 2, 1, 2, 2, 5, 7]
def baseStart_262933 : Nat := 118140960795 + 262933 * 2 ^ 59
def prefixEnd_262933 : Nat := 4983230072969 + 3 ^ 40 * 262933 * 2
def baseEnd_262933 : Nat := 5000407738100926189937

theorem tailTrace_262933 : CollatzResearch.WordTrace tailWord_262933 prefixEnd_262933 5000407738100926189937 := by
  unfold tailWord_262933
  simp only [CollatzResearch.WordTrace]
  refine ⟨9589954356446121226409453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6393302904297414150939635 9589954356446121226409453)
  ·
    refine ⟨3596232883667295459903545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9589954356446121226409453 3596232883667295459903545)
    ·
      refine ⟨2697174662750471594927659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3596232883667295459903545 2697174662750471594927659)
      ·
        refine ⟨4045761994125707392391489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697174662750471594927659 4045761994125707392391489)
        ·
          refine ⟨3034321495594280544293617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4045761994125707392391489 3034321495594280544293617)
          ·
            refine ⟨2275741121695710408220213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3034321495594280544293617 2275741121695710408220213)
            ·
              refine ⟨213350730158972850770645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2275741121695710408220213 213350730158972850770645)
              ·
                refine ⟨5000407738100926189937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 213350730158972850770645 5000407738100926189937)
                ·
                  rfl

theorem cell23_262933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 7].length) (baseStart_262933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262933 prefixEnd_262933 := by exact prefixLift 262933
  have htrace : WordTrace (prefixWord ++ tailWord_262933) baseStart_262933 baseEnd_262933 := by
    simpa [prefixWord, tailWord_262933, baseEnd_262933] using wordTrace_append hprefix tailTrace_262933
  have hstable : (prefixWord ++ tailWord_262933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262933).length < 2 ^ (prefixWord ++ tailWord_262933).sum := by decide
  have hdescent : baseEnd_262933 < baseStart_262933 := by decide
  rcases family_descends (prefixWord ++ tailWord_262933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262941 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_262941 : Nat := 118140960795 + 262941 * 2 ^ 59
def prefixEnd_262941 : Nat := 4983230072969 + 3 ^ 40 * 262941 * 2
def baseEnd_262941 : Nat := 45005038924653658609421

theorem tailTrace_262941 : CollatzResearch.WordTrace tailWord_262941 prefixEnd_262941 45005038924653658609421 := by
  unfold tailWord_262941
  simp only [CollatzResearch.WordTrace]
  refine ⟨9590246140417138592700677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6393497426944759061800451 9590246140417138592700677)
  ·
    refine ⟨1798171151328213486131377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9590246140417138592700677 1798171151328213486131377)
    ·
      refine ⟨1348628363496160114598533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1798171151328213486131377 1348628363496160114598533)
      ·
        refine ⟨252867818155530021487225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1348628363496160114598533 252867818155530021487225)
        ·
          refine ⟨189650863616647516115419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252867818155530021487225 189650863616647516115419)
          ·
            refine ⟨284476295424971274173129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189650863616647516115419 284476295424971274173129)
            ·
              refine ⟨213357221568728455629847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284476295424971274173129 213357221568728455629847)
              ·
                refine ⟨320035832353092683444771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213357221568728455629847 320035832353092683444771)
                ·
                  refine ⟨480053748529639025167157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320035832353092683444771 480053748529639025167157)
                  ·
                    refine ⟨45005038924653658609421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 480053748529639025167157 45005038924653658609421)
                    ·
                      rfl

theorem cell23_262941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_262941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262941 prefixEnd_262941 := by exact prefixLift 262941
  have htrace : WordTrace (prefixWord ++ tailWord_262941) baseStart_262941 baseEnd_262941 := by
    simpa [prefixWord, tailWord_262941, baseEnd_262941] using wordTrace_append hprefix tailTrace_262941
  have hstable : (prefixWord ++ tailWord_262941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262941).length < 2 ^ (prefixWord ++ tailWord_262941).sum := by decide
  have hdescent : baseEnd_262941 < baseStart_262941 := by decide
  rcases family_descends (prefixWord ++ tailWord_262941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262944 : List Nat := [2, 1, 1, 5, 1, 2, 1, 5, 1, 2, 2]
def baseStart_262944 : Nat := 118140960795 + 262944 * 2 ^ 59
def prefixEnd_262944 : Nat := 4983230072969 + 3 ^ 40 * 262944 * 2
def baseEnd_262944 : Nat := 135016657215924464090749

theorem tailTrace_262944 : CollatzResearch.WordTrace tailWord_262944 prefixEnd_262944 135016657215924464090749 := by
  unfold tailWord_262944
  simp only [CollatzResearch.WordTrace]
  refine ⟨4795177779703135052529943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6393570372937513403373257 4795177779703135052529943)
  ·
    refine ⟨7192766669554702578794915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4795177779703135052529943 7192766669554702578794915)
    ·
      refine ⟨10789150004332053868192373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7192766669554702578794915 10789150004332053868192373)
      ·
        refine ⟨1011482812906130050143035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10789150004332053868192373 1011482812906130050143035)
        ·
          refine ⟨1517224219359195075214553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011482812906130050143035 1517224219359195075214553)
          ·
            refine ⟨1137918164519396306410915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1517224219359195075214553 1137918164519396306410915)
            ·
              refine ⟨1706877246779094459616373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137918164519396306410915 1706877246779094459616373)
              ·
                refine ⟨160019741885540105589035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1706877246779094459616373 160019741885540105589035)
                ·
                  refine ⟨240029612828310158383553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160019741885540105589035 240029612828310158383553)
                  ·
                    refine ⟨180022209621232618787665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240029612828310158383553 180022209621232618787665)
                    ·
                      refine ⟨135016657215924464090749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180022209621232618787665 135016657215924464090749)
                      ·
                        rfl

theorem cell23_262944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_262944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262944 prefixEnd_262944 := by exact prefixLift 262944
  have htrace : WordTrace (prefixWord ++ tailWord_262944) baseStart_262944 baseEnd_262944 := by
    simpa [prefixWord, tailWord_262944, baseEnd_262944] using wordTrace_append hprefix tailTrace_262944
  have hstable : (prefixWord ++ tailWord_262944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262944).length < 2 ^ (prefixWord ++ tailWord_262944).sum := by decide
  have hdescent : baseEnd_262944 < baseStart_262944 := by decide
  rcases family_descends (prefixWord ++ tailWord_262944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262974 : List Nat := [4, 2, 1, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_262974 : Nat := 118140960795 + 262974 * 2 ^ 59
def prefixEnd_262974 : Nat := 4983230072969 + 3 ^ 40 * 262974 * 2
def baseEnd_262974 : Nat := 135032061635559346715611

theorem tailTrace_262974 : CollatzResearch.WordTrace tailWord_262974 prefixEnd_262974 135032061635559346715611 := by
  unfold tailWord_262974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198931218662198153581497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6394299832865056819101317 1198931218662198153581497)
  ·
    refine ⟨899198413996648615186123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1198931218662198153581497 899198413996648615186123)
    ·
      refine ⟨1348797620994972922779185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899198413996648615186123 1348797620994972922779185)
      ·
        refine ⟨1011598215746229692084389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1348797620994972922779185 1011598215746229692084389)
        ·
          refine ⟨189674665452418067265823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1011598215746229692084389 189674665452418067265823)
          ·
            refine ⟨284511998178627100898735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189674665452418067265823 284511998178627100898735)
            ·
              refine ⟨426767997267940651348103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284511998178627100898735 426767997267940651348103)
              ·
                refine ⟨640151995901910977022155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426767997267940651348103 640151995901910977022155)
                ·
                  refine ⟨960227993852866465533233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640151995901910977022155 960227993852866465533233)
                  ·
                    refine ⟨720170995389649849149925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 960227993852866465533233 720170995389649849149925)
                    ·
                      refine ⟨135032061635559346715611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 720170995389649849149925 135032061635559346715611)
                      ·
                        rfl

theorem cell23_262974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_262974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_262974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_262974 prefixEnd_262974 := by exact prefixLift 262974
  have htrace : WordTrace (prefixWord ++ tailWord_262974) baseStart_262974 baseEnd_262974 := by
    simpa [prefixWord, tailWord_262974, baseEnd_262974] using wordTrace_append hprefix tailTrace_262974
  have hstable : (prefixWord ++ tailWord_262974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262974).length < 2 ^ (prefixWord ++ tailWord_262974).sum := by decide
  have hdescent : baseEnd_262974 < baseStart_262974 := by decide
  rcases family_descends (prefixWord ++ tailWord_262974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263000 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 1, 4, 2]
def baseStart_263000 : Nat := 118140960795 + 263000 * 2 ^ 59
def prefixEnd_263000 : Nat := 4983230072969 + 3 ^ 40 * 263000 * 2
def baseEnd_263000 : Nat := 135045412132576244990491

theorem tailTrace_263000 : CollatzResearch.WordTrace tailWord_263000 prefixEnd_263000 135045412132576244990491 := by
  unfold tailWord_263000
  simp only [CollatzResearch.WordTrace]
  refine ⟨4796199023601695834549227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6394932031468927779398969 4796199023601695834549227)
  ·
    refine ⟨7194298535402543751823841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4796199023601695834549227 7194298535402543751823841)
    ·
      refine ⟨5395723901551907813867881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7194298535402543751823841 5395723901551907813867881)
      ·
        refine ⟨4046792926163930860400911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5395723901551907813867881 4046792926163930860400911)
        ·
          refine ⟨6070189389245896290601367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4046792926163930860400911 6070189389245896290601367)
          ·
            refine ⟨9105284083868844435902051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6070189389245896290601367 9105284083868844435902051)
            ·
              refine ⟨13657926125803266653853077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9105284083868844435902051 13657926125803266653853077)
              ·
                refine ⟨640215287147028124399363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13657926125803266653853077 640215287147028124399363)
                ·
                  refine ⟨960322930720542186599045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640215287147028124399363 960322930720542186599045)
                  ·
                    refine ⟨180060549510101659987321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 960322930720542186599045 180060549510101659987321)
                    ·
                      refine ⟨135045412132576244990491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180060549510101659987321 135045412132576244990491)
                      ·
                        rfl

theorem cell23_263000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_263000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263000 prefixEnd_263000 := by exact prefixLift 263000
  have htrace : WordTrace (prefixWord ++ tailWord_263000) baseStart_263000 baseEnd_263000 := by
    simpa [prefixWord, tailWord_263000, baseEnd_263000] using wordTrace_append hprefix tailTrace_263000
  have hstable : (prefixWord ++ tailWord_263000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263000).length < 2 ^ (prefixWord ++ tailWord_263000).sum := by decide
  have hdescent : baseEnd_263000 < baseStart_263000 := by decide
  rcases family_descends (prefixWord ++ tailWord_263000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263004 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_263004 : Nat := 118140960795 + 263004 * 2 ^ 59
def prefixEnd_263004 : Nat := 4983230072969 + 3 ^ 40 * 263004 * 2
def baseEnd_263004 : Nat := 135047466055194229340473

theorem tailTrace_263004 : CollatzResearch.WordTrace tailWord_263004 prefixEnd_263004 135047466055194229340473 := by
  unfold tailWord_263004
  simp only [CollatzResearch.WordTrace]
  refine ⟨4796271969594450176122033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6395029292792600234829377 4796271969594450176122033)
  ·
    refine ⟨3597203977195837632091525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4796271969594450176122033 3597203977195837632091525)
    ·
      refine ⟨674475745724219556017161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3597203977195837632091525 674475745724219556017161)
      ·
        refine ⟨505856809293164667012871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674475745724219556017161 505856809293164667012871)
        ·
          refine ⟨758785213939747000519307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505856809293164667012871 758785213939747000519307)
          ·
            refine ⟨1138177820909620500778961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758785213939747000519307 1138177820909620500778961)
            ·
              refine ⟨853633365682215375584221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138177820909620500778961 853633365682215375584221)
              ·
                refine ⟨320112512130830765844083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 853633365682215375584221 320112512130830765844083)
                ·
                  refine ⟨480168768196246148766125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320112512130830765844083 480168768196246148766125)
                  ·
                    refine ⟨180063288073592305787297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 480168768196246148766125 180063288073592305787297)
                    ·
                      refine ⟨135047466055194229340473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180063288073592305787297 135047466055194229340473)
                      ·
                        rfl

theorem cell23_263004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_263004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263004 prefixEnd_263004 := by exact prefixLift 263004
  have htrace : WordTrace (prefixWord ++ tailWord_263004) baseStart_263004 baseEnd_263004 := by
    simpa [prefixWord, tailWord_263004, baseEnd_263004] using wordTrace_append hprefix tailTrace_263004
  have hstable : (prefixWord ++ tailWord_263004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263004).length < 2 ^ (prefixWord ++ tailWord_263004).sum := by decide
  have hdescent : baseEnd_263004 < baseStart_263004 := by decide
  rcases family_descends (prefixWord ++ tailWord_263004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263013 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_263013 : Nat := 118140960795 + 263013 * 2 ^ 59
def prefixEnd_263013 : Nat := 4983230072969 + 3 ^ 40 * 263013 * 2
def baseEnd_263013 : Nat := 135052087381084694127931

theorem tailTrace_263013 : CollatzResearch.WordTrace tailWord_263013 prefixEnd_263013 135052087381084694127931 := by
  unfold tailWord_263013
  simp only [CollatzResearch.WordTrace]
  refine ⟨9592872196156294889321693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6395248130770863259547795 9592872196156294889321693)
  ·
    refine ⟨3597327073558610583495635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9592872196156294889321693 3597327073558610583495635)
    ·
      refine ⟨5395990610337915875243453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3597327073558610583495635 5395990610337915875243453)
      ·
        refine ⟨2023496478876718453216295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5395990610337915875243453 2023496478876718453216295)
        ·
          refine ⟨3035244718315077679824443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023496478876718453216295 3035244718315077679824443)
          ·
            refine ⟨4552867077472616519736665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3035244718315077679824443 4552867077472616519736665)
            ·
              refine ⟨3414650308104462389802499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4552867077472616519736665 3414650308104462389802499)
              ·
                refine ⟨5121975462156693584703749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3414650308104462389802499 5121975462156693584703749)
                ·
                  refine ⟨960370399154380047131953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5121975462156693584703749 960370399154380047131953)
                  ·
                    refine ⟨720277799365785035348965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 960370399154380047131953 720277799365785035348965)
                    ·
                      refine ⟨135052087381084694127931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 720277799365785035348965 135052087381084694127931)
                      ·
                        rfl

theorem cell23_263013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_263013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263013 prefixEnd_263013 := by exact prefixLift 263013
  have htrace : WordTrace (prefixWord ++ tailWord_263013) baseStart_263013 baseEnd_263013 := by
    simpa [prefixWord, tailWord_263013, baseEnd_263013] using wordTrace_append hprefix tailTrace_263013
  have hstable : (prefixWord ++ tailWord_263013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263013).length < 2 ^ (prefixWord ++ tailWord_263013).sum := by decide
  have hdescent : baseEnd_263013 < baseStart_263013 := by decide
  rcases family_descends (prefixWord ++ tailWord_263013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263038 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_263038 : Nat := 118140960795 + 263038 * 2 ^ 59
def prefixEnd_263038 : Nat := 4983230072969 + 3 ^ 40 * 263038 * 2
def baseEnd_263038 : Nat := 135064924397447096315317

theorem tailTrace_263038 : CollatzResearch.WordTrace tailWord_263038 prefixEnd_263038 135064924397447096315317 := by
  unfold tailWord_263038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1199223002633215519872721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6395856014043816105987845 1199223002633215519872721)
  ·
    refine ⟨899417251974911639904541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1199223002633215519872721 899417251974911639904541)
    ·
      refine ⟨337281469490591864964203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 899417251974911639904541 337281469490591864964203)
      ·
        refine ⟨505922204235887797446305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337281469490591864964203 505922204235887797446305)
        ·
          refine ⟨379441653176915848084729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505922204235887797446305 379441653176915848084729)
          ·
            refine ⟨284581239882686886063547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379441653176915848084729 284581239882686886063547)
            ·
              refine ⟨426871859824030329095321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284581239882686886063547 426871859824030329095321)
              ·
                refine ⟨320153894868022746821491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426871859824030329095321 320153894868022746821491)
                ·
                  refine ⟨480230842302034120232237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320153894868022746821491 480230842302034120232237)
                  ·
                    refine ⟨180086565863262795087089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 480230842302034120232237 180086565863262795087089)
                    ·
                      refine ⟨135064924397447096315317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180086565863262795087089 135064924397447096315317)
                      ·
                        rfl

theorem cell23_263038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_263038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263038 prefixEnd_263038 := by exact prefixLift 263038
  have htrace : WordTrace (prefixWord ++ tailWord_263038) baseStart_263038 baseEnd_263038 := by
    simpa [prefixWord, tailWord_263038, baseEnd_263038] using wordTrace_append hprefix tailTrace_263038
  have hstable : (prefixWord ++ tailWord_263038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263038).length < 2 ^ (prefixWord ++ tailWord_263038).sum := by decide
  have hdescent : baseEnd_263038 < baseStart_263038 := by decide
  rcases family_descends (prefixWord ++ tailWord_263038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263063 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_263063 : Nat := 118140960795 + 263063 * 2 ^ 59
def prefixEnd_263063 : Nat := 4983230072969 + 3 ^ 40 * 263063 * 2
def baseEnd_263063 : Nat := 135077761413809498502701

theorem tailTrace_263063 : CollatzResearch.WordTrace tailWord_263063 prefixEnd_263063 135077761413809498502701 := by
  unfold tailWord_263063
  simp only [CollatzResearch.WordTrace]
  refine ⟨9594695845975153428641843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6396463897316768952427895 9594695845975153428641843)
  ·
    refine ⟨14392043768962730142962765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9594695845975153428641843 14392043768962730142962765)
    ·
      refine ⟨5397016413361023803611037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14392043768962730142962765 5397016413361023803611037)
      ·
        refine ⟨2023881155010383926354139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5397016413361023803611037 2023881155010383926354139)
        ·
          refine ⟨3035821732515575889531209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023881155010383926354139 3035821732515575889531209)
          ·
            refine ⟨2276866299386681917148407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3035821732515575889531209 2276866299386681917148407)
            ·
              refine ⟨3415299449080022875722611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276866299386681917148407 3415299449080022875722611)
              ·
                refine ⟨5122949173620034313583917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3415299449080022875722611 5122949173620034313583917)
                ·
                  refine ⟨1921105940107512867593969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5122949173620034313583917 1921105940107512867593969)
                  ·
                    refine ⟨1440829455080634650695477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1921105940107512867593969 1440829455080634650695477)
                    ·
                      refine ⟨135077761413809498502701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1440829455080634650695477 135077761413809498502701)
                      ·
                        rfl

theorem cell23_263063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_263063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263063 prefixEnd_263063 := by exact prefixLift 263063
  have htrace : WordTrace (prefixWord ++ tailWord_263063) baseStart_263063 baseEnd_263063 := by
    simpa [prefixWord, tailWord_263063, baseEnd_263063] using wordTrace_append hprefix tailTrace_263063
  have hstable : (prefixWord ++ tailWord_263063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263063).length < 2 ^ (prefixWord ++ tailWord_263063).sum := by decide
  have hdescent : baseEnd_263063 < baseStart_263063 := by decide
  rcases family_descends (prefixWord ++ tailWord_263063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263074 : List Nat := [3, 3, 1, 2, 2, 1, 4, 2, 5]
def baseStart_263074 : Nat := 118140960795 + 263074 * 2 ^ 59
def prefixEnd_263074 : Nat := 4983230072969 + 3 ^ 40 * 263074 * 2
def baseEnd_263074 : Nat := 15009267744556550607239

theorem tailTrace_263074 : CollatzResearch.WordTrace tailWord_263074 prefixEnd_263074 15009267744556550607239 := by
  unfold tailWord_263074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398774262233825576823069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6396731365956868204861517 2398774262233825576823069)
  ·
    refine ⟨899540348337684591308651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2398774262233825576823069 899540348337684591308651)
    ·
      refine ⟨1349310522506526886962977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899540348337684591308651 1349310522506526886962977)
      ·
        refine ⟨1011982891879895165222233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1349310522506526886962977 1011982891879895165222233)
        ·
          refine ⟨758987168909921373916675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011982891879895165222233 758987168909921373916675)
          ·
            refine ⟨1138480753364882060875013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758987168909921373916675 1138480753364882060875013)
            ·
              refine ⟨213465141255915386414065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1138480753364882060875013 213465141255915386414065)
              ·
                refine ⟨160098855941936539810549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213465141255915386414065 160098855941936539810549)
                ·
                  refine ⟨15009267744556550607239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160098855941936539810549 15009267744556550607239)
                  ·
                    rfl

theorem cell23_263074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_263074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263074 prefixEnd_263074 := by exact prefixLift 263074
  have htrace : WordTrace (prefixWord ++ tailWord_263074) baseStart_263074 baseEnd_263074 := by
    simpa [prefixWord, tailWord_263074, baseEnd_263074] using wordTrace_append hprefix tailTrace_263074
  have hstable : (prefixWord ++ tailWord_263074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263074).length < 2 ^ (prefixWord ++ tailWord_263074).sum := by decide
  have hdescent : baseEnd_263074 < baseStart_263074 := by decide
  rcases family_descends (prefixWord ++ tailWord_263074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263103 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 4]
def baseStart_263103 : Nat := 118140960795 + 263103 * 2 ^ 59
def prefixEnd_263103 : Nat := 4983230072969 + 3 ^ 40 * 263103 * 2
def baseEnd_263103 : Nat := 135098300639989342002517

theorem tailTrace_263103 : CollatzResearch.WordTrace tailWord_263103 prefixEnd_263103 135098300639989342002517 := by
  unfold tailWord_263103
  simp only [CollatzResearch.WordTrace]
  refine ⟨9596154765830240260097963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6397436510553493506731975 9596154765830240260097963)
  ·
    refine ⟨14394232148745360390146945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9596154765830240260097963 14394232148745360390146945)
    ·
      refine ⟨10795674111559020292610209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14394232148745360390146945 10795674111559020292610209)
      ·
        refine ⟨8096755583669265219457657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10795674111559020292610209 8096755583669265219457657)
        ·
          refine ⟨6072566687751948914593243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8096755583669265219457657 6072566687751948914593243)
          ·
            refine ⟨9108850031627923371889865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6072566687751948914593243 9108850031627923371889865)
            ·
              refine ⟨6831637523720942528917399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9108850031627923371889865 6831637523720942528917399)
              ·
                refine ⟨10247456285581413793376099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6831637523720942528917399 10247456285581413793376099)
                ·
                  refine ⟨15371184428372120690064149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10247456285581413793376099 15371184428372120690064149)
                  ·
                    refine ⟨720524270079943157346757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15371184428372120690064149 720524270079943157346757)
                    ·
                      refine ⟨135098300639989342002517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 720524270079943157346757 135098300639989342002517)
                      ·
                        rfl

theorem cell23_263103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_263103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263103 prefixEnd_263103 := by exact prefixLift 263103
  have htrace : WordTrace (prefixWord ++ tailWord_263103) baseStart_263103 baseEnd_263103 := by
    simpa [prefixWord, tailWord_263103, baseEnd_263103] using wordTrace_append hprefix tailTrace_263103
  have hstable : (prefixWord ++ tailWord_263103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263103).length < 2 ^ (prefixWord ++ tailWord_263103).sum := by decide
  have hdescent : baseEnd_263103 < baseStart_263103 := by decide
  rcases family_descends (prefixWord ++ tailWord_263103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263130 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 8]
def baseStart_263130 : Nat := 118140960795 + 263130 * 2 ^ 59
def prefixEnd_263130 : Nat := 4983230072969 + 3 ^ 40 * 263130 * 2
def baseEnd_263130 : Nat := 15012462735295637373877

theorem tailTrace_263130 : CollatzResearch.WordTrace tailWord_263130 prefixEnd_263130 15012462735295637373877 := by
  unfold tailWord_263130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2399284884183105967832711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6398093024488282580887229 2399284884183105967832711)
  ·
    refine ⟨3598927326274658951749067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2399284884183105967832711 3598927326274658951749067)
    ·
      refine ⟨5398390989411988427623601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3598927326274658951749067 5398390989411988427623601)
      ·
        refine ⟨4048793242058991320717701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5398390989411988427623601 4048793242058991320717701)
        ·
          refine ⟨759148732886060872634569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4048793242058991320717701 759148732886060872634569)
          ·
            refine ⟨569361549664545654475927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759148732886060872634569 569361549664545654475927)
            ·
              refine ⟨854042324496818481713891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569361549664545654475927 854042324496818481713891)
              ·
                refine ⟨1281063486745227722570837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854042324496818481713891 1281063486745227722570837)
                ·
                  refine ⟨15012462735295637373877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1281063486745227722570837 15012462735295637373877)
                  ·
                    rfl

theorem cell23_263130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_263130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263130 prefixEnd_263130 := by exact prefixLift 263130
  have htrace : WordTrace (prefixWord ++ tailWord_263130) baseStart_263130 baseEnd_263130 := by
    simpa [prefixWord, tailWord_263130, baseEnd_263130] using wordTrace_append hprefix tailTrace_263130
  have hstable : (prefixWord ++ tailWord_263130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263130).length < 2 ^ (prefixWord ++ tailWord_263130).sum := by decide
  have hdescent : baseEnd_263130 < baseStart_263130 := by decide
  rcases family_descends (prefixWord ++ tailWord_263130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263191 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 3, 1, 3]
def baseStart_263191 : Nat := 118140960795 + 263191 * 2 ^ 59
def prefixEnd_263191 : Nat := 4983230072969 + 3 ^ 40 * 263191 * 2
def baseEnd_263191 : Nat := 135143486937584997702113

theorem tailTrace_263191 : CollatzResearch.WordTrace tailWord_263191 prefixEnd_263191 135143486937584997702113 := by
  unfold tailWord_263191
  simp only [CollatzResearch.WordTrace]
  refine ⟨9599364389511431289301427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6399576259674287526200951 9599364389511431289301427)
  ·
    refine ⟨14399046584267146933952141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9599364389511431289301427 14399046584267146933952141)
    ·
      refine ⟨5399642469100180100232053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14399046584267146933952141 5399642469100180100232053)
      ·
        refine ⟨506216481478141884396755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5399642469100180100232053 506216481478141884396755)
        ·
          refine ⟨759324722217212826595133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506216481478141884396755 759324722217212826595133)
          ·
            refine ⟨284746770831454809973175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759324722217212826595133 284746770831454809973175)
            ·
              refine ⟨427120156247182214959763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284746770831454809973175 427120156247182214959763)
              ·
                refine ⟨640680234370773322439645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427120156247182214959763 640680234370773322439645)
                ·
                  refine ⟨240255087889039995914867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640680234370773322439645 240255087889039995914867)
                  ·
                    refine ⟨360382631833559993872301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 240255087889039995914867 360382631833559993872301)
                    ·
                      refine ⟨135143486937584997702113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 360382631833559993872301 135143486937584997702113)
                      ·
                        rfl

theorem cell23_263191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_263191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263191 prefixEnd_263191 := by exact prefixLift 263191
  have htrace : WordTrace (prefixWord ++ tailWord_263191) baseStart_263191 baseEnd_263191 := by
    simpa [prefixWord, tailWord_263191, baseEnd_263191] using wordTrace_append hprefix tailTrace_263191
  have hstable : (prefixWord ++ tailWord_263191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263191).length < 2 ^ (prefixWord ++ tailWord_263191).sum := by decide
  have hdescent : baseEnd_263191 < baseStart_263191 := by decide
  rcases family_descends (prefixWord ++ tailWord_263191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263217 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 3, 2, 3]
def baseStart_263217 : Nat := 118140960795 + 263217 * 2 ^ 59
def prefixEnd_263217 : Nat := 4983230072969 + 3 ^ 40 * 263217 * 2
def baseEnd_263217 : Nat := 135156837434601895976993

theorem tailTrace_263217 : CollatzResearch.WordTrace tailWord_263217 prefixEnd_263217 135156837434601895976993 := by
  unfold tailWord_263217
  simp only [CollatzResearch.WordTrace]
  refine ⟨9600312687417237729747905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6400208458278158486498603 9600312687417237729747905)
  ·
    refine ⟨7200234515562928297310929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9600312687417237729747905 7200234515562928297310929)
    ·
      refine ⟨5400175886672196222983197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7200234515562928297310929 5400175886672196222983197)
      ·
        refine ⟨2025065957502073583618699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5400175886672196222983197 2025065957502073583618699)
        ·
          refine ⟨3037598936253110375428049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025065957502073583618699 3037598936253110375428049)
          ·
            refine ⟨2278199202189832781571037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3037598936253110375428049 2278199202189832781571037)
            ·
              refine ⟨854324700821187293089139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2278199202189832781571037 854324700821187293089139)
              ·
                refine ⟨1281487051231780939633709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854324700821187293089139 1281487051231780939633709)
                ·
                  refine ⟨480557644211917852362641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1281487051231780939633709 480557644211917852362641)
                  ·
                    refine ⟨360418233158938389271981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 480557644211917852362641 360418233158938389271981)
                    ·
                      refine ⟨135156837434601895976993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 360418233158938389271981 135156837434601895976993)
                      ·
                        rfl

theorem cell23_263217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_263217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263217 prefixEnd_263217 := by exact prefixLift 263217
  have htrace : WordTrace (prefixWord ++ tailWord_263217) baseStart_263217 baseEnd_263217 := by
    simpa [prefixWord, tailWord_263217, baseEnd_263217] using wordTrace_append hprefix tailTrace_263217
  have hstable : (prefixWord ++ tailWord_263217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263217).length < 2 ^ (prefixWord ++ tailWord_263217).sum := by decide
  have hdescent : baseEnd_263217 < baseStart_263217 := by decide
  rcases family_descends (prefixWord ++ tailWord_263217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263231 : List Nat := [1, 1, 2, 2, 3, 1, 1, 7, 1, 2, 2]
def baseStart_263231 : Nat := 118140960795 + 263231 * 2 ^ 59
def prefixEnd_263231 : Nat := 4983230072969 + 3 ^ 40 * 263231 * 2
def baseEnd_263231 : Nat := 135164026163764841201929

theorem tailTrace_263231 : CollatzResearch.WordTrace tailWord_263231 prefixEnd_263231 135164026163764841201929 := by
  unfold tailWord_263231
  simp only [CollatzResearch.WordTrace]
  refine ⟨9600823309366518120757547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6400548872911012080505031 9600823309366518120757547)
  ·
    refine ⟨14401234964049777181136321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9600823309366518120757547 14401234964049777181136321)
    ·
      refine ⟨10800926223037332885852241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14401234964049777181136321 10800926223037332885852241)
      ·
        refine ⟨8100694667277999664389181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10800926223037332885852241 8100694667277999664389181)
        ·
          refine ⟨3037760500229249874145943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8100694667277999664389181 3037760500229249874145943)
          ·
            refine ⟨4556640750343874811218915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037760500229249874145943 4556640750343874811218915)
            ·
              refine ⟨6834961125515812216828373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4556640750343874811218915 6834961125515812216828373)
              ·
                refine ⟨160194401379276848831915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6834961125515812216828373 160194401379276848831915)
                ·
                  refine ⟨240291602068915273247873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160194401379276848831915 240291602068915273247873)
                  ·
                    refine ⟨180218701551686454935905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240291602068915273247873 180218701551686454935905)
                    ·
                      refine ⟨135164026163764841201929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180218701551686454935905 135164026163764841201929)
                      ·
                        rfl

theorem cell23_263231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 1, 2, 2].length) (baseStart_263231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263231 prefixEnd_263231 := by exact prefixLift 263231
  have htrace : WordTrace (prefixWord ++ tailWord_263231) baseStart_263231 baseEnd_263231 := by
    simpa [prefixWord, tailWord_263231, baseEnd_263231] using wordTrace_append hprefix tailTrace_263231
  have hstable : (prefixWord ++ tailWord_263231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263231).length < 2 ^ (prefixWord ++ tailWord_263231).sum := by decide
  have hdescent : baseEnd_263231 < baseStart_263231 := by decide
  rcases family_descends (prefixWord ++ tailWord_263231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263261 : List Nat := [1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_263261 : Nat := 118140960795 + 263261 * 2 ^ 59
def prefixEnd_263261 : Nat := 4983230072969 + 3 ^ 40 * 263261 * 2
def baseEnd_263261 : Nat := 135179430583399723826791

theorem tailTrace_263261 : CollatzResearch.WordTrace tailWord_263261 prefixEnd_263261 135179430583399723826791 := by
  unfold tailWord_263261
  simp only [CollatzResearch.WordTrace]
  refine ⟨9601917499257833244349637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6401278332838555496233091 9601917499257833244349637)
  ·
    refine ⟨1800359531110843733315557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9601917499257833244349637 1800359531110843733315557)
    ·
      refine ⟨337567412083283199996667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1800359531110843733315557 337567412083283199996667)
      ·
        refine ⟨506351118124924799995001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337567412083283199996667 506351118124924799995001)
        ·
          refine ⟨379763338593693599996251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506351118124924799995001 379763338593693599996251)
          ·
            refine ⟨569645007890540399994377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379763338593693599996251 569645007890540399994377)
            ·
              refine ⟨427233755917905299995783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569645007890540399994377 427233755917905299995783)
              ·
                refine ⟨640850633876857949993675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427233755917905299995783 640850633876857949993675)
                ·
                  refine ⟨961275950815286924990513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640850633876857949993675 961275950815286924990513)
                  ·
                    refine ⟨720956963111465193742885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 961275950815286924990513 720956963111465193742885)
                    ·
                      refine ⟨135179430583399723826791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 720956963111465193742885 135179430583399723826791)
                      ·
                        rfl

theorem cell23_263261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_263261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263261 prefixEnd_263261 := by exact prefixLift 263261
  have htrace : WordTrace (prefixWord ++ tailWord_263261) baseStart_263261 baseEnd_263261 := by
    simpa [prefixWord, tailWord_263261, baseEnd_263261] using wordTrace_append hprefix tailTrace_263261
  have hstable : (prefixWord ++ tailWord_263261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263261).length < 2 ^ (prefixWord ++ tailWord_263261).sum := by decide
  have hdescent : baseEnd_263261 < baseStart_263261 := by decide
  rcases family_descends (prefixWord ++ tailWord_263261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263264 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 2, 1, 3]
def baseStart_263264 : Nat := 118140960795 + 263264 * 2 ^ 59
def prefixEnd_263264 : Nat := 4983230072969 + 3 ^ 40 * 263264 * 2
def baseEnd_263264 : Nat := 135180971025363212089277

theorem tailTrace_263264 : CollatzResearch.WordTrace tailWord_263264 prefixEnd_263264 135180971025363212089277 := by
  unfold tailWord_263264
  simp only [CollatzResearch.WordTrace]
  refine ⟨4801013459123482378354423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6401351278831309837805897 4801013459123482378354423)
  ·
    refine ⟨7201520188685223567531635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4801013459123482378354423 7201520188685223567531635)
    ·
      refine ⟨10802280283027835351297453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7201520188685223567531635 10802280283027835351297453)
      ·
        refine ⟨4050855106135438256736545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10802280283027835351297453 4050855106135438256736545)
        ·
          refine ⟨3038141329601578692552409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4050855106135438256736545 3038141329601578692552409)
          ·
            refine ⟨2278605997201184019414307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3038141329601578692552409 2278605997201184019414307)
            ·
              refine ⟨3417908995801776029121461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278605997201184019414307 3417908995801776029121461)
              ·
                refine ⟨320428968356416502730137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3417908995801776029121461 320428968356416502730137)
                ·
                  refine ⟨240321726267312377047603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320428968356416502730137 240321726267312377047603)
                  ·
                    refine ⟨360482589400968565571405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 240321726267312377047603 360482589400968565571405)
                    ·
                      refine ⟨135180971025363212089277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 360482589400968565571405 135180971025363212089277)
                      ·
                        rfl

theorem cell23_263264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_263264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263264 prefixEnd_263264 := by exact prefixLift 263264
  have htrace : WordTrace (prefixWord ++ tailWord_263264) baseStart_263264 baseEnd_263264 := by
    simpa [prefixWord, tailWord_263264, baseEnd_263264] using wordTrace_append hprefix tailTrace_263264
  have hstable : (prefixWord ++ tailWord_263264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263264).length < 2 ^ (prefixWord ++ tailWord_263264).sum := by decide
  have hdescent : baseEnd_263264 < baseStart_263264 := by decide
  rcases family_descends (prefixWord ++ tailWord_263264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263280 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 1, 8]
def baseStart_263280 : Nat := 118140960795 + 263280 * 2 ^ 59
def prefixEnd_263280 : Nat := 4983230072969 + 3 ^ 40 * 263280 * 2
def baseEnd_263280 : Nat := 45063062238611716496401

theorem tailTrace_263280 : CollatzResearch.WordTrace tailWord_263280 prefixEnd_263280 45063062238611716496401 := by
  unfold tailWord_263280
  simp only [CollatzResearch.WordTrace]
  refine ⟨4801305243094499744645647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6401740324125999659527529 4801305243094499744645647)
  ·
    refine ⟨7201957864641749616968471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4801305243094499744645647 7201957864641749616968471)
    ·
      refine ⟨10802936796962624425452707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7201957864641749616968471 10802936796962624425452707)
      ·
        refine ⟨16204405195443936638179061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10802936796962624425452707 16204405195443936638179061)
        ·
          refine ⟨1519162987072869059829287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16204405195443936638179061 1519162987072869059829287)
          ·
            refine ⟨2278744480609303589743931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519162987072869059829287 2278744480609303589743931)
            ·
              refine ⟨3418116720913955384615897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278744480609303589743931 3418116720913955384615897)
              ·
                refine ⟨2563587540685466538461923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3418116720913955384615897 2563587540685466538461923)
                ·
                  refine ⟨3845381311028199807692885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563587540685466538461923 3845381311028199807692885)
                  ·
                    refine ⟨45063062238611716496401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3845381311028199807692885 45063062238611716496401)
                    ·
                      rfl

theorem cell23_263280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_263280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263280 prefixEnd_263280 := by exact prefixLift 263280
  have htrace : WordTrace (prefixWord ++ tailWord_263280) baseStart_263280 baseEnd_263280 := by
    simpa [prefixWord, tailWord_263280, baseEnd_263280] using wordTrace_append hprefix tailTrace_263280
  have hstable : (prefixWord ++ tailWord_263280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263280).length < 2 ^ (prefixWord ++ tailWord_263280).sum := by decide
  have hdescent : baseEnd_263280 < baseStart_263280 := by decide
  rcases family_descends (prefixWord ++ tailWord_263280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263285 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_263285 : Nat := 118140960795 + 263285 * 2 ^ 59
def prefixEnd_263285 : Nat := 4983230072969 + 3 ^ 40 * 263285 * 2
def baseEnd_263285 : Nat := 135191754119107629926681

theorem tailTrace_263285 : CollatzResearch.WordTrace tailWord_263285 prefixEnd_263285 135191754119107629926681 := by
  unfold tailWord_263285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9602792851170885343223309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6401861900780590228815539 9602792851170885343223309)
  ·
    refine ⟨3601047319189082003708741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9602792851170885343223309 3601047319189082003708741)
    ·
      refine ⟨675196372347952875695389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3601047319189082003708741 675196372347952875695389)
      ·
        refine ⟨253198639630482328385771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 675196372347952875695389 253198639630482328385771)
        ·
          refine ⟨379797959445723492578657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253198639630482328385771 379797959445723492578657)
          ·
            refine ⟨284848469584292619433993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379797959445723492578657 284848469584292619433993)
            ·
              refine ⟨213636352188219464575495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284848469584292619433993 213636352188219464575495)
              ·
                refine ⟨320454528282329196863243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213636352188219464575495 320454528282329196863243)
                ·
                  refine ⟨480681792423493795294865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 320454528282329196863243 480681792423493795294865)
                  ·
                    refine ⟨360511344317620346471149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 480681792423493795294865 360511344317620346471149)
                    ·
                      refine ⟨135191754119107629926681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 360511344317620346471149 135191754119107629926681)
                      ·
                        rfl

theorem cell23_263285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_263285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263285 prefixEnd_263285 := by exact prefixLift 263285
  have htrace : WordTrace (prefixWord ++ tailWord_263285) baseStart_263285 baseEnd_263285 := by
    simpa [prefixWord, tailWord_263285, baseEnd_263285] using wordTrace_append hprefix tailTrace_263285
  have hstable : (prefixWord ++ tailWord_263285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263285).length < 2 ^ (prefixWord ++ tailWord_263285).sum := by decide
  have hdescent : baseEnd_263285 < baseStart_263285 := by decide
  rcases family_descends (prefixWord ++ tailWord_263285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263297 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 2, 6]
def baseStart_263297 : Nat := 118140960795 + 263297 * 2 ^ 59
def prefixEnd_263297 : Nat := 4983230072969 + 3 ^ 40 * 263297 * 2
def baseEnd_263297 : Nat := 45065971962320527658875

theorem tailTrace_263297 : CollatzResearch.WordTrace tailWord_263297 prefixEnd_263297 45065971962320527658875 := by
  unfold tailWord_263297
  simp only [CollatzResearch.WordTrace]
  refine ⟨9603230527127411392660145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6402153684751607595106763 9603230527127411392660145)
  ·
    refine ⟨7202422895345558544495109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9603230527127411392660145 7202422895345558544495109)
    ·
      refine ⟨1350454292877292227092833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7202422895345558544495109 1350454292877292227092833)
      ·
        refine ⟨1012840719657969170319625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1350454292877292227092833 1012840719657969170319625)
        ·
          refine ⟨759630539743476877739719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012840719657969170319625 759630539743476877739719)
          ·
            refine ⟨1139445809615215316609579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759630539743476877739719 1139445809615215316609579)
            ·
              refine ⟨1709168714422822974914369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139445809615215316609579 1709168714422822974914369)
              ·
                refine ⟨1281876535817117231185777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1709168714422822974914369 1281876535817117231185777)
                ·
                  refine ⟨961407401862837923389333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1281876535817117231185777 961407401862837923389333)
                  ·
                    refine ⟨45065971962320527658875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 961407401862837923389333 45065971962320527658875)
                    ·
                      rfl

theorem cell23_263297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_263297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263297 prefixEnd_263297 := by exact prefixLift 263297
  have htrace : WordTrace (prefixWord ++ tailWord_263297) baseStart_263297 baseEnd_263297 := by
    simpa [prefixWord, tailWord_263297, baseEnd_263297] using wordTrace_append hprefix tailTrace_263297
  have hstable : (prefixWord ++ tailWord_263297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263297).length < 2 ^ (prefixWord ++ tailWord_263297).sum := by decide
  have hdescent : baseEnd_263297 < baseStart_263297 := by decide
  rcases family_descends (prefixWord ++ tailWord_263297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263338 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_263338 : Nat := 118140960795 + 263338 * 2 ^ 59
def prefixEnd_263338 : Nat := 4983230072969 + 3 ^ 40 * 263338 * 2
def baseEnd_263338 : Nat := 135218968593795922563937

theorem tailTrace_263338 : CollatzResearch.WordTrace tailWord_263338 prefixEnd_263338 135218968593795922563937 := by
  unfold tailWord_263338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2401181479994718848725667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6403150613319250263268445 2401181479994718848725667)
  ·
    refine ⟨3601772219992078273088501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2401181479994718848725667 3601772219992078273088501)
    ·
      refine ⟨337666145624257338102047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3601772219992078273088501 337666145624257338102047)
      ·
        refine ⟨506499218436386007153071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337666145624257338102047 506499218436386007153071)
        ·
          refine ⟨759748827654579010729607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506499218436386007153071 759748827654579010729607)
          ·
            refine ⟨1139623241481868516094411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759748827654579010729607 1139623241481868516094411)
            ·
              refine ⟨1709434862222802774141617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139623241481868516094411 1709434862222802774141617)
              ·
                refine ⟨1282076146667102080606213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1709434862222802774141617 1282076146667102080606213)
                ·
                  refine ⟨240389277500081640113665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282076146667102080606213 240389277500081640113665)
                  ·
                    refine ⟨180291958125061230085249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240389277500081640113665 180291958125061230085249)
                    ·
                      refine ⟨135218968593795922563937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180291958125061230085249 135218968593795922563937)
                      ·
                        rfl

theorem cell23_263338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_263338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263338 prefixEnd_263338 := by exact prefixLift 263338
  have htrace : WordTrace (prefixWord ++ tailWord_263338) baseStart_263338 baseEnd_263338 := by
    simpa [prefixWord, tailWord_263338, baseEnd_263338] using wordTrace_append hprefix tailTrace_263338
  have hstable : (prefixWord ++ tailWord_263338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263338).length < 2 ^ (prefixWord ++ tailWord_263338).sum := by decide
  have hdescent : baseEnd_263338 < baseStart_263338 := by decide
  rcases family_descends (prefixWord ++ tailWord_263338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263357 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_263357 : Nat := 118140960795 + 263357 * 2 ^ 59
def prefixEnd_263357 : Nat := 4983230072969 + 3 ^ 40 * 263357 * 2
def baseEnd_263357 : Nat := 45076241575410449408783

theorem tailTrace_263357 : CollatzResearch.WordTrace tailWord_263357 prefixEnd_263357 45076241575410449408783 := by
  unfold tailWord_263357
  simp only [CollatzResearch.WordTrace]
  refine ⟨9605418906910041639844325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6403612604606694426562883 9605418906910041639844325)
  ·
    refine ⟨1801016045045632807470811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9605418906910041639844325 1801016045045632807470811)
    ·
      refine ⟨2701524067568449211206217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1801016045045632807470811 2701524067568449211206217)
      ·
        refine ⟨2026143050676336908404663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2701524067568449211206217 2026143050676336908404663)
        ·
          refine ⟨3039214576014505362606995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026143050676336908404663 3039214576014505362606995)
          ·
            refine ⟨4558821864021758043910493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039214576014505362606995 4558821864021758043910493)
            ·
              refine ⟨1709558199008159266466435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4558821864021758043910493 1709558199008159266466435)
              ·
                refine ⟨2564337298512238899699653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709558199008159266466435 2564337298512238899699653)
                ·
                  refine ⟨480813243471044793693685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2564337298512238899699653 480813243471044793693685)
                  ·
                    refine ⟨45076241575410449408783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 480813243471044793693685 45076241575410449408783)
                    ·
                      rfl

theorem cell23_263357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_263357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263357 prefixEnd_263357 := by exact prefixLift 263357
  have htrace : WordTrace (prefixWord ++ tailWord_263357) baseStart_263357 baseEnd_263357 := by
    simpa [prefixWord, tailWord_263357, baseEnd_263357] using wordTrace_append hprefix tailTrace_263357
  have hstable : (prefixWord ++ tailWord_263357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263357).length < 2 ^ (prefixWord ++ tailWord_263357).sum := by decide
  have hdescent : baseEnd_263357 < baseStart_263357 := by decide
  rcases family_descends (prefixWord ++ tailWord_263357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263361 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 7]
def baseStart_263361 : Nat := 118140960795 + 263361 * 2 ^ 59
def prefixEnd_263361 : Nat := 4983230072969 + 3 ^ 40 * 263361 * 2
def baseEnd_263361 : Nat := 15025642072094370286259

theorem tailTrace_263361 : CollatzResearch.WordTrace tailWord_263361 prefixEnd_263361 15025642072094370286259 := by
  unfold tailWord_263361
  simp only [CollatzResearch.WordTrace]
  refine ⟨9605564798895550322989937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6403709865930366881993291 9605564798895550322989937)
  ·
    refine ⟨7204173599171662742242453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9605564798895550322989937 7204173599171662742242453)
    ·
      refine ⟨337695637461171691042615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7204173599171662742242453 337695637461171691042615)
      ·
        refine ⟨506543456191757536563923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337695637461171691042615 506543456191757536563923)
        ·
          refine ⟨759815184287636304845885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506543456191757536563923 759815184287636304845885)
          ·
            refine ⟨284930694107863614317207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759815184287636304845885 284930694107863614317207)
            ·
              refine ⟨427396041161795421475811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284930694107863614317207 427396041161795421475811)
              ·
                refine ⟨641094061742693132213717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427396041161795421475811 641094061742693132213717)
                ·
                  refine ⟨15025642072094370286259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 641094061742693132213717 15025642072094370286259)
                  ·
                    rfl

theorem cell23_263361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 7].length) (baseStart_263361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263361 prefixEnd_263361 := by exact prefixLift 263361
  have htrace : WordTrace (prefixWord ++ tailWord_263361) baseStart_263361 baseEnd_263361 := by
    simpa [prefixWord, tailWord_263361, baseEnd_263361] using wordTrace_append hprefix tailTrace_263361
  have hstable : (prefixWord ++ tailWord_263361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263361).length < 2 ^ (prefixWord ++ tailWord_263361).sum := by decide
  have hdescent : baseEnd_263361 < baseStart_263361 := by decide
  rcases family_descends (prefixWord ++ tailWord_263361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263366 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_263366 : Nat := 118140960795 + 263366 * 2 ^ 59
def prefixEnd_263366 : Nat := 4983230072969 + 3 ^ 40 * 263366 * 2
def baseEnd_263366 : Nat := 135233346052121813013809

theorem tailTrace_263366 : CollatzResearch.WordTrace tailWord_263366 prefixEnd_263366 135233346052121813013809 := by
  unfold tailWord_263366
  simp only [CollatzResearch.WordTrace]
  refine ⟨300179598871169880528811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6403831442584957451281301 300179598871169880528811)
  ·
    refine ⟨450269398306754820793217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300179598871169880528811 450269398306754820793217)
    ·
      refine ⟨337702048730066115594913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450269398306754820793217 337702048730066115594913)
      ·
        refine ⟨253276536547549586696185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337702048730066115594913 253276536547549586696185)
        ·
          refine ⟨189957402410662190022139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253276536547549586696185 189957402410662190022139)
          ·
            refine ⟨284936103615993285033209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189957402410662190022139 284936103615993285033209)
            ·
              refine ⟨213702077711994963774907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284936103615993285033209 213702077711994963774907)
              ·
                refine ⟨320553116567992445662361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213702077711994963774907 320553116567992445662361)
                ·
                  refine ⟨240414837425994334246771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320553116567992445662361 240414837425994334246771)
                  ·
                    refine ⟨360622256138991501370157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 240414837425994334246771 360622256138991501370157)
                    ·
                      refine ⟨135233346052121813013809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 360622256138991501370157 135233346052121813013809)
                      ·
                        rfl

theorem cell23_263366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_263366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263366 prefixEnd_263366 := by exact prefixLift 263366
  have htrace : WordTrace (prefixWord ++ tailWord_263366) baseStart_263366 baseEnd_263366 := by
    simpa [prefixWord, tailWord_263366, baseEnd_263366] using wordTrace_append hprefix tailTrace_263366
  have hstable : (prefixWord ++ tailWord_263366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263366).length < 2 ^ (prefixWord ++ tailWord_263366).sum := by decide
  have hdescent : baseEnd_263366 < baseStart_263366 := by decide
  rcases family_descends (prefixWord ++ tailWord_263366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263377 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_263377 : Nat := 118140960795 + 263377 * 2 ^ 59
def prefixEnd_263377 : Nat := 4983230072969 + 3 ^ 40 * 263377 * 2
def baseEnd_263377 : Nat := 135238994339321269976257

theorem tailTrace_263377 : CollatzResearch.WordTrace tailWord_263377 prefixEnd_263377 135238994339321269976257 := by
  unfold tailWord_263377
  simp only [CollatzResearch.WordTrace]
  refine ⟨9606148366837585055572385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6404098911225056703714923 9606148366837585055572385)
  ·
    refine ⟨7204611275128188791679289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9606148366837585055572385 7204611275128188791679289)
    ·
      refine ⟨5403458456346141593759467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7204611275128188791679289 5403458456346141593759467)
      ·
        refine ⟨8105187684519212390639201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5403458456346141593759467 8105187684519212390639201)
        ·
          refine ⟨6078890763389409292979401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8105187684519212390639201 6078890763389409292979401)
          ·
            refine ⟨4559168072542056969734551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6078890763389409292979401 4559168072542056969734551)
            ·
              refine ⟨6838752108813085454601827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559168072542056969734551 6838752108813085454601827)
              ·
                refine ⟨10258128163219628181902741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6838752108813085454601827 10258128163219628181902741)
                ·
                  refine ⟨480849757650920071026691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10258128163219628181902741 480849757650920071026691)
                  ·
                    refine ⟨721274636476380106540037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 480849757650920071026691 721274636476380106540037)
                    ·
                      refine ⟨135238994339321269976257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 721274636476380106540037 135238994339321269976257)
                      ·
                        rfl

theorem cell23_263377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_263377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263377 prefixEnd_263377 := by exact prefixLift 263377
  have htrace : WordTrace (prefixWord ++ tailWord_263377) baseStart_263377 baseEnd_263377 := by
    simpa [prefixWord, tailWord_263377, baseEnd_263377] using wordTrace_append hprefix tailTrace_263377
  have hstable : (prefixWord ++ tailWord_263377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263377).length < 2 ^ (prefixWord ++ tailWord_263377).sum := by decide
  have hdescent : baseEnd_263377 < baseStart_263377 := by decide
  rcases family_descends (prefixWord ++ tailWord_263377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263414 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_263414 : Nat := 118140960795 + 263414 * 2 ^ 59
def prefixEnd_263414 : Nat := 4983230072969 + 3 ^ 40 * 263414 * 2
def baseEnd_263414 : Nat := 135257993123537625213587

theorem tailTrace_263414 : CollatzResearch.WordTrace tailWord_263414 prefixEnd_263414 135257993123537625213587 := by
  unfold tailWord_263414
  simp only [CollatzResearch.WordTrace]
  refine ⟨600468616731471273416831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6404998578469026916446197 600468616731471273416831)
  ·
    refine ⟨900702925097206910125247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 600468616731471273416831 900702925097206910125247)
    ·
      refine ⟨1351054387645810365187871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 900702925097206910125247 1351054387645810365187871)
      ·
        refine ⟨2026581581468715547781807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351054387645810365187871 2026581581468715547781807)
        ·
          refine ⟨3039872372203073321672711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026581581468715547781807 3039872372203073321672711)
          ·
            refine ⟨4559808558304609982509067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039872372203073321672711 4559808558304609982509067)
            ·
              refine ⟨6839712837456914973763601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559808558304609982509067 6839712837456914973763601)
              ·
                refine ⟨5129784628092686230322701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6839712837456914973763601 5129784628092686230322701)
                ·
                  refine ⟨1923669235534757336371013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5129784628092686230322701 1923669235534757336371013)
                  ·
                    refine ⟨360687981662767000569565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1923669235534757336371013 360687981662767000569565)
                    ·
                      refine ⟨135257993123537625213587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 360687981662767000569565 135257993123537625213587)
                      ·
                        rfl

theorem cell23_263414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_263414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263414 prefixEnd_263414 := by exact prefixLift 263414
  have htrace : WordTrace (prefixWord ++ tailWord_263414) baseStart_263414 baseEnd_263414 := by
    simpa [prefixWord, tailWord_263414, baseEnd_263414] using wordTrace_append hprefix tailTrace_263414
  have hstable : (prefixWord ++ tailWord_263414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263414).length < 2 ^ (prefixWord ++ tailWord_263414).sum := by decide
  have hdescent : baseEnd_263414 < baseStart_263414 := by decide
  rcases family_descends (prefixWord ++ tailWord_263414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263457 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_263457 : Nat := 118140960795 + 263457 * 2 ^ 59
def prefixEnd_263457 : Nat := 4983230072969 + 3 ^ 40 * 263457 * 2
def baseEnd_263457 : Nat := 135280072791680956975889

theorem tailTrace_263457 : CollatzResearch.WordTrace tailWord_263457 prefixEnd_263457 135280072791680956975889 := by
  unfold tailWord_263457
  simp only [CollatzResearch.WordTrace]
  refine ⟨9609066206547758718484625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6406044137698505812323083 9609066206547758718484625)
  ·
    refine ⟨7206799654910819038863469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9609066206547758718484625 7206799654910819038863469)
    ·
      refine ⟨2702549870591557139573801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7206799654910819038863469 2702549870591557139573801)
      ·
        refine ⟨2026912402943667854680351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2702549870591557139573801 2026912402943667854680351)
        ·
          refine ⟨3040368604415501782020527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026912402943667854680351 3040368604415501782020527)
          ·
            refine ⟨4560552906623252673030791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040368604415501782020527 4560552906623252673030791)
            ·
              refine ⟨6840829359934879009546187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4560552906623252673030791 6840829359934879009546187)
              ·
                refine ⟨10261244039902318514319281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6840829359934879009546187 10261244039902318514319281)
                ·
                  refine ⟨7695933029926738885739461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10261244039902318514319281 7695933029926738885739461)
                  ·
                    refine ⟨1442987443111263541076149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7695933029926738885739461 1442987443111263541076149)
                    ·
                      refine ⟨135280072791680956975889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1442987443111263541076149 135280072791680956975889)
                      ·
                        rfl

theorem cell23_263457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_263457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263457 prefixEnd_263457 := by exact prefixLift 263457
  have htrace : WordTrace (prefixWord ++ tailWord_263457) baseStart_263457 baseEnd_263457 := by
    simpa [prefixWord, tailWord_263457, baseEnd_263457] using wordTrace_append hprefix tailTrace_263457
  have hstable : (prefixWord ++ tailWord_263457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263457).length < 2 ^ (prefixWord ++ tailWord_263457).sum := by decide
  have hdescent : baseEnd_263457 < baseStart_263457 := by decide
  rcases family_descends (prefixWord ++ tailWord_263457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263507 : List Nat := [1, 1, 1, 2, 1, 1, 7, 9]
def baseStart_263507 : Nat := 118140960795 + 263507 * 2 ^ 59
def prefixEnd_263507 : Nat := 4983230072969 + 3 ^ 40 * 263507 * 2
def baseEnd_263507 : Nat := 5011323956459472642617

theorem tailTrace_263507 : CollatzResearch.WordTrace tailWord_263507 prefixEnd_263507 5011323956459472642617 := by
  unfold tailWord_263507
  simp only [CollatzResearch.WordTrace]
  refine ⟨9610889856366617257804775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6407259904244411505203183 9610889856366617257804775)
  ·
    refine ⟨14416334784549925886707163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9610889856366617257804775 14416334784549925886707163)
    ·
      refine ⟨21624502176824888830060745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14416334784549925886707163 21624502176824888830060745)
      ·
        refine ⟨16218376632618666622545559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21624502176824888830060745 16218376632618666622545559)
        ·
          refine ⟨24327564948927999933818339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16218376632618666622545559 24327564948927999933818339)
          ·
            refine ⟨36491347423391999900727509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24327564948927999933818339 36491347423391999900727509)
            ·
              refine ⟨855265955235749997673301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36491347423391999900727509 855265955235749997673301)
              ·
                refine ⟨5011323956459472642617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 855265955235749997673301 5011323956459472642617)
                ·
                  rfl

theorem cell23_263507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 9].length) (baseStart_263507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263507 prefixEnd_263507 := by exact prefixLift 263507
  have htrace : WordTrace (prefixWord ++ tailWord_263507) baseStart_263507 baseEnd_263507 := by
    simpa [prefixWord, tailWord_263507, baseEnd_263507] using wordTrace_append hprefix tailTrace_263507
  have hstable : (prefixWord ++ tailWord_263507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263507).length < 2 ^ (prefixWord ++ tailWord_263507).sum := by decide
  have hdescent : baseEnd_263507 < baseStart_263507 := by decide
  rcases family_descends (prefixWord ++ tailWord_263507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263514 : List Nat := [3, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_263514 : Nat := 118140960795 + 263514 * 2 ^ 59
def prefixEnd_263514 : Nat := 4983230072969 + 3 ^ 40 * 263514 * 2
def baseEnd_263514 : Nat := 135309341188987233963127

theorem tailTrace_263514 : CollatzResearch.WordTrace tailWord_263514 prefixEnd_263514 135309341188987233963127 := by
  unfold tailWord_263514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2402786291835314363327399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6407430111560838302206397 2402786291835314363327399)
  ·
    refine ⟨3604179437752971544991099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2402786291835314363327399 3604179437752971544991099)
    ·
      refine ⟨5406269156629457317486649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3604179437752971544991099 5406269156629457317486649)
      ·
        refine ⟨4054701867472092988114987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5406269156629457317486649 4054701867472092988114987)
        ·
          refine ⟨6082052801208139482172481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4054701867472092988114987 6082052801208139482172481)
          ·
            refine ⟨4561539600906104611629361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6082052801208139482172481 4561539600906104611629361)
            ·
              refine ⟨3421154700679578458722021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4561539600906104611629361 3421154700679578458722021)
              ·
                refine ⟨641466506377420961010379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3421154700679578458722021 641466506377420961010379)
                ·
                  refine ⟨962199759566131441515569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641466506377420961010379 962199759566131441515569)
                  ·
                    refine ⟨721649819674598581136677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 962199759566131441515569 721649819674598581136677)
                    ·
                      refine ⟨135309341188987233963127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 721649819674598581136677 135309341188987233963127)
                      ·
                        rfl

theorem cell23_263514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_263514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263514 prefixEnd_263514 := by exact prefixLift 263514
  have htrace : WordTrace (prefixWord ++ tailWord_263514) baseStart_263514 baseEnd_263514 := by
    simpa [prefixWord, tailWord_263514, baseEnd_263514] using wordTrace_append hprefix tailTrace_263514
  have hstable : (prefixWord ++ tailWord_263514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263514).length < 2 ^ (prefixWord ++ tailWord_263514).sum := by decide
  have hdescent : baseEnd_263514 < baseStart_263514 := by decide
  rcases family_descends (prefixWord ++ tailWord_263514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263524 : List Nat := [2, 3, 1, 1, 3, 4, 9]
def baseStart_263524 : Nat := 118140960795 + 263524 * 2 ^ 59
def prefixEnd_263524 : Nat := 4983230072969 + 3 ^ 40 * 263524 * 2
def baseEnd_263524 : Nat := 1670549086364594998001

theorem tailTrace_263524 : CollatzResearch.WordTrace tailWord_263524 prefixEnd_263524 1670549086364594998001 := by
  unfold tailWord_263524
  simp only [CollatzResearch.WordTrace]
  refine ⟨4805754948652514580586813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6407673264870019440782417 4805754948652514580586813)
  ·
    refine ⟨1802158105744692967720055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4805754948652514580586813 1802158105744692967720055)
    ·
      refine ⟨2703237158617039451580083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1802158105744692967720055 2703237158617039451580083)
      ·
        refine ⟨4054855737925559177370125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2703237158617039451580083 4054855737925559177370125)
        ·
          refine ⟨1520570901722084691513797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4054855737925559177370125 1520570901722084691513797)
          ·
            refine ⟨285107044072890879658837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1520570901722084691513797 285107044072890879658837)
            ·
              refine ⟨1670549086364594998001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 285107044072890879658837 1670549086364594998001)
              ·
                rfl

theorem cell23_263524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 9].length) (baseStart_263524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263524 prefixEnd_263524 := by exact prefixLift 263524
  have htrace : WordTrace (prefixWord ++ tailWord_263524) baseStart_263524 baseEnd_263524 := by
    simpa [prefixWord, tailWord_263524, baseEnd_263524] using wordTrace_append hprefix tailTrace_263524
  have hstable : (prefixWord ++ tailWord_263524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263524).length < 2 ^ (prefixWord ++ tailWord_263524).sum := by decide
  have hdescent : baseEnd_263524 < baseStart_263524 := by decide
  rcases family_descends (prefixWord ++ tailWord_263524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263541 : List Nat := [1, 3, 4, 1, 3, 1, 2, 8]
def baseStart_263541 : Nat := 118140960795 + 263541 * 2 ^ 59
def prefixEnd_263541 : Nat := 4983230072969 + 3 ^ 40 * 263541 * 2
def baseEnd_263541 : Nat := 5011970561728097345389

theorem tailTrace_263541 : CollatzResearch.WordTrace tailWord_263541 prefixEnd_263541 5011970561728097345389 := by
  unfold tailWord_263541
  simp only [CollatzResearch.WordTrace]
  refine ⟨9612129938243441064542477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6408086625495627376361651 9612129938243441064542477)
  ·
    refine ⟨3604548726841290399203429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9612129938243441064542477 3604548726841290399203429)
    ·
      refine ⟨675852886282741949850643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3604548726841290399203429 675852886282741949850643)
      ·
        refine ⟨1013779329424112924775965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675852886282741949850643 1013779329424112924775965)
        ·
          refine ⟨380167248534042346790987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1013779329424112924775965 380167248534042346790987)
          ·
            refine ⟨570250872801063520186481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380167248534042346790987 570250872801063520186481)
            ·
              refine ⟨427688154600797640139861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570250872801063520186481 427688154600797640139861)
              ·
                refine ⟨5011970561728097345389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 427688154600797640139861 5011970561728097345389)
                ·
                  rfl

theorem cell23_263541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 8].length) (baseStart_263541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263541 prefixEnd_263541 := by exact prefixLift 263541
  have htrace : WordTrace (prefixWord ++ tailWord_263541) baseStart_263541 baseEnd_263541 := by
    simpa [prefixWord, tailWord_263541, baseEnd_263541] using wordTrace_append hprefix tailTrace_263541
  have hstable : (prefixWord ++ tailWord_263541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263541).length < 2 ^ (prefixWord ++ tailWord_263541).sum := by decide
  have hdescent : baseEnd_263541 < baseStart_263541 := by decide
  rcases family_descends (prefixWord ++ tailWord_263541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263584 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 2, 6]
def baseStart_263584 : Nat := 118140960795 + 263584 * 2 ^ 59
def prefixEnd_263584 : Nat := 4983230072969 + 3 ^ 40 * 263584 * 2
def baseEnd_263584 : Nat := 45115094944933986695935

theorem tailTrace_263584 : CollatzResearch.WordTrace tailWord_263584 prefixEnd_263584 45115094944933986695935 := by
  unfold tailWord_263584
  simp only [CollatzResearch.WordTrace]
  refine ⟨4806849138543829704178903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6409132184725106272238537 4806849138543829704178903)
  ·
    refine ⟨7210273707815744556268355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4806849138543829704178903 7210273707815744556268355)
    ·
      refine ⟨10815410561723616834402533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7210273707815744556268355 10815410561723616834402533)
      ·
        refine ⟨2027889480323178156450475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10815410561723616834402533 2027889480323178156450475)
        ·
          refine ⟨3041834220484767234675713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2027889480323178156450475 3041834220484767234675713)
          ·
            refine ⟨2281375665363575426006785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3041834220484767234675713 2281375665363575426006785)
            ·
              refine ⟨1711031749022681569505089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2281375665363575426006785 1711031749022681569505089)
              ·
                refine ⟨1283273811767011177128817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1711031749022681569505089 1283273811767011177128817)
                ·
                  refine ⟨962455358825258382846613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1283273811767011177128817 962455358825258382846613)
                  ·
                    refine ⟨45115094944933986695935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 962455358825258382846613 45115094944933986695935)
                    ·
                      rfl

theorem cell23_263584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_263584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263584 prefixEnd_263584 := by exact prefixLift 263584
  have htrace : WordTrace (prefixWord ++ tailWord_263584) baseStart_263584 baseEnd_263584 := by
    simpa [prefixWord, tailWord_263584, baseEnd_263584] using wordTrace_append hprefix tailTrace_263584
  have hstable : (prefixWord ++ tailWord_263584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263584).length < 2 ^ (prefixWord ++ tailWord_263584).sum := by decide
  have hdescent : baseEnd_263584 < baseStart_263584 := by decide
  rcases family_descends (prefixWord ++ tailWord_263584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263631 : List Nat := [1, 1, 2, 1, 1, 4, 3, 5, 5]
def baseStart_263631 : Nat := 118140960795 + 263631 * 2 ^ 59
def prefixEnd_263631 : Nat := 4983230072969 + 3 ^ 40 * 263631 * 2
def baseEnd_263631 : Nat := 15041046491729252911121

theorem tailTrace_263631 : CollatzResearch.WordTrace tailWord_263631 prefixEnd_263631 15041046491729252911121 := by
  unfold tailWord_263631
  simp only [CollatzResearch.WordTrace]
  refine ⟨9615412507917386435318747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6410275005278257623545831 9615412507917386435318747)
  ·
    refine ⟨14423118761876079652978121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9615412507917386435318747 14423118761876079652978121)
    ·
      refine ⟨10817339071407059739733591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14423118761876079652978121 10817339071407059739733591)
      ·
        refine ⟨16226008607110589609600387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10817339071407059739733591 16226008607110589609600387)
        ·
          refine ⟨24339012910665884414400581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16226008607110589609600387 24339012910665884414400581)
          ·
            refine ⟨4563564920749853327700109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24339012910665884414400581 4563564920749853327700109)
            ·
              refine ⟨1711336845281194997887541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4563564920749853327700109 1711336845281194997887541)
              ·
                refine ⟨160437829245112031051957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1711336845281194997887541 160437829245112031051957)
                ·
                  refine ⟨15041046491729252911121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160437829245112031051957 15041046491729252911121)
                  ·
                    rfl

theorem cell23_263631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 5].length) (baseStart_263631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263631 prefixEnd_263631 := by exact prefixLift 263631
  have htrace : WordTrace (prefixWord ++ tailWord_263631) baseStart_263631 baseEnd_263631 := by
    simpa [prefixWord, tailWord_263631, baseEnd_263631] using wordTrace_append hprefix tailTrace_263631
  have hstable : (prefixWord ++ tailWord_263631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263631).length < 2 ^ (prefixWord ++ tailWord_263631).sum := by decide
  have hdescent : baseEnd_263631 < baseStart_263631 := by decide
  rcases family_descends (prefixWord ++ tailWord_263631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263638 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_263638 : Nat := 118140960795 + 263638 * 2 ^ 59
def prefixEnd_263638 : Nat := 4983230072969 + 3 ^ 40 * 263638 * 2
def baseEnd_263638 : Nat := 135373012790144748812557

theorem tailTrace_263638 : CollatzResearch.WordTrace tailWord_263638 prefixEnd_263638 135373012790144748812557 := by
  unfold tailWord_263638
  simp only [CollatzResearch.WordTrace]
  refine ⟨600979238680751664426473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6410445212594684420549045 600979238680751664426473)
  ·
    refine ⟨450734429010563748319855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 600979238680751664426473 450734429010563748319855)
    ·
      refine ⟨676101643515845622479783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450734429010563748319855 676101643515845622479783)
      ·
        refine ⟨1014152465273768433719675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676101643515845622479783 1014152465273768433719675)
        ·
          refine ⟨1521228697910652650579513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014152465273768433719675 1521228697910652650579513)
          ·
            refine ⟨1140921523432989487934635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521228697910652650579513 1140921523432989487934635)
            ·
              refine ⟨1711382285149484231901953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140921523432989487934635 1711382285149484231901953)
              ·
                refine ⟨1283536713862113173926465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1711382285149484231901953 1283536713862113173926465)
                ·
                  refine ⟨962652535396584880444849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1283536713862113173926465 962652535396584880444849)
                  ·
                    refine ⟨721989401547438660333637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 962652535396584880444849 721989401547438660333637)
                    ·
                      refine ⟨135373012790144748812557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 721989401547438660333637 135373012790144748812557)
                      ·
                        rfl

theorem cell23_263638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_263638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263638 prefixEnd_263638 := by exact prefixLift 263638
  have htrace : WordTrace (prefixWord ++ tailWord_263638) baseStart_263638 baseEnd_263638 := by
    simpa [prefixWord, tailWord_263638, baseEnd_263638] using wordTrace_append hprefix tailTrace_263638
  have hstable : (prefixWord ++ tailWord_263638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263638).length < 2 ^ (prefixWord ++ tailWord_263638).sum := by decide
  have hdescent : baseEnd_263638 < baseStart_263638 := by decide
  rcases family_descends (prefixWord ++ tailWord_263638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263641 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 2, 3, 3]
def baseStart_263641 : Nat := 118140960795 + 263641 * 2 ^ 59
def prefixEnd_263641 : Nat := 4983230072969 + 3 ^ 40 * 263641 * 2
def baseEnd_263641 : Nat := 135374553232108237075043

theorem tailTrace_263641 : CollatzResearch.WordTrace tailWord_263641 prefixEnd_263641 135374553232108237075043 := by
  unfold tailWord_263641
  simp only [CollatzResearch.WordTrace]
  refine ⟨9615777237881158143182777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6410518158587438762121851 9615777237881158143182777)
  ·
    refine ⟨7211832928410868607387083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9615777237881158143182777 7211832928410868607387083)
    ·
      refine ⟨10817749392616302911080625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7211832928410868607387083 10817749392616302911080625)
      ·
        refine ⟨8113312044462227183310469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10817749392616302911080625 8113312044462227183310469)
        ·
          refine ⟨1521246008336667596870713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8113312044462227183310469 1521246008336667596870713)
          ·
            refine ⟨1140934506252500697653035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521246008336667596870713 1140934506252500697653035)
            ·
              refine ⟨1711401759378751046479553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140934506252500697653035 1711401759378751046479553)
              ·
                refine ⟨1283551319534063284859665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1711401759378751046479553 1283551319534063284859665)
                ·
                  refine ⟨962663489650547463644749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1283551319534063284859665 962663489650547463644749)
                  ·
                    refine ⟨360998808618955298866781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 962663489650547463644749 360998808618955298866781)
                    ·
                      refine ⟨135374553232108237075043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 360998808618955298866781 135374553232108237075043)
                      ·
                        rfl

theorem cell23_263641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_263641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263641 prefixEnd_263641 := by exact prefixLift 263641
  have htrace : WordTrace (prefixWord ++ tailWord_263641) baseStart_263641 baseEnd_263641 := by
    simpa [prefixWord, tailWord_263641, baseEnd_263641] using wordTrace_append hprefix tailTrace_263641
  have hstable : (prefixWord ++ tailWord_263641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263641).length < 2 ^ (prefixWord ++ tailWord_263641).sum := by decide
  have hdescent : baseEnd_263641 < baseStart_263641 := by decide
  rcases family_descends (prefixWord ++ tailWord_263641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263642 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2]
def baseStart_263642 : Nat := 118140960795 + 263642 * 2 ^ 59
def prefixEnd_263642 : Nat := 4983230072969 + 3 ^ 40 * 263642 * 2
def baseEnd_263642 : Nat := 135375066712762733162539

theorem tailTrace_263642 : CollatzResearch.WordTrace tailWord_263642 prefixEnd_263642 135375066712762733162539 := by
  unfold tailWord_263642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2403953427719383828492295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6410542473918356875979453 2403953427719383828492295)
  ·
    refine ⟨3605930141579075742738443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2403953427719383828492295 3605930141579075742738443)
    ·
      refine ⟨5408895212368613614107665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3605930141579075742738443 5408895212368613614107665)
      ·
        refine ⟨4056671409276460210580749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5408895212368613614107665 4056671409276460210580749)
        ·
          refine ⟨1521251778478672578967781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4056671409276460210580749 1521251778478672578967781)
          ·
            refine ⟨285234708464751108556459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1521251778478672578967781 285234708464751108556459)
            ·
              refine ⟨427852062697126662834689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285234708464751108556459 427852062697126662834689)
              ·
                refine ⟨320889047022844997126017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427852062697126662834689 320889047022844997126017)
                ·
                  refine ⟨240666785267133747844513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320889047022844997126017 240666785267133747844513)
                  ·
                    refine ⟨180500088950350310883385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240666785267133747844513 180500088950350310883385)
                    ·
                      refine ⟨135375066712762733162539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180500088950350310883385 135375066712762733162539)
                      ·
                        rfl

theorem cell23_263642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_263642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263642 prefixEnd_263642 := by exact prefixLift 263642
  have htrace : WordTrace (prefixWord ++ tailWord_263642) baseStart_263642 baseEnd_263642 := by
    simpa [prefixWord, tailWord_263642, baseEnd_263642] using wordTrace_append hprefix tailTrace_263642
  have hstable : (prefixWord ++ tailWord_263642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263642).length < 2 ^ (prefixWord ++ tailWord_263642).sum := by decide
  have hdescent : baseEnd_263642 < baseStart_263642 := by decide
  rcases family_descends (prefixWord ++ tailWord_263642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263674 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_263674 : Nat := 118140960795 + 263674 * 2 ^ 59
def prefixEnd_263674 : Nat := 4983230072969 + 3 ^ 40 * 263674 * 2
def baseEnd_263674 : Nat := 45130499364568869320797

theorem tailTrace_263674 : CollatzResearch.WordTrace tailWord_263674 prefixEnd_263674 45130499364568869320797 := by
  unfold tailWord_263674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2404245211690401194783519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6411320564507736519422717 2404245211690401194783519)
  ·
    refine ⟨3606367817535601792175279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2404245211690401194783519 3606367817535601792175279)
    ·
      refine ⟨5409551726303402688262919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3606367817535601792175279 5409551726303402688262919)
      ·
        refine ⟨8114327589455104032394379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5409551726303402688262919 8114327589455104032394379)
        ·
          refine ⟨12171491384182656048591569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8114327589455104032394379 12171491384182656048591569)
          ·
            refine ⟨9128618538136992036443677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12171491384182656048591569 9128618538136992036443677)
            ·
              refine ⟨3423231951801372013666379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9128618538136992036443677 3423231951801372013666379)
              ·
                refine ⟨5134847927702058020499569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3423231951801372013666379 5134847927702058020499569)
                ·
                  refine ⟨3851135945776543515374677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5134847927702058020499569 3851135945776543515374677)
                  ·
                    refine ⟨45130499364568869320797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3851135945776543515374677 45130499364568869320797)
                    ·
                      rfl

theorem cell23_263674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_263674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263674 prefixEnd_263674 := by exact prefixLift 263674
  have htrace : WordTrace (prefixWord ++ tailWord_263674) baseStart_263674 baseEnd_263674 := by
    simpa [prefixWord, tailWord_263674, baseEnd_263674] using wordTrace_append hprefix tailTrace_263674
  have hstable : (prefixWord ++ tailWord_263674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263674).length < 2 ^ (prefixWord ++ tailWord_263674).sum := by decide
  have hdescent : baseEnd_263674 < baseStart_263674 := by decide
  rcases family_descends (prefixWord ++ tailWord_263674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263682 : List Nat := [3, 4, 1, 2, 1, 3, 1, 3, 5]
def baseStart_263682 : Nat := 118140960795 + 263682 * 2 ^ 59
def prefixEnd_263682 : Nat := 4983230072969 + 3 ^ 40 * 263682 * 2
def baseEnd_263682 : Nat := 15043956215438064073595

theorem tailTrace_263682 : CollatzResearch.WordTrace tailWord_263682 prefixEnd_263682 15043956215438064073595 := by
  unfold tailWord_263682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2404318157683155536356325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6411515087155081430283533 2404318157683155536356325)
  ·
    refine ⟨450809654565591663066811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2404318157683155536356325 450809654565591663066811)
    ·
      refine ⟨676214481848387494600217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450809654565591663066811 676214481848387494600217)
      ·
        refine ⟨507160861386290620950163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676214481848387494600217 507160861386290620950163)
        ·
          refine ⟨760741292079435931425245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507160861386290620950163 760741292079435931425245)
          ·
            refine ⟨285277984529788474284467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 760741292079435931425245 285277984529788474284467)
            ·
              refine ⟨427916976794682711426701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285277984529788474284467 427916976794682711426701)
              ·
                refine ⟨160468866298006016785013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427916976794682711426701 160468866298006016785013)
                ·
                  refine ⟨15043956215438064073595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160468866298006016785013 15043956215438064073595)
                  ·
                    rfl

theorem cell23_263682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_263682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263682 prefixEnd_263682 := by exact prefixLift 263682
  have htrace : WordTrace (prefixWord ++ tailWord_263682) baseStart_263682 baseEnd_263682 := by
    simpa [prefixWord, tailWord_263682, baseEnd_263682] using wordTrace_append hprefix tailTrace_263682
  have hstable : (prefixWord ++ tailWord_263682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263682).length < 2 ^ (prefixWord ++ tailWord_263682).sum := by decide
  have hdescent : baseEnd_263682 < baseStart_263682 := by decide
  rcases family_descends (prefixWord ++ tailWord_263682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263710 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_263710 : Nat := 118140960795 + 263710 * 2 ^ 59
def prefixEnd_263710 : Nat := 4983230072969 + 3 ^ 40 * 263710 * 2
def baseEnd_263710 : Nat := 135409983397268467112227

theorem tailTrace_263710 : CollatzResearch.WordTrace tailWord_263710 prefixEnd_263710 135409983397268467112227 := by
  unfold tailWord_263710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202286734328897865930573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6412195916420788618296389 1202286734328897865930573)
  ·
    refine ⟨450857525373336699723965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1202286734328897865930573 450857525373336699723965)
    ·
      refine ⟨169071572015001262396487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 450857525373336699723965 169071572015001262396487)
      ·
        refine ⟨253607358022501893594731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169071572015001262396487 253607358022501893594731)
        ·
          refine ⟨380411037033752840392097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253607358022501893594731 380411037033752840392097)
          ·
            refine ⟨285308277775314630294073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380411037033752840392097 285308277775314630294073)
            ·
              refine ⟨213981208331485972720555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285308277775314630294073 213981208331485972720555)
              ·
                refine ⟨320971812497228959080833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213981208331485972720555 320971812497228959080833)
                ·
                  refine ⟨240728859372921719310625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320971812497228959080833 240728859372921719310625)
                  ·
                    refine ⟨180546644529691289482969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240728859372921719310625 180546644529691289482969)
                    ·
                      refine ⟨135409983397268467112227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180546644529691289482969 135409983397268467112227)
                      ·
                        rfl

theorem cell23_263710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_263710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263710 prefixEnd_263710 := by exact prefixLift 263710
  have htrace : WordTrace (prefixWord ++ tailWord_263710) baseStart_263710 baseEnd_263710 := by
    simpa [prefixWord, tailWord_263710, baseEnd_263710] using wordTrace_append hprefix tailTrace_263710
  have hstable : (prefixWord ++ tailWord_263710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263710).length < 2 ^ (prefixWord ++ tailWord_263710).sum := by decide
  have hdescent : baseEnd_263710 < baseStart_263710 := by decide
  rcases family_descends (prefixWord ++ tailWord_263710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263758 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2]
def baseStart_263758 : Nat := 118140960795 + 263758 * 2 ^ 59
def prefixEnd_263758 : Nat := 4983230072969 + 3 ^ 40 * 263758 * 2
def baseEnd_263758 : Nat := 135434630468684279312005

theorem tailTrace_263758 : CollatzResearch.WordTrace tailWord_263758 prefixEnd_263758 135434630468684279312005 := by
  unfold tailWord_263758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202505572307160890648991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6413363052304858083461285 1202505572307160890648991)
  ·
    refine ⟨1803758358460741335973487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1202505572307160890648991 1803758358460741335973487)
    ·
      refine ⟨2705637537691112003960231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1803758358460741335973487 2705637537691112003960231)
      ·
        refine ⟨4058456306536668005940347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2705637537691112003960231 4058456306536668005940347)
        ·
          refine ⟨6087684459805002008910521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4058456306536668005940347 6087684459805002008910521)
          ·
            refine ⟨4565763344853751506682891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6087684459805002008910521 4565763344853751506682891)
            ·
              refine ⟨6848645017280627260024337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4565763344853751506682891 6848645017280627260024337)
              ·
                refine ⟨5136483762960470445018253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6848645017280627260024337 5136483762960470445018253)
                ·
                  refine ⟨1926181411110176416881845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5136483762960470445018253 1926181411110176416881845)
                  ·
                    refine ⟨180579507291579039082673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1926181411110176416881845 180579507291579039082673)
                    ·
                      refine ⟨135434630468684279312005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180579507291579039082673 135434630468684279312005)
                      ·
                        rfl

theorem cell23_263758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_263758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263758 prefixEnd_263758 := by exact prefixLift 263758
  have htrace : WordTrace (prefixWord ++ tailWord_263758) baseStart_263758 baseEnd_263758 := by
    simpa [prefixWord, tailWord_263758, baseEnd_263758] using wordTrace_append hprefix tailTrace_263758
  have hstable : (prefixWord ++ tailWord_263758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263758).length < 2 ^ (prefixWord ++ tailWord_263758).sum := by decide
  have hdescent : baseEnd_263758 < baseStart_263758 := by decide
  rcases family_descends (prefixWord ++ tailWord_263758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263788 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 4]
def baseStart_263788 : Nat := 118140960795 + 263788 * 2 ^ 59
def prefixEnd_263788 : Nat := 4983230072969 + 3 ^ 40 * 263788 * 2
def baseEnd_263788 : Nat := 135450034888319161936867

theorem tailTrace_263788 : CollatzResearch.WordTrace tailWord_263788 prefixEnd_263788 135450034888319161936867 := by
  unfold tailWord_263788
  simp only [CollatzResearch.WordTrace]
  refine ⟨4810569384174301124392009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6414092512232401499189345 4810569384174301124392009)
  ·
    refine ⟨3607927038130725843294007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4810569384174301124392009 3607927038130725843294007)
    ·
      refine ⟨5411890557196088764941011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3607927038130725843294007 5411890557196088764941011)
      ·
        refine ⟨8117835835794133147411517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5411890557196088764941011 8117835835794133147411517)
        ·
          refine ⟨3044188438422799930279319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8117835835794133147411517 3044188438422799930279319)
          ·
            refine ⟨4566282657634199895418979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044188438422799930279319 4566282657634199895418979)
            ·
              refine ⟨6849423986451299843128469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4566282657634199895418979 6849423986451299843128469)
              ·
                refine ⟨321066749364904680146647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6849423986451299843128469 321066749364904680146647)
                ·
                  refine ⟨481600124047357020219971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321066749364904680146647 481600124047357020219971)
                  ·
                    refine ⟨722400186071035530329957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 481600124047357020219971 722400186071035530329957)
                    ·
                      refine ⟨135450034888319161936867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 722400186071035530329957 135450034888319161936867)
                      ·
                        rfl

theorem cell23_263788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_263788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263788 prefixEnd_263788 := by exact prefixLift 263788
  have htrace : WordTrace (prefixWord ++ tailWord_263788) baseStart_263788 baseEnd_263788 := by
    simpa [prefixWord, tailWord_263788, baseEnd_263788] using wordTrace_append hprefix tailTrace_263788
  have hstable : (prefixWord ++ tailWord_263788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263788).length < 2 ^ (prefixWord ++ tailWord_263788).sum := by decide
  have hdescent : baseEnd_263788 < baseStart_263788 := by decide
  rcases family_descends (prefixWord ++ tailWord_263788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263792 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 2, 3, 2]
def baseStart_263792 : Nat := 118140960795 + 263792 * 2 ^ 59
def prefixEnd_263792 : Nat := 4983230072969 + 3 ^ 40 * 263792 * 2
def baseEnd_263792 : Nat := 135452088810937146286849

theorem tailTrace_263792 : CollatzResearch.WordTrace tailWord_263792 prefixEnd_263792 135452088810937146286849 := by
  unfold tailWord_263792
  simp only [CollatzResearch.WordTrace]
  refine ⟨4810642330167055465964815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6414189773556073954619753 4810642330167055465964815)
  ·
    refine ⟨7215963495250583198947223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4810642330167055465964815 7215963495250583198947223)
    ·
      refine ⟨10823945242875874798420835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7215963495250583198947223 10823945242875874798420835)
      ·
        refine ⟨16235917864313812197631253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10823945242875874798420835 16235917864313812197631253)
        ·
          refine ⟨761058649889709946763965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16235917864313812197631253 761058649889709946763965)
          ·
            refine ⟨285396993708641230036487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 761058649889709946763965 285396993708641230036487)
            ·
              refine ⟨428095490562961845054731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285396993708641230036487 428095490562961845054731)
              ·
                refine ⟨642143235844442767582097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428095490562961845054731 642143235844442767582097)
                ·
                  refine ⟨481607426883332075686573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 642143235844442767582097 481607426883332075686573)
                  ·
                    refine ⟨180602785081249528382465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 481607426883332075686573 180602785081249528382465)
                    ·
                      refine ⟨135452088810937146286849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180602785081249528382465 135452088810937146286849)
                      ·
                        rfl

theorem cell23_263792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 3, 2].length) (baseStart_263792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263792 prefixEnd_263792 := by exact prefixLift 263792
  have htrace : WordTrace (prefixWord ++ tailWord_263792) baseStart_263792 baseEnd_263792 := by
    simpa [prefixWord, tailWord_263792, baseEnd_263792] using wordTrace_append hprefix tailTrace_263792
  have hstable : (prefixWord ++ tailWord_263792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263792).length < 2 ^ (prefixWord ++ tailWord_263792).sum := by decide
  have hdescent : baseEnd_263792 < baseStart_263792 := by decide
  rcases family_descends (prefixWord ++ tailWord_263792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263805 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_263805 : Nat := 118140960795 + 263805 * 2 ^ 59
def prefixEnd_263805 : Nat := 4983230072969 + 3 ^ 40 * 263805 * 2
def baseEnd_263805 : Nat := 135458764059445595424289

theorem tailTrace_263805 : CollatzResearch.WordTrace tailWord_263805 prefixEnd_263805 135458764059445595424289 := by
  unfold tailWord_263805
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621758809287014152152869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6414505872858009434768579 9621758809287014152152869)
  ·
    refine ⟨1804079776741315153528663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9621758809287014152152869 1804079776741315153528663)
    ·
      refine ⟨2706119665111972730292995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1804079776741315153528663 2706119665111972730292995)
      ·
        refine ⟨4059179497667959095439493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2706119665111972730292995 4059179497667959095439493)
        ·
          refine ⟨761096155812742330394905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4059179497667959095439493 761096155812742330394905)
          ·
            refine ⟨570822116859556747796179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761096155812742330394905 570822116859556747796179)
            ·
              refine ⟨856233175289335121694269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570822116859556747796179 856233175289335121694269)
              ·
                refine ⟨321087440733500670635351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 856233175289335121694269 321087440733500670635351)
                ·
                  refine ⟨481631161100251005953027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321087440733500670635351 481631161100251005953027)
                  ·
                    refine ⟨722446741650376508929541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 481631161100251005953027 722446741650376508929541)
                    ·
                      refine ⟨135458764059445595424289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 722446741650376508929541 135458764059445595424289)
                      ·
                        rfl

theorem cell23_263805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_263805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263805 prefixEnd_263805 := by exact prefixLift 263805
  have htrace : WordTrace (prefixWord ++ tailWord_263805) baseStart_263805 baseEnd_263805 := by
    simpa [prefixWord, tailWord_263805, baseEnd_263805] using wordTrace_append hprefix tailTrace_263805
  have hstable : (prefixWord ++ tailWord_263805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263805).length < 2 ^ (prefixWord ++ tailWord_263805).sum := by decide
  have hdescent : baseEnd_263805 < baseStart_263805 := by decide
  rcases family_descends (prefixWord ++ tailWord_263805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263815 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 2, 4]
def baseStart_263815 : Nat := 118140960795 + 263815 * 2 ^ 59
def prefixEnd_263815 : Nat := 4983230072969 + 3 ^ 40 * 263815 * 2
def baseEnd_263815 : Nat := 45154632955330185433081

theorem tailTrace_263815 : CollatzResearch.WordTrace tailWord_263815 prefixEnd_263815 45154632955330185433081 := by
  unfold tailWord_263815
  simp only [CollatzResearch.WordTrace]
  refine ⟨9622123539250785860016899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6414749026167190573344599 9622123539250785860016899)
  ·
    refine ⟨14433185308876178790025349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9622123539250785860016899 14433185308876178790025349)
    ·
      refine ⟨2706222245414283523129753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14433185308876178790025349 2706222245414283523129753)
      ·
        refine ⟨2029666684060712642347315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2706222245414283523129753 2029666684060712642347315)
        ·
          refine ⟨3044500026091068963520973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029666684060712642347315 3044500026091068963520973)
          ·
            refine ⟨1141687509784150861320365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3044500026091068963520973 1141687509784150861320365)
            ·
              refine ⟨428132816169056572995137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1141687509784150861320365 428132816169056572995137)
              ·
                refine ⟨321099612126792429746353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428132816169056572995137 321099612126792429746353)
                ·
                  refine ⟨240824709095094322309765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321099612126792429746353 240824709095094322309765)
                  ·
                    refine ⟨45154632955330185433081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240824709095094322309765 45154632955330185433081)
                    ·
                      rfl

theorem cell23_263815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_263815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263815 prefixEnd_263815 := by exact prefixLift 263815
  have htrace : WordTrace (prefixWord ++ tailWord_263815) baseStart_263815 baseEnd_263815 := by
    simpa [prefixWord, tailWord_263815, baseEnd_263815] using wordTrace_append hprefix tailTrace_263815
  have hstable : (prefixWord ++ tailWord_263815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263815).length < 2 ^ (prefixWord ++ tailWord_263815).sum := by decide
  have hdescent : baseEnd_263815 < baseStart_263815 := by decide
  rcases family_descends (prefixWord ++ tailWord_263815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263822 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2]
def baseStart_263822 : Nat := 118140960795 + 263822 * 2 ^ 59
def prefixEnd_263822 : Nat := 4983230072969 + 3 ^ 40 * 263822 * 2
def baseEnd_263822 : Nat := 135467493230572028911711

theorem tailTrace_263822 : CollatzResearch.WordTrace tailWord_263822 prefixEnd_263822 135467493230572028911711 := by
  unfold tailWord_263822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202797356278178256940215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6414919233483617370347813 1202797356278178256940215)
  ·
    refine ⟨1804196034417267385410323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1202797356278178256940215 1804196034417267385410323)
    ·
      refine ⟨2706294051625901078115485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1804196034417267385410323 2706294051625901078115485)
      ·
        refine ⟨1014860269359712904293307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2706294051625901078115485 1014860269359712904293307)
        ·
          refine ⟨1522290404039569356439961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014860269359712904293307 1522290404039569356439961)
          ·
            refine ⟨1141717803029677017329971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522290404039569356439961 1141717803029677017329971)
            ·
              refine ⟨1712576704544515525994957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141717803029677017329971 1712576704544515525994957)
              ·
                refine ⟨642216264204193322248109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1712576704544515525994957 642216264204193322248109)
                ·
                  refine ⟨240831099076572495843041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642216264204193322248109 240831099076572495843041)
                  ·
                    refine ⟨180623324307429371882281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 240831099076572495843041 180623324307429371882281)
                    ·
                      refine ⟨135467493230572028911711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180623324307429371882281 135467493230572028911711)
                      ·
                        rfl

theorem cell23_263822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_263822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263822 prefixEnd_263822 := by exact prefixLift 263822
  have htrace : WordTrace (prefixWord ++ tailWord_263822) baseStart_263822 baseEnd_263822 := by
    simpa [prefixWord, tailWord_263822, baseEnd_263822] using wordTrace_append hprefix tailTrace_263822
  have hstable : (prefixWord ++ tailWord_263822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263822).length < 2 ^ (prefixWord ++ tailWord_263822).sum := by decide
  have hdescent : baseEnd_263822 < baseStart_263822 := by decide
  rcases family_descends (prefixWord ++ tailWord_263822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263832 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 2, 4]
def baseStart_263832 : Nat := 118140960795 + 263832 * 2 ^ 59
def prefixEnd_263832 : Nat := 4983230072969 + 3 ^ 40 * 263832 * 2
def baseEnd_263832 : Nat := 45157542679038996595555

theorem tailTrace_263832 : CollatzResearch.WordTrace tailWord_263832 prefixEnd_263832 45157542679038996595555 := by
  unfold tailWord_263832
  simp only [CollatzResearch.WordTrace]
  refine ⟨4811371790094598881692875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6415162386792798508923833 4811371790094598881692875)
  ·
    refine ⟨7217057685141898322539313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4811371790094598881692875 7217057685141898322539313)
    ·
      refine ⟨5412793263856423741904485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7217057685141898322539313 5412793263856423741904485)
      ·
        refine ⟨1014898736973079451607091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5412793263856423741904485 1014898736973079451607091)
        ·
          refine ⟨1522348105459619177410637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014898736973079451607091 1522348105459619177410637)
          ·
            refine ⟨570880539547357191528989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1522348105459619177410637 570880539547357191528989)
            ·
              refine ⟨214080202330258946823371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570880539547357191528989 214080202330258946823371)
              ·
                refine ⟨321120303495388420235057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214080202330258946823371 321120303495388420235057)
                ·
                  refine ⟨240840227621541315176293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321120303495388420235057 240840227621541315176293)
                  ·
                    refine ⟨45157542679038996595555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240840227621541315176293 45157542679038996595555)
                    ·
                      rfl

theorem cell23_263832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_263832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263832 prefixEnd_263832 := by exact prefixLift 263832
  have htrace : WordTrace (prefixWord ++ tailWord_263832) baseStart_263832 baseEnd_263832 := by
    simpa [prefixWord, tailWord_263832, baseEnd_263832] using wordTrace_append hprefix tailTrace_263832
  have hstable : (prefixWord ++ tailWord_263832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263832).length < 2 ^ (prefixWord ++ tailWord_263832).sum := by decide
  have hdescent : baseEnd_263832 < baseStart_263832 := by decide
  rcases family_descends (prefixWord ++ tailWord_263832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263889 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 2, 1, 3]
def baseStart_263889 : Nat := 118140960795 + 263889 * 2 ^ 59
def prefixEnd_263889 : Nat := 4983230072969 + 3 ^ 40 * 263889 * 2
def baseEnd_263889 : Nat := 135501896434423266773903

theorem tailTrace_263889 : CollatzResearch.WordTrace tailWord_263889 prefixEnd_263889 135501896434423266773903 := by
  unfold tailWord_263889
  simp only [CollatzResearch.WordTrace]
  refine ⟨9624822540982696498210721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6416548360655130998807147 9624822540982696498210721)
  ·
    refine ⟨7218616905737022373658041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9624822540982696498210721 7218616905737022373658041)
    ·
      refine ⟨5413962679302766780243531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7218616905737022373658041 5413962679302766780243531)
      ·
        refine ⟨8120944018954150170365297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5413962679302766780243531 8120944018954150170365297)
        ·
          refine ⟨6090708014215612627773973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8120944018954150170365297 6090708014215612627773973)
          ·
            refine ⟨285501938166356841926905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6090708014215612627773973 285501938166356841926905)
            ·
              refine ⟨214126453624767631445179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285501938166356841926905 214126453624767631445179)
              ·
                refine ⟨321189680437151447167769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214126453624767631445179 321189680437151447167769)
                ·
                  refine ⟨240892260327863585375827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321189680437151447167769 240892260327863585375827)
                  ·
                    refine ⟨361338390491795378063741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 240892260327863585375827 361338390491795378063741)
                    ·
                      refine ⟨135501896434423266773903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 361338390491795378063741 135501896434423266773903)
                      ·
                        rfl

theorem cell23_263889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 2, 1, 3].length) (baseStart_263889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263889 prefixEnd_263889 := by exact prefixLift 263889
  have htrace : WordTrace (prefixWord ++ tailWord_263889) baseStart_263889 baseEnd_263889 := by
    simpa [prefixWord, tailWord_263889, baseEnd_263889] using wordTrace_append hprefix tailTrace_263889
  have hstable : (prefixWord ++ tailWord_263889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263889).length < 2 ^ (prefixWord ++ tailWord_263889).sum := by decide
  have hdescent : baseEnd_263889 < baseStart_263889 := by decide
  rcases family_descends (prefixWord ++ tailWord_263889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263895 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 1, 4, 2]
def baseStart_263895 : Nat := 118140960795 + 263895 * 2 ^ 59
def prefixEnd_263895 : Nat := 4983230072969 + 3 ^ 40 * 263895 * 2
def baseEnd_263895 : Nat := 135504977318350243298875

theorem tailTrace_263895 : CollatzResearch.WordTrace tailWord_263895 prefixEnd_263895 135504977318350243298875 := by
  unfold tailWord_263895
  simp only [CollatzResearch.WordTrace]
  refine ⟨9625041378960959522929139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6416694252640639681952759 9625041378960959522929139)
  ·
    refine ⟨14437562068441439284393709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9625041378960959522929139 14437562068441439284393709)
    ·
      refine ⟨5414085775665539731647641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14437562068441439284393709 5414085775665539731647641)
      ·
        refine ⟨4060564331749154798735731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5414085775665539731647641 4060564331749154798735731)
        ·
          refine ⟨6090846497623732198103597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4060564331749154798735731 6090846497623732198103597)
          ·
            refine ⟨2284067436608899574288849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6090846497623732198103597 2284067436608899574288849)
            ·
              refine ⟨1713050577456674680716637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2284067436608899574288849 1713050577456674680716637)
              ·
                refine ⟨642393966546253005268739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1713050577456674680716637 642393966546253005268739)
                ·
                  refine ⟨963590949819379507903109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642393966546253005268739 963590949819379507903109)
                  ·
                    refine ⟨180673303091133657731833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 963590949819379507903109 180673303091133657731833)
                    ·
                      refine ⟨135504977318350243298875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180673303091133657731833 135504977318350243298875)
                      ·
                        rfl

theorem cell23_263895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_263895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263895 prefixEnd_263895 := by exact prefixLift 263895
  have htrace : WordTrace (prefixWord ++ tailWord_263895) baseStart_263895 baseEnd_263895 := by
    simpa [prefixWord, tailWord_263895, baseEnd_263895] using wordTrace_append hprefix tailTrace_263895
  have hstable : (prefixWord ++ tailWord_263895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263895).length < 2 ^ (prefixWord ++ tailWord_263895).sum := by decide
  have hdescent : baseEnd_263895 < baseStart_263895 := by decide
  rcases family_descends (prefixWord ++ tailWord_263895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263898 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_263898 : Nat := 118140960795 + 263898 * 2 ^ 59
def prefixEnd_263898 : Nat := 4983230072969 + 3 ^ 40 * 263898 * 2
def baseEnd_263898 : Nat := 135506517760313731561361

theorem tailTrace_263898 : CollatzResearch.WordTrace tailWord_263898 prefixEnd_263898 135506517760313731561361 := by
  unfold tailWord_263898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406287699487522758822087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6416767198633394023525565 2406287699487522758822087)
  ·
    refine ⟨3609431549231284138233131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2406287699487522758822087 3609431549231284138233131)
    ·
      refine ⟨5414147323846926207349697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3609431549231284138233131 5414147323846926207349697)
      ·
        refine ⟨4060610492885194655512273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5414147323846926207349697 4060610492885194655512273)
        ·
          refine ⟨3045457869663895991634205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4060610492885194655512273 3045457869663895991634205)
          ·
            refine ⟨1142046701123960996862827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3045457869663895991634205 1142046701123960996862827)
            ·
              refine ⟨1713070051685941495294241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142046701123960996862827 1713070051685941495294241)
              ·
                refine ⟨1284802538764456121470681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713070051685941495294241 1284802538764456121470681)
                ·
                  refine ⟨963601904073342091103011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1284802538764456121470681 963601904073342091103011)
                  ·
                    refine ⟨1445402856110013136654517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 963601904073342091103011 1445402856110013136654517)
                    ·
                      refine ⟨135506517760313731561361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1445402856110013136654517 135506517760313731561361)
                      ·
                        rfl

theorem cell23_263898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_263898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263898 prefixEnd_263898 := by exact prefixLift 263898
  have htrace : WordTrace (prefixWord ++ tailWord_263898) baseStart_263898 baseEnd_263898 := by
    simpa [prefixWord, tailWord_263898, baseEnd_263898] using wordTrace_append hprefix tailTrace_263898
  have hstable : (prefixWord ++ tailWord_263898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263898).length < 2 ^ (prefixWord ++ tailWord_263898).sum := by decide
  have hdescent : baseEnd_263898 < baseStart_263898 := by decide
  rcases family_descends (prefixWord ++ tailWord_263898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263912 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_263912 : Nat := 118140960795 + 263912 * 2 ^ 59
def prefixEnd_263912 : Nat := 4983230072969 + 3 ^ 40 * 263912 * 2
def baseEnd_263912 : Nat := 135513706489476676786297

theorem tailTrace_263912 : CollatzResearch.WordTrace tailWord_263912 prefixEnd_263912 135513706489476676786297 := by
  unfold tailWord_263912
  simp only [CollatzResearch.WordTrace]
  refine ⟨4812830709949685713148995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6417107613266247617531993 4812830709949685713148995)
  ·
    refine ⟨7219246064924528569723493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4812830709949685713148995 7219246064924528569723493)
    ·
      refine ⟨1353608637173349106823155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7219246064924528569723493 1353608637173349106823155)
      ·
        refine ⟨2030412955760023660234733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353608637173349106823155 2030412955760023660234733)
        ·
          refine ⟨761404858410008872588025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2030412955760023660234733 761404858410008872588025)
          ·
            refine ⟨571053643807506654441019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761404858410008872588025 571053643807506654441019)
            ·
              refine ⟨856580465711259981661529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571053643807506654441019 856580465711259981661529)
              ·
                refine ⟨642435349283444986246147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856580465711259981661529 642435349283444986246147)
                ·
                  refine ⟨963653023925167479369221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642435349283444986246147 963653023925167479369221)
                  ·
                    refine ⟨180684941985968902381729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 963653023925167479369221 180684941985968902381729)
                    ·
                      refine ⟨135513706489476676786297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180684941985968902381729 135513706489476676786297)
                      ·
                        rfl

theorem cell23_263912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_263912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263912 prefixEnd_263912 := by exact prefixLift 263912
  have htrace : WordTrace (prefixWord ++ tailWord_263912) baseStart_263912 baseEnd_263912 := by
    simpa [prefixWord, tailWord_263912, baseEnd_263912] using wordTrace_append hprefix tailTrace_263912
  have hstable : (prefixWord ++ tailWord_263912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263912).length < 2 ^ (prefixWord ++ tailWord_263912).sum := by decide
  have hdescent : baseEnd_263912 < baseStart_263912 := by decide
  rcases family_descends (prefixWord ++ tailWord_263912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263948 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_263948 : Nat := 118140960795 + 263948 * 2 ^ 59
def prefixEnd_263948 : Nat := 4983230072969 + 3 ^ 40 * 263948 * 2
def baseEnd_263948 : Nat := 45177397264346178645377

theorem tailTrace_263948 : CollatzResearch.WordTrace tailWord_263948 prefixEnd_263948 45177397264346178645377 := by
  unfold tailWord_263948
  simp only [CollatzResearch.WordTrace]
  refine ⟨4813487223884474787304249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6417982965179299716405665 4813487223884474787304249)
  ·
    refine ⟨3610115417913356090478187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4813487223884474787304249 3610115417913356090478187)
    ·
      refine ⟨5415173126870034135717281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3610115417913356090478187 5415173126870034135717281)
      ·
        refine ⟨4061379845152525601787961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5415173126870034135717281 4061379845152525601787961)
        ·
          refine ⟨3046034883864394201340971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4061379845152525601787961 3046034883864394201340971)
          ·
            refine ⟨4569052325796591302011457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046034883864394201340971 4569052325796591302011457)
            ·
              refine ⟨3426789244347443476508593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4569052325796591302011457 3426789244347443476508593)
              ·
                refine ⟨2570091933260582607381445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3426789244347443476508593 2570091933260582607381445)
                ·
                  refine ⟨481892237486359238884021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2570091933260582607381445 481892237486359238884021)
                  ·
                    refine ⟨45177397264346178645377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 481892237486359238884021 45177397264346178645377)
                    ·
                      rfl

theorem cell23_263948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_263948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_263948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_263948 prefixEnd_263948 := by exact prefixLift 263948
  have htrace : WordTrace (prefixWord ++ tailWord_263948) baseStart_263948 baseEnd_263948 := by
    simpa [prefixWord, tailWord_263948, baseEnd_263948] using wordTrace_append hprefix tailTrace_263948
  have hstable : (prefixWord ++ tailWord_263948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263948).length < 2 ^ (prefixWord ++ tailWord_263948).sum := by decide
  have hdescent : baseEnd_263948 < baseStart_263948 := by decide
  rcases family_descends (prefixWord ++ tailWord_263948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264048 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_264048 : Nat := 118140960795 + 264048 * 2 ^ 59
def prefixEnd_264048 : Nat := 4983230072969 + 3 ^ 40 * 264048 * 2
def baseEnd_264048 : Nat := 135583539858488144685671

theorem tailTrace_264048 : CollatzResearch.WordTrace tailWord_264048 prefixEnd_264048 135583539858488144685671 := by
  unfold tailWord_264048
  simp only [CollatzResearch.WordTrace]
  refine ⟨4815310873703333326624399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6420414498271111102165865 4815310873703333326624399)
  ·
    refine ⟨7222966310554999989936599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4815310873703333326624399 7222966310554999989936599)
    ·
      refine ⟨10834449465832499984904899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7222966310554999989936599 10834449465832499984904899)
      ·
        refine ⟨16251674198748749977357349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10834449465832499984904899 16251674198748749977357349)
        ·
          refine ⟨3047188912265390620754503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16251674198748749977357349 3047188912265390620754503)
          ·
            refine ⟨4570783368398085931131755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3047188912265390620754503 4570783368398085931131755)
            ·
              refine ⟨6856175052597128896697633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570783368398085931131755 6856175052597128896697633)
              ·
                refine ⟨5142131289447846672523225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6856175052597128896697633 5142131289447846672523225)
                ·
                  refine ⟨3856598467085885004392419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5142131289447846672523225 3856598467085885004392419)
                  ·
                    refine ⟨5784897700628827506588629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3856598467085885004392419 5784897700628827506588629)
                    ·
                      refine ⟨135583539858488144685671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5784897700628827506588629 135583539858488144685671)
                      ·
                        rfl

theorem cell23_264048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_264048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264048 prefixEnd_264048 := by exact prefixLift 264048
  have htrace : WordTrace (prefixWord ++ tailWord_264048) baseStart_264048 baseEnd_264048 := by
    simpa [prefixWord, tailWord_264048, baseEnd_264048] using wordTrace_append hprefix tailTrace_264048
  have hstable : (prefixWord ++ tailWord_264048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264048).length < 2 ^ (prefixWord ++ tailWord_264048).sum := by decide
  have hdescent : baseEnd_264048 < baseStart_264048 := by decide
  rcases family_descends (prefixWord ++ tailWord_264048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264072 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 3, 5]
def baseStart_264072 : Nat := 118140960795 + 264072 * 2 ^ 59
def prefixEnd_264072 : Nat := 4983230072969 + 3 ^ 40 * 264072 * 2
def baseEnd_264072 : Nat := 45198621131398683595187

theorem tailTrace_264072 : CollatzResearch.WordTrace tailWord_264072 prefixEnd_264072 45198621131398683595187 := by
  unfold tailWord_264072
  simp only [CollatzResearch.WordTrace]
  refine ⟨4815748549659859376061235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6420998066213145834748313 4815748549659859376061235)
  ·
    refine ⟨7223622824489789064091853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4815748549659859376061235 7223622824489789064091853)
    ·
      refine ⟨2708858559183670899034445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7223622824489789064091853 2708858559183670899034445)
      ·
        refine ⟨1015821959693876587137917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2708858559183670899034445 1015821959693876587137917)
        ·
          refine ⟨380933234885203720176719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1015821959693876587137917 380933234885203720176719)
          ·
            refine ⟨571399852327805580265079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380933234885203720176719 571399852327805580265079)
            ·
              refine ⟨857099778491708370397619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571399852327805580265079 857099778491708370397619)
              ·
                refine ⟨1285649667737562555596429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857099778491708370397619 1285649667737562555596429)
                ·
                  refine ⟨482118625401585958348661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1285649667737562555596429 482118625401585958348661)
                  ·
                    refine ⟨45198621131398683595187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 482118625401585958348661 45198621131398683595187)
                    ·
                      rfl

theorem cell23_264072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_264072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264072 prefixEnd_264072 := by exact prefixLift 264072
  have htrace : WordTrace (prefixWord ++ tailWord_264072) baseStart_264072 baseEnd_264072 := by
    simpa [prefixWord, tailWord_264072, baseEnd_264072] using wordTrace_append hprefix tailTrace_264072
  have hstable : (prefixWord ++ tailWord_264072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264072).length < 2 ^ (prefixWord ++ tailWord_264072).sum := by decide
  have hdescent : baseEnd_264072 < baseStart_264072 := by decide
  rcases family_descends (prefixWord ++ tailWord_264072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264085 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_264085 : Nat := 118140960795 + 264085 * 2 ^ 59
def prefixEnd_264085 : Nat := 4983230072969 + 3 ^ 40 * 264085 * 2
def baseEnd_264085 : Nat := 45200846214234833307667

theorem tailTrace_264085 : CollatzResearch.WordTrace tailWord_264085 prefixEnd_264085 45200846214234833307667 := by
  unfold tailWord_264085
  simp only [CollatzResearch.WordTrace]
  refine ⟨9631971248272621972345709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6421314165515081314897139 9631971248272621972345709)
  ·
    refine ⟨3611989218102233239629641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9631971248272621972345709 3611989218102233239629641)
    ·
      refine ⟨2708991913576674929722231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3611989218102233239629641 2708991913576674929722231)
      ·
        refine ⟨4063487870365012394583347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2708991913576674929722231 4063487870365012394583347)
        ·
          refine ⟨6095231805547518591875021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063487870365012394583347 6095231805547518591875021)
          ·
            refine ⟨2285711927080319471953133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6095231805547518591875021 2285711927080319471953133)
            ·
              refine ⟨857141972655119801982425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2285711927080319471953133 857141972655119801982425)
              ·
                refine ⟨642856479491339851486819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857141972655119801982425 642856479491339851486819)
                ·
                  refine ⟨964284719237009777230229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642856479491339851486819 964284719237009777230229)
                  ·
                    refine ⟨45200846214234833307667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 964284719237009777230229 45200846214234833307667)
                    ·
                      rfl

theorem cell23_264085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_264085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264085 prefixEnd_264085 := by exact prefixLift 264085
  have htrace : WordTrace (prefixWord ++ tailWord_264085) baseStart_264085 baseEnd_264085 := by
    simpa [prefixWord, tailWord_264085, baseEnd_264085] using wordTrace_append hprefix tailTrace_264085
  have hstable : (prefixWord ++ tailWord_264085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264085).length < 2 ^ (prefixWord ++ tailWord_264085).sum := by decide
  have hdescent : baseEnd_264085 < baseStart_264085 := by decide
  rcases family_descends (prefixWord ++ tailWord_264085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264103 : List Nat := [1, 1, 6, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_264103 : Nat := 118140960795 + 264103 * 2 ^ 59
def prefixEnd_264103 : Nat := 4983230072969 + 3 ^ 40 * 264103 * 2
def baseEnd_264103 : Nat := 135611781294485429497919

theorem tailTrace_264103 : CollatzResearch.WordTrace tailWord_264103 prefixEnd_264103 135611781294485429497919 := by
  unfold tailWord_264103
  simp only [CollatzResearch.WordTrace]
  refine ⟨9632627762207411046500963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6421751841471607364333975 9632627762207411046500963)
  ·
    refine ⟨14448941643311116569751445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9632627762207411046500963 14448941643311116569751445)
    ·
      refine ⟨677294139530208589207099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14448941643311116569751445 677294139530208589207099)
      ·
        refine ⟨1015941209295312883810649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677294139530208589207099 1015941209295312883810649)
        ·
          refine ⟨761955906971484662857987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015941209295312883810649 761955906971484662857987)
          ·
            refine ⟨1142933860457226994286981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761955906971484662857987 1142933860457226994286981)
            ·
              refine ⟨214300098835730061428809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1142933860457226994286981 214300098835730061428809)
              ·
                refine ⟨160725074126797546071607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214300098835730061428809 160725074126797546071607)
                ·
                  refine ⟨241087611190196319107411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160725074126797546071607 241087611190196319107411)
                  ·
                    refine ⟨361631416785294478661117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241087611190196319107411 361631416785294478661117)
                    ·
                      refine ⟨135611781294485429497919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 361631416785294478661117 135611781294485429497919)
                      ·
                        rfl

theorem cell23_264103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_264103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264103 prefixEnd_264103 := by exact prefixLift 264103
  have htrace : WordTrace (prefixWord ++ tailWord_264103) baseStart_264103 baseEnd_264103 := by
    simpa [prefixWord, tailWord_264103, baseEnd_264103] using wordTrace_append hprefix tailTrace_264103
  have hstable : (prefixWord ++ tailWord_264103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264103).length < 2 ^ (prefixWord ++ tailWord_264103).sum := by decide
  have hdescent : baseEnd_264103 < baseStart_264103 := by decide
  rcases family_descends (prefixWord ++ tailWord_264103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264126 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_264126 : Nat := 118140960795 + 264126 * 2 ^ 59
def prefixEnd_264126 : Nat := 4983230072969 + 3 ^ 40 * 264126 * 2
def baseEnd_264126 : Nat := 135623591349538839510313

theorem tailTrace_264126 : CollatzResearch.WordTrace tailWord_264126 prefixEnd_264126 135623591349538839510313 := by
  unfold tailWord_264126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204183330140510746823529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6422311094082723983058821 1204183330140510746823529)
  ·
    refine ⟨903137497605383060117647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1204183330140510746823529 903137497605383060117647)
    ·
      refine ⟨1354706246408074590176471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 903137497605383060117647 1354706246408074590176471)
      ·
        refine ⟨2032059369612111885264707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1354706246408074590176471 2032059369612111885264707)
        ·
          refine ⟨3048089054418167827897061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2032059369612111885264707 3048089054418167827897061)
          ·
            refine ⟨571516697703406467730699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3048089054418167827897061 571516697703406467730699)
            ·
              refine ⟨857275046555109701596049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571516697703406467730699 857275046555109701596049)
              ·
                refine ⟨642956284916332276197037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 857275046555109701596049 642956284916332276197037)
                ·
                  refine ⟨241108606843624603573889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 642956284916332276197037 241108606843624603573889)
                  ·
                    refine ⟨180831455132718452680417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241108606843624603573889 180831455132718452680417)
                    ·
                      refine ⟨135623591349538839510313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180831455132718452680417 135623591349538839510313)
                      ·
                        rfl

theorem cell23_264126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_264126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264126 prefixEnd_264126 := by exact prefixLift 264126
  have htrace : WordTrace (prefixWord ++ tailWord_264126) baseStart_264126 baseEnd_264126 := by
    simpa [prefixWord, tailWord_264126, baseEnd_264126] using wordTrace_append hprefix tailTrace_264126
  have hstable : (prefixWord ++ tailWord_264126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264126).length < 2 ^ (prefixWord ++ tailWord_264126).sum := by decide
  have hdescent : baseEnd_264126 < baseStart_264126 := by decide
  rcases family_descends (prefixWord ++ tailWord_264126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264142 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_264142 : Nat := 118140960795 + 264142 * 2 ^ 59
def prefixEnd_264142 : Nat := 4983230072969 + 3 ^ 40 * 264142 * 2
def baseEnd_264142 : Nat := 135631807040010776910239

theorem tailTrace_264142 : CollatzResearch.WordTrace tailWord_264142 prefixEnd_264142 135631807040010776910239 := by
  unfold tailWord_264142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204256276133265088396335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6422700139377413804780453 1204256276133265088396335)
  ·
    refine ⟨1806384414199897632594503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1204256276133265088396335 1806384414199897632594503)
    ·
      refine ⟨2709576621299846448891755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1806384414199897632594503 2709576621299846448891755)
      ·
        refine ⟨4064364931949769673337633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2709576621299846448891755 4064364931949769673337633)
        ·
          refine ⟨3048273698962327255003225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4064364931949769673337633 3048273698962327255003225)
          ·
            refine ⟨2286205274221745441252419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3048273698962327255003225 2286205274221745441252419)
            ·
              refine ⟨3429307911332618161878629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2286205274221745441252419 3429307911332618161878629)
              ·
                refine ⟨642995233374865905352243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3429307911332618161878629 642995233374865905352243)
                ·
                  refine ⟨964492850062298858028365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642995233374865905352243 964492850062298858028365)
                  ·
                    refine ⟨361684818773362071760637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 964492850062298858028365 361684818773362071760637)
                    ·
                      refine ⟨135631807040010776910239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 361684818773362071760637 135631807040010776910239)
                      ·
                        rfl

theorem cell23_264142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_264142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264142 prefixEnd_264142 := by exact prefixLift 264142
  have htrace : WordTrace (prefixWord ++ tailWord_264142) baseStart_264142 baseEnd_264142 := by
    simpa [prefixWord, tailWord_264142, baseEnd_264142] using wordTrace_append hprefix tailTrace_264142
  have hstable : (prefixWord ++ tailWord_264142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264142).length < 2 ^ (prefixWord ++ tailWord_264142).sum := by decide
  have hdescent : baseEnd_264142 < baseStart_264142 := by decide
  rcases family_descends (prefixWord ++ tailWord_264142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264146 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_264146 : Nat := 118140960795 + 264146 * 2 ^ 59
def prefixEnd_264146 : Nat := 4983230072969 + 3 ^ 40 * 264146 * 2
def baseEnd_264146 : Nat := 135633860962628761260221

theorem tailTrace_264146 : CollatzResearch.WordTrace tailWord_264146 prefixEnd_264146 135633860962628761260221 := by
  unfold tailWord_264146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2408549025262907347579073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6422797400701086260210861 2408549025262907347579073)
  ·
    refine ⟨1806411768947180510684305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2408549025262907347579073 1806411768947180510684305)
    ·
      refine ⟨1354808826710385383013229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1806411768947180510684305 1354808826710385383013229)
      ·
        refine ⟨508053310016394518629961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1354808826710385383013229 508053310016394518629961)
        ·
          refine ⟨381039982512295888972471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508053310016394518629961 381039982512295888972471)
          ·
            refine ⟨571559973768443833458707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381039982512295888972471 571559973768443833458707)
            ·
              refine ⟨857339960652665750188061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571559973768443833458707 857339960652665750188061)
              ·
                refine ⟨321502485244749656320523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 857339960652665750188061 321502485244749656320523)
                ·
                  refine ⟨482253727867124484480785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321502485244749656320523 482253727867124484480785)
                  ·
                    refine ⟨361690295900343363360589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 482253727867124484480785 361690295900343363360589)
                    ·
                      refine ⟨135633860962628761260221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 361690295900343363360589 135633860962628761260221)
                      ·
                        rfl

theorem cell23_264146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_264146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264146 prefixEnd_264146 := by exact prefixLift 264146
  have htrace : WordTrace (prefixWord ++ tailWord_264146) baseStart_264146 baseEnd_264146 := by
    simpa [prefixWord, tailWord_264146, baseEnd_264146] using wordTrace_append hprefix tailTrace_264146
  have hstable : (prefixWord ++ tailWord_264146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264146).length < 2 ^ (prefixWord ++ tailWord_264146).sum := by decide
  have hdescent : baseEnd_264146 < baseStart_264146 := by decide
  rcases family_descends (prefixWord ++ tailWord_264146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264159 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 4, 1, 3]
def baseStart_264159 : Nat := 118140960795 + 264159 * 2 ^ 59
def prefixEnd_264159 : Nat := 4983230072969 + 3 ^ 40 * 264159 * 2
def baseEnd_264159 : Nat := 135640536211137210397661

theorem tailTrace_264159 : CollatzResearch.WordTrace tailWord_264159 prefixEnd_264159 135640536211137210397661 := by
  unfold tailWord_264159
  simp only [CollatzResearch.WordTrace]
  refine ⟨9634670250004532610539531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6423113500003021740359687 9634670250004532610539531)
  ·
    refine ⟨14452005375006798915809297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9634670250004532610539531 14452005375006798915809297)
    ·
      refine ⟨10839004031255099186856973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14452005375006798915809297 10839004031255099186856973)
      ·
        refine ⟨4064626511720662195071365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10839004031255099186856973 4064626511720662195071365)
        ·
          refine ⟨762117470947624161575881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4064626511720662195071365 762117470947624161575881)
          ·
            refine ⟨571588103210718121181911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762117470947624161575881 571588103210718121181911)
            ·
              refine ⟨857382154816077181772867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571588103210718121181911 857382154816077181772867)
              ·
                refine ⟨1286073232224115772659301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857382154816077181772867 1286073232224115772659301)
                ·
                  refine ⟨241138731042021707373619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1286073232224115772659301 241138731042021707373619)
                  ·
                    refine ⟨361708096563032561060429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241138731042021707373619 361708096563032561060429)
                    ·
                      refine ⟨135640536211137210397661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 361708096563032561060429 135640536211137210397661)
                      ·
                        rfl

theorem cell23_264159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_264159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264159 prefixEnd_264159 := by exact prefixLift 264159
  have htrace : WordTrace (prefixWord ++ tailWord_264159) baseStart_264159 baseEnd_264159 := by
    simpa [prefixWord, tailWord_264159, baseEnd_264159] using wordTrace_append hprefix tailTrace_264159
  have hstable : (prefixWord ++ tailWord_264159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264159).length < 2 ^ (prefixWord ++ tailWord_264159).sum := by decide
  have hdescent : baseEnd_264159 < baseStart_264159 := by decide
  rcases family_descends (prefixWord ++ tailWord_264159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264173 : List Nat := [1, 5, 1, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_264173 : Nat := 118140960795 + 264173 * 2 ^ 59
def prefixEnd_264173 : Nat := 4983230072969 + 3 ^ 40 * 264173 * 2
def baseEnd_264173 : Nat := 135647724940300155622597

theorem tailTrace_264173 : CollatzResearch.WordTrace tailWord_264173 prefixEnd_264173 135647724940300155622597 := by
  unfold tailWord_264173
  simp only [CollatzResearch.WordTrace]
  refine ⟨9635180871953813001549173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6423453914635875334366115 9635180871953813001549173)
  ·
    refine ⟨903298206745669968895235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9635180871953813001549173 903298206745669968895235)
    ·
      refine ⟨1354947310118504953342853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 903298206745669968895235 1354947310118504953342853)
      ·
        refine ⟨254052620647219678751785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1354947310118504953342853 254052620647219678751785)
        ·
          refine ⟨190539465485414759063839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254052620647219678751785 190539465485414759063839)
          ·
            refine ⟨285809198228122138595759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190539465485414759063839 285809198228122138595759)
            ·
              refine ⟨428713797342183207893639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285809198228122138595759 428713797342183207893639)
              ·
                refine ⟨643070696013274811840459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428713797342183207893639 643070696013274811840459)
                ·
                  refine ⟨964606044019912217760689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643070696013274811840459 964606044019912217760689)
                  ·
                    refine ⟨723454533014934163320517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 964606044019912217760689 723454533014934163320517)
                    ·
                      refine ⟨135647724940300155622597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 723454533014934163320517 135647724940300155622597)
                      ·
                        rfl

theorem cell23_264173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_264173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264173 prefixEnd_264173 := by exact prefixLift 264173
  have htrace : WordTrace (prefixWord ++ tailWord_264173) baseStart_264173 baseEnd_264173 := by
    simpa [prefixWord, tailWord_264173, baseEnd_264173] using wordTrace_append hprefix tailTrace_264173
  have hstable : (prefixWord ++ tailWord_264173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264173).length < 2 ^ (prefixWord ++ tailWord_264173).sum := by decide
  have hdescent : baseEnd_264173 < baseStart_264173 := by decide
  rcases family_descends (prefixWord ++ tailWord_264173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264175 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 2, 6]
def baseStart_264175 : Nat := 118140960795 + 264175 * 2 ^ 59
def prefixEnd_264175 : Nat := 4983230072969 + 3 ^ 40 * 264175 * 2
def baseEnd_264175 : Nat := 45216250633869715932529

theorem tailTrace_264175 : CollatzResearch.WordTrace tailWord_264175 prefixEnd_264175 45216250633869715932529 := by
  unfold tailWord_264175
  simp only [CollatzResearch.WordTrace]
  refine ⟨9635253817946567343121979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6423502545297711562081319 9635253817946567343121979)
  ·
    refine ⟨14452880726919851014682969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9635253817946567343121979 14452880726919851014682969)
    ·
      refine ⟨10839660545189888261012227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14452880726919851014682969 10839660545189888261012227)
      ·
        refine ⟨16259490817784832391518341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10839660545189888261012227 16259490817784832391518341)
        ·
          refine ⟨3048654528334656073409689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16259490817784832391518341 3048654528334656073409689)
          ·
            refine ⟨2286490896250992055057267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3048654528334656073409689 2286490896250992055057267)
            ·
              refine ⟨3429736344376488082585901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2286490896250992055057267 3429736344376488082585901)
              ·
                refine ⟨1286151129141183030969713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3429736344376488082585901 1286151129141183030969713)
                ·
                  refine ⟨964613346855887273227285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1286151129141183030969713 964613346855887273227285)
                  ·
                    refine ⟨45216250633869715932529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 964613346855887273227285 45216250633869715932529)
                    ·
                      rfl

theorem cell23_264175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_264175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264175 prefixEnd_264175 := by exact prefixLift 264175
  have htrace : WordTrace (prefixWord ++ tailWord_264175) baseStart_264175 baseEnd_264175 := by
    simpa [prefixWord, tailWord_264175, baseEnd_264175] using wordTrace_append hprefix tailTrace_264175
  have hstable : (prefixWord ++ tailWord_264175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264175).length < 2 ^ (prefixWord ++ tailWord_264175).sum := by decide
  have hdescent : baseEnd_264175 < baseStart_264175 := by decide
  rcases family_descends (prefixWord ++ tailWord_264175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264195 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 4]
def baseStart_264195 : Nat := 118140960795 + 264195 * 2 ^ 59
def prefixEnd_264195 : Nat := 4983230072969 + 3 ^ 40 * 264195 * 2
def baseEnd_264195 : Nat := 135659021514699069547495

theorem tailTrace_264195 : CollatzResearch.WordTrace tailWord_264195 prefixEnd_264195 135659021514699069547495 := by
  unfold tailWord_264195
  simp only [CollatzResearch.WordTrace]
  refine ⟨9635983277874110758850039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6423988851916073839233359 9635983277874110758850039)
  ·
    refine ⟨14453974916811166138275059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9635983277874110758850039 14453974916811166138275059)
    ·
      refine ⟨21680962375216749207412589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14453974916811166138275059 21680962375216749207412589)
      ·
        refine ⟨8130360890706280952779721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21680962375216749207412589 8130360890706280952779721)
        ·
          refine ⟨6097770668029710714584791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8130360890706280952779721 6097770668029710714584791)
          ·
            refine ⟨9146656002044566071877187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6097770668029710714584791 9146656002044566071877187)
            ·
              refine ⟨13719984003066849107815781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9146656002044566071877187 13719984003066849107815781)
              ·
                refine ⟨2572497000575034207715459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13719984003066849107815781 2572497000575034207715459)
                ·
                  refine ⟨3858745500862551311573189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572497000575034207715459 3858745500862551311573189)
                  ·
                    refine ⟨723514781411728370919973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3858745500862551311573189 723514781411728370919973)
                    ·
                      refine ⟨135659021514699069547495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 723514781411728370919973 135659021514699069547495)
                      ·
                        rfl

theorem cell23_264195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_264195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264195 prefixEnd_264195 := by exact prefixLift 264195
  have htrace : WordTrace (prefixWord ++ tailWord_264195) baseStart_264195 baseEnd_264195 := by
    simpa [prefixWord, tailWord_264195, baseEnd_264195] using wordTrace_append hprefix tailTrace_264195
  have hstable : (prefixWord ++ tailWord_264195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264195).length < 2 ^ (prefixWord ++ tailWord_264195).sum := by decide
  have hdescent : baseEnd_264195 < baseStart_264195 := by decide
  rcases family_descends (prefixWord ++ tailWord_264195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264216 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 2, 2, 2]
def baseStart_264216 : Nat := 118140960795 + 264216 * 2 ^ 59
def prefixEnd_264216 : Nat := 4983230072969 + 3 ^ 40 * 264216 * 2
def baseEnd_264216 : Nat := 135669804608443487384899

theorem tailTrace_264216 : CollatzResearch.WordTrace tailWord_264216 prefixEnd_264216 135669804608443487384899 := by
  unfold tailWord_264216
  simp only [CollatzResearch.WordTrace]
  refine ⟨4818374605399015672682251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6424499473865354230243001 4818374605399015672682251)
  ·
    refine ⟨7227561908098523509023377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4818374605399015672682251 7227561908098523509023377)
    ·
      refine ⟨5420671431073892631767533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7227561908098523509023377 5420671431073892631767533)
      ·
        refine ⟨2032751786652709736912825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5420671431073892631767533 2032751786652709736912825)
        ·
          refine ⟨1524563839989532302684619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2032751786652709736912825 1524563839989532302684619)
          ·
            refine ⟨2286845759984298454026929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524563839989532302684619 2286845759984298454026929)
            ·
              refine ⟨1715134319988223840520197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2286845759984298454026929 1715134319988223840520197)
              ·
                refine ⟨321587684997791970097537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1715134319988223840520197 321587684997791970097537)
                ·
                  refine ⟨241190763748343977573153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321587684997791970097537 241190763748343977573153)
                  ·
                    refine ⟨180893072811257983179865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241190763748343977573153 180893072811257983179865)
                    ·
                      refine ⟨135669804608443487384899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 180893072811257983179865 135669804608443487384899)
                      ·
                        rfl

theorem cell23_264216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_264216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264216 prefixEnd_264216 := by exact prefixLift 264216
  have htrace : WordTrace (prefixWord ++ tailWord_264216) baseStart_264216 baseEnd_264216 := by
    simpa [prefixWord, tailWord_264216, baseEnd_264216] using wordTrace_append hprefix tailTrace_264216
  have hstable : (prefixWord ++ tailWord_264216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264216).length < 2 ^ (prefixWord ++ tailWord_264216).sum := by decide
  have hdescent : baseEnd_264216 < baseStart_264216 := by decide
  rcases family_descends (prefixWord ++ tailWord_264216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264235 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 1, 7]
def baseStart_264235 : Nat := 118140960795 + 264235 * 2 ^ 59
def prefixEnd_264235 : Nat := 4983230072969 + 3 ^ 40 * 264235 * 2
def baseEnd_264235 : Nat := 45226520246959637682437

theorem tailTrace_264235 : CollatzResearch.WordTrace tailWord_264235 prefixEnd_264235 45226520246959637682437 := by
  unfold tailWord_264235
  simp only [CollatzResearch.WordTrace]
  refine ⟨9637442197729197590306159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6424961465152798393537439 9637442197729197590306159)
  ·
    refine ⟨14456163296593796385459239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9637442197729197590306159 14456163296593796385459239)
    ·
      refine ⟨21684244944890694578188859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14456163296593796385459239 21684244944890694578188859)
      ·
        refine ⟨32526367417336041867283289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21684244944890694578188859 32526367417336041867283289)
        ·
          refine ⟨24394775563002031400462467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32526367417336041867283289 24394775563002031400462467)
          ·
            refine ⟨36592163344503047100693701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24394775563002031400462467 36592163344503047100693701)
            ·
              refine ⟨6861030627094321331380069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36592163344503047100693701 6861030627094321331380069)
              ·
                refine ⟨1286443242580185249633763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6861030627094321331380069 1286443242580185249633763)
                ·
                  refine ⟨1929664863870277874450645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286443242580185249633763 1929664863870277874450645)
                  ·
                    refine ⟨45226520246959637682437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1929664863870277874450645 45226520246959637682437)
                    ·
                      rfl

theorem cell23_264235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 7].length) (baseStart_264235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264235 prefixEnd_264235 := by exact prefixLift 264235
  have htrace : WordTrace (prefixWord ++ tailWord_264235) baseStart_264235 baseEnd_264235 := by
    simpa [prefixWord, tailWord_264235, baseEnd_264235] using wordTrace_append hprefix tailTrace_264235
  have hstable : (prefixWord ++ tailWord_264235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264235).length < 2 ^ (prefixWord ++ tailWord_264235).sum := by decide
  have hdescent : baseEnd_264235 < baseStart_264235 := by decide
  rcases family_descends (prefixWord ++ tailWord_264235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264269 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_264269 : Nat := 118140960795 + 264269 * 2 ^ 59
def prefixEnd_264269 : Nat := 4983230072969 + 3 ^ 40 * 264269 * 2
def baseEnd_264269 : Nat := 45232339694377260007385

theorem tailTrace_264269 : CollatzResearch.WordTrace tailWord_264269 prefixEnd_264269 45232339694377260007385 := by
  unfold tailWord_264269
  simp only [CollatzResearch.WordTrace]
  refine ⟨9638682279606021397043861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6425788186404014264695907 9638682279606021397043861)
  ·
    refine ⟨451813231856532252986431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9638682279606021397043861 451813231856532252986431)
    ·
      refine ⟨677719847784798379479647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451813231856532252986431 677719847784798379479647)
      ·
        refine ⟨1016579771677197569219471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677719847784798379479647 1016579771677197569219471)
        ·
          refine ⟨1524869657515796353829207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016579771677197569219471 1524869657515796353829207)
          ·
            refine ⟨2287304486273694530743811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1524869657515796353829207 2287304486273694530743811)
            ·
              refine ⟨3430956729410541796115717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2287304486273694530743811 3430956729410541796115717)
              ·
                refine ⟨643304386764476586771697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3430956729410541796115717 643304386764476586771697)
                ·
                  refine ⟨482478290073357440078773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 643304386764476586771697 482478290073357440078773)
                  ·
                    refine ⟨45232339694377260007385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 482478290073357440078773 45232339694377260007385)
                    ·
                      rfl

theorem cell23_264269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_264269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264269 prefixEnd_264269 := by exact prefixLift 264269
  have htrace : WordTrace (prefixWord ++ tailWord_264269) baseStart_264269 baseEnd_264269 := by
    simpa [prefixWord, tailWord_264269, baseEnd_264269] using wordTrace_append hprefix tailTrace_264269
  have hstable : (prefixWord ++ tailWord_264269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264269).length < 2 ^ (prefixWord ++ tailWord_264269).sum := by decide
  have hdescent : baseEnd_264269 < baseStart_264269 := by decide
  rcases family_descends (prefixWord ++ tailWord_264269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264306 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_264306 : Nat := 118140960795 + 264306 * 2 ^ 59
def prefixEnd_264306 : Nat := 4983230072969 + 3 ^ 40 * 264306 * 2
def baseEnd_264306 : Nat := 135716017867348135259485

theorem tailTrace_264306 : CollatzResearch.WordTrace tailWord_264306 prefixEnd_264306 135716017867348135259485 := by
  unfold tailWord_264306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2410007945117994179035193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6426687853647984477427181 2410007945117994179035193)
  ·
    refine ⟨1807505958838495634276395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2410007945117994179035193 1807505958838495634276395)
    ·
      refine ⟨2711258938257743451414593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1807505958838495634276395 2711258938257743451414593)
      ·
        refine ⟨2033444203693307588560945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2711258938257743451414593 2033444203693307588560945)
        ·
          refine ⟨1525083152769980691420709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2033444203693307588560945 1525083152769980691420709)
          ·
            refine ⟨285953091144371379641383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1525083152769980691420709 285953091144371379641383)
            ·
              refine ⟨428929636716557069462075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285953091144371379641383 428929636716557069462075)
              ·
                refine ⟨643394455074835604193113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428929636716557069462075 643394455074835604193113)
                ·
                  refine ⟨482545841306126703144835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 643394455074835604193113 482545841306126703144835)
                  ·
                    refine ⟨723818761959190054717253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 482545841306126703144835 723818761959190054717253)
                    ·
                      refine ⟨135716017867348135259485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 723818761959190054717253 135716017867348135259485)
                      ·
                        rfl

theorem cell23_264306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_264306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264306 prefixEnd_264306 := by exact prefixLift 264306
  have htrace : WordTrace (prefixWord ++ tailWord_264306) baseStart_264306 baseEnd_264306 := by
    simpa [prefixWord, tailWord_264306, baseEnd_264306] using wordTrace_append hprefix tailTrace_264306
  have hstable : (prefixWord ++ tailWord_264306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264306).length < 2 ^ (prefixWord ++ tailWord_264306).sum := by decide
  have hdescent : baseEnd_264306 < baseStart_264306 := by decide
  rcases family_descends (prefixWord ++ tailWord_264306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264316 : List Nat := [2, 2, 2, 1, 1, 4, 1, 5, 1, 4]
def baseStart_264316 : Nat := 118140960795 + 264316 * 2 ^ 59
def prefixEnd_264316 : Nat := 4983230072969 + 3 ^ 40 * 264316 * 2
def baseEnd_264316 : Nat := 45240384224631032044813

theorem tailTrace_264316 : CollatzResearch.WordTrace tailWord_264316 prefixEnd_264316 45240384224631032044813 := by
  unfold tailWord_264316
  simp only [CollatzResearch.WordTrace]
  refine ⟨4820198255217874212002401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6426931006957165616003201 4820198255217874212002401)
  ·
    refine ⟨3615148691413405659001801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4820198255217874212002401 3615148691413405659001801)
    ·
      refine ⟨2711361518560054244251351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3615148691413405659001801 2711361518560054244251351)
      ·
        refine ⟨4067042277840081366377027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2711361518560054244251351 4067042277840081366377027)
        ·
          refine ⟨6100563416760122049565541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4067042277840081366377027 6100563416760122049565541)
          ·
            refine ⟨1143855640642522884293539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6100563416760122049565541 1143855640642522884293539)
            ·
              refine ⟨1715783460963784326440309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143855640642522884293539 1715783460963784326440309)
              ·
                refine ⟨160854699465354780603779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1715783460963784326440309 160854699465354780603779)
                ·
                  refine ⟨241282049198032170905669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160854699465354780603779 241282049198032170905669)
                  ·
                    refine ⟨45240384224631032044813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241282049198032170905669 45240384224631032044813)
                    ·
                      rfl

theorem cell23_264316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_264316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264316 prefixEnd_264316 := by exact prefixLift 264316
  have htrace : WordTrace (prefixWord ++ tailWord_264316) baseStart_264316 baseEnd_264316 := by
    simpa [prefixWord, tailWord_264316, baseEnd_264316] using wordTrace_append hprefix tailTrace_264316
  have hstable : (prefixWord ++ tailWord_264316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264316).length < 2 ^ (prefixWord ++ tailWord_264316).sum := by decide
  have hdescent : baseEnd_264316 < baseStart_264316 := by decide
  rcases family_descends (prefixWord ++ tailWord_264316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264379 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 4]
def baseStart_264379 : Nat := 118140960795 + 264379 * 2 ^ 59
def prefixEnd_264379 : Nat := 4983230072969 + 3 ^ 40 * 264379 * 2
def baseEnd_264379 : Nat := 135753501955126349646649

theorem tailTrace_264379 : CollatzResearch.WordTrace tailWord_264379 prefixEnd_264379 135753501955126349646649 := by
  unfold tailWord_264379
  simp only [CollatzResearch.WordTrace]
  refine ⟨9642694309207510183548191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6428462872805006789032127 9642694309207510183548191)
  ·
    refine ⟨14464041463811265275322287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9642694309207510183548191 14464041463811265275322287)
    ·
      refine ⟨21696062195716897912983431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14464041463811265275322287 21696062195716897912983431)
      ·
        refine ⟨32544093293575346869475147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21696062195716897912983431 32544093293575346869475147)
        ·
          refine ⟨48816139940363020304212721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32544093293575346869475147 48816139940363020304212721)
          ·
            refine ⟨36612104955272265228159541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48816139940363020304212721 36612104955272265228159541)
            ·
              refine ⟨3432384839556774865139957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36612104955272265228159541 3432384839556774865139957)
              ·
                refine ⟨321786078708447643606871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3432384839556774865139957 321786078708447643606871)
                ·
                  refine ⟨482679118062671465410307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321786078708447643606871 482679118062671465410307)
                  ·
                    refine ⟨724018677094007198115461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 482679118062671465410307 724018677094007198115461)
                    ·
                      refine ⟨135753501955126349646649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 724018677094007198115461 135753501955126349646649)
                      ·
                        rfl

theorem cell23_264379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 4].length) (baseStart_264379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264379 prefixEnd_264379 := by exact prefixLift 264379
  have htrace : WordTrace (prefixWord ++ tailWord_264379) baseStart_264379 baseEnd_264379 := by
    simpa [prefixWord, tailWord_264379, baseEnd_264379] using wordTrace_append hprefix tailTrace_264379
  have hstable : (prefixWord ++ tailWord_264379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264379).length < 2 ^ (prefixWord ++ tailWord_264379).sum := by decide
  have hdescent : baseEnd_264379 < baseStart_264379 := by decide
  rcases family_descends (prefixWord ++ tailWord_264379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264389 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 4, 4]
def baseStart_264389 : Nat := 118140960795 + 264389 * 2 ^ 59
def prefixEnd_264389 : Nat := 4983230072969 + 3 ^ 40 * 264389 * 2
def baseEnd_264389 : Nat := 45252878920557103507201

theorem tailTrace_264389 : CollatzResearch.WordTrace tailWord_264389 prefixEnd_264389 45252878920557103507201 := by
  unfold tailWord_264389
  simp only [CollatzResearch.WordTrace]
  refine ⟨9643059039171281891412221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6428706026114187927608147 9643059039171281891412221)
  ·
    refine ⟨3616147139689230709279583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9643059039171281891412221 3616147139689230709279583)
    ·
      refine ⟨5424220709533846063919375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3616147139689230709279583 5424220709533846063919375)
      ·
        refine ⟨8136331064300769095879063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5424220709533846063919375 8136331064300769095879063)
        ·
          refine ⟨12204496596451153643818595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8136331064300769095879063 12204496596451153643818595)
          ·
            refine ⟨18306744894676730465727893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12204496596451153643818595 18306744894676730465727893)
            ·
              refine ⟨858128666937971740580995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18306744894676730465727893 858128666937971740580995)
              ·
                refine ⟨1287193000406957610871493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858128666937971740580995 1287193000406957610871493)
                ·
                  refine ⟨241348687576304552038405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1287193000406957610871493 241348687576304552038405)
                  ·
                    refine ⟨45252878920557103507201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241348687576304552038405 45252878920557103507201)
                    ·
                      rfl

theorem cell23_264389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_264389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264389 prefixEnd_264389 := by exact prefixLift 264389
  have htrace : WordTrace (prefixWord ++ tailWord_264389) baseStart_264389 baseEnd_264389 := by
    simpa [prefixWord, tailWord_264389, baseEnd_264389] using wordTrace_append hprefix tailTrace_264389
  have hstable : (prefixWord ++ tailWord_264389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264389).length < 2 ^ (prefixWord ++ tailWord_264389).sum := by decide
  have hdescent : baseEnd_264389 < baseStart_264389 := by decide
  rcases family_descends (prefixWord ++ tailWord_264389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264399 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 3]
def baseStart_264399 : Nat := 118140960795 + 264399 * 2 ^ 59
def prefixEnd_264399 : Nat := 4983230072969 + 3 ^ 40 * 264399 * 2
def baseEnd_264399 : Nat := 135763771568216271396557

theorem tailTrace_264399 : CollatzResearch.WordTrace tailWord_264399 prefixEnd_264399 135763771568216271396557 := by
  unfold tailWord_264399
  simp only [CollatzResearch.WordTrace]
  refine ⟨9643423769135053599276251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6428949179423369066184167 9643423769135053599276251)
  ·
    refine ⟨14465135653702580398914377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9643423769135053599276251 14465135653702580398914377)
    ·
      refine ⟨10848851740276935299185783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14465135653702580398914377 10848851740276935299185783)
      ·
        refine ⟨16273277610415402948778675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10848851740276935299185783 16273277610415402948778675)
        ·
          refine ⟨24409916415623104423168013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16273277610415402948778675 24409916415623104423168013)
          ·
            refine ⟨9153718655858664158688005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24409916415623104423168013 9153718655858664158688005)
            ·
              refine ⟨1716322247973499529754001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9153718655858664158688005 1716322247973499529754001)
              ·
                refine ⟨1287241685980124647315501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1716322247973499529754001 1287241685980124647315501)
                ·
                  refine ⟨482715632242546742743313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1287241685980124647315501 482715632242546742743313)
                  ·
                    refine ⟨362036724181910057057485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 482715632242546742743313 362036724181910057057485)
                    ·
                      refine ⟨135763771568216271396557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 362036724181910057057485 135763771568216271396557)
                      ·
                        rfl

theorem cell23_264399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 3].length) (baseStart_264399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264399 prefixEnd_264399 := by exact prefixLift 264399
  have htrace : WordTrace (prefixWord ++ tailWord_264399) baseStart_264399 baseEnd_264399 := by
    simpa [prefixWord, tailWord_264399, baseEnd_264399] using wordTrace_append hprefix tailTrace_264399
  have hstable : (prefixWord ++ tailWord_264399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264399).length < 2 ^ (prefixWord ++ tailWord_264399).sum := by decide
  have hdescent : baseEnd_264399 < baseStart_264399 := by decide
  rcases family_descends (prefixWord ++ tailWord_264399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264413 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_264413 : Nat := 118140960795 + 264413 * 2 ^ 59
def prefixEnd_264413 : Nat := 4983230072969 + 3 ^ 40 * 264413 * 2
def baseEnd_264413 : Nat := 135770960297379216621493

theorem tailTrace_264413 : CollatzResearch.WordTrace tailWord_264413 prefixEnd_264413 135770960297379216621493 := by
  unfold tailWord_264413
  simp only [CollatzResearch.WordTrace]
  refine ⟨9643934391084333990285893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6429289594056222660190595 9643934391084333990285893)
  ·
    refine ⟨1808237698328312623178605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9643934391084333990285893 1808237698328312623178605)
    ·
      refine ⟨678089136873117233691977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1808237698328312623178605 678089136873117233691977)
      ·
        refine ⟨508566852654837925268983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678089136873117233691977 508566852654837925268983)
        ·
          refine ⟨762850278982256887903475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508566852654837925268983 762850278982256887903475)
          ·
            refine ⟨1144275418473385331855213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762850278982256887903475 1144275418473385331855213)
            ·
              refine ⟨429103281927519499445705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1144275418473385331855213 429103281927519499445705)
              ·
                refine ⟨321827461445639624584279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429103281927519499445705 321827461445639624584279)
                ·
                  refine ⟨482741192168459436876419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 321827461445639624584279 482741192168459436876419)
                  ·
                    refine ⟨724111788252689155314629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 482741192168459436876419 724111788252689155314629)
                    ·
                      refine ⟨135770960297379216621493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 724111788252689155314629 135770960297379216621493)
                      ·
                        rfl

theorem cell23_264413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_264413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264413 prefixEnd_264413 := by exact prefixLift 264413
  have htrace : WordTrace (prefixWord ++ tailWord_264413) baseStart_264413 baseEnd_264413 := by
    simpa [prefixWord, tailWord_264413, baseEnd_264413] using wordTrace_append hprefix tailTrace_264413
  have hstable : (prefixWord ++ tailWord_264413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264413).length < 2 ^ (prefixWord ++ tailWord_264413).sum := by decide
  have hdescent : baseEnd_264413 < baseStart_264413 := by decide
  rcases family_descends (prefixWord ++ tailWord_264413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264430 : List Nat := [4, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_264430 : Nat := 118140960795 + 264430 * 2 ^ 59
def prefixEnd_264430 : Nat := 4983230072969 + 3 ^ 40 * 264430 * 2
def baseEnd_264430 : Nat := 135779689468505650108915

theorem tailTrace_264430 : CollatzResearch.WordTrace tailWord_264430 prefixEnd_264430 135779689468505650108915 := by
  unfold tailWord_264430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205569304002843236706843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6429702954681830595769829 1205569304002843236706843)
  ·
    refine ⟨1808353956004264855060265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1205569304002843236706843 1808353956004264855060265)
    ·
      refine ⟨1356265467003198641295199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1808353956004264855060265 1356265467003198641295199)
      ·
        refine ⟨2034398200504797961942799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356265467003198641295199 2034398200504797961942799)
        ·
          refine ⟨3051597300757196942914199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034398200504797961942799 3051597300757196942914199)
          ·
            refine ⟨4577395951135795414371299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051597300757196942914199 4577395951135795414371299)
            ·
              refine ⟨6866093926703693121556949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4577395951135795414371299 6866093926703693121556949)
              ·
                refine ⟨160924076407117807536491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6866093926703693121556949 160924076407117807536491)
                ·
                  refine ⟨241386114610676711304737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160924076407117807536491 241386114610676711304737)
                  ·
                    refine ⟨181039585958007533478553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241386114610676711304737 181039585958007533478553)
                    ·
                      refine ⟨135779689468505650108915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 181039585958007533478553 135779689468505650108915)
                      ·
                        rfl

theorem cell23_264430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_264430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264430 prefixEnd_264430 := by exact prefixLift 264430
  have htrace : WordTrace (prefixWord ++ tailWord_264430) baseStart_264430 baseEnd_264430 := by
    simpa [prefixWord, tailWord_264430, baseEnd_264430] using wordTrace_append hprefix tailTrace_264430
  have hstable : (prefixWord ++ tailWord_264430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264430).length < 2 ^ (prefixWord ++ tailWord_264430).sum := by decide
  have hdescent : baseEnd_264430 < baseStart_264430 := by decide
  rcases family_descends (prefixWord ++ tailWord_264430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264432 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 4, 7]
def baseStart_264432 : Nat := 118140960795 + 264432 * 2 ^ 59
def prefixEnd_264432 : Nat := 4983230072969 + 3 ^ 40 * 264432 * 2
def baseEnd_264432 : Nat := 45260238809938214094635

theorem tailTrace_264432 : CollatzResearch.WordTrace tailWord_264432 prefixEnd_264432 45260238809938214094635 := by
  unfold tailWord_264432
  simp only [CollatzResearch.WordTrace]
  refine ⟨4822313689007750117613775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6429751585343666823485033 4822313689007750117613775)
  ·
    refine ⟨7233470533511625176420663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4822313689007750117613775 7233470533511625176420663)
    ·
      refine ⟨10850205800267437764630995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7233470533511625176420663 10850205800267437764630995)
      ·
        refine ⟨16275308700401156646946493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10850205800267437764630995 16275308700401156646946493)
        ·
          refine ⟨6103240762650433742604935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16275308700401156646946493 6103240762650433742604935)
          ·
            refine ⟨9154861143975650613907403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6103240762650433742604935 9154861143975650613907403)
            ·
              refine ⟨13732291715963475920861105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9154861143975650613907403 13732291715963475920861105)
              ·
                refine ⟨10299218786972606940645829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13732291715963475920861105 10299218786972606940645829)
                ·
                  refine ⟨1931103522557363801371093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10299218786972606940645829 1931103522557363801371093)
                  ·
                    refine ⟨45260238809938214094635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1931103522557363801371093 45260238809938214094635)
                    ·
                      rfl

theorem cell23_264432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_264432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264432 prefixEnd_264432 := by exact prefixLift 264432
  have htrace : WordTrace (prefixWord ++ tailWord_264432) baseStart_264432 baseEnd_264432 := by
    simpa [prefixWord, tailWord_264432, baseEnd_264432] using wordTrace_append hprefix tailTrace_264432
  have hstable : (prefixWord ++ tailWord_264432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264432).length < 2 ^ (prefixWord ++ tailWord_264432).sum := by decide
  have hdescent : baseEnd_264432 < baseStart_264432 := by decide
  rcases family_descends (prefixWord ++ tailWord_264432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264446 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_264446 : Nat := 118140960795 + 264446 * 2 ^ 59
def prefixEnd_264446 : Nat := 4983230072969 + 3 ^ 40 * 264446 * 2
def baseEnd_264446 : Nat := 135787905158977587508841

theorem tailTrace_264446 : CollatzResearch.WordTrace tailWord_264446 prefixEnd_264446 135787905158977587508841 := by
  unfold tailWord_264446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205642249995597578279649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6430091999976520417491461 1205642249995597578279649)
  ·
    refine ⟨904231687496698183709737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1205642249995597578279649 904231687496698183709737)
    ·
      refine ⟨678173765622523637782303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 904231687496698183709737 678173765622523637782303)
      ·
        refine ⟨1017260648433785456673455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678173765622523637782303 1017260648433785456673455)
        ·
          refine ⟨1525890972650678185010183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017260648433785456673455 1525890972650678185010183)
          ·
            refine ⟨2288836458976017277515275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1525890972650678185010183 2288836458976017277515275)
            ·
              refine ⟨3433254688464025916272913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2288836458976017277515275 3433254688464025916272913)
              ·
                refine ⟨2574941016348019437204685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3433254688464025916272913 2574941016348019437204685)
                ·
                  refine ⟨965602881130507288951757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2574941016348019437204685 965602881130507288951757)
                  ·
                    refine ⟨362101080423940233356909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965602881130507288951757 362101080423940233356909)
                    ·
                      refine ⟨135787905158977587508841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 362101080423940233356909 135787905158977587508841)
                      ·
                        rfl

theorem cell23_264446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_264446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264446 prefixEnd_264446 := by exact prefixLift 264446
  have htrace : WordTrace (prefixWord ++ tailWord_264446) baseStart_264446 baseEnd_264446 := by
    simpa [prefixWord, tailWord_264446, baseEnd_264446] using wordTrace_append hprefix tailTrace_264446
  have hstable : (prefixWord ++ tailWord_264446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264446).length < 2 ^ (prefixWord ++ tailWord_264446).sum := by decide
  have hdescent : baseEnd_264446 < baseStart_264446 := by decide
  rcases family_descends (prefixWord ++ tailWord_264446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264497 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 2, 1, 3]
def baseStart_264497 : Nat := 118140960795 + 264497 * 2 ^ 59
def prefixEnd_264497 : Nat := 4983230072969 + 3 ^ 40 * 264497 * 2
def baseEnd_264497 : Nat := 135814092672356887971107

theorem tailTrace_264497 : CollatzResearch.WordTrace tailWord_264497 prefixEnd_264497 135814092672356887971107 := by
  unfold tailWord_264497
  simp only [CollatzResearch.WordTrace]
  refine ⟨9646998122780016336343745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6431332081853344224229163 9646998122780016336343745)
  ·
    refine ⟨7235248592085012252257809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9646998122780016336343745 7235248592085012252257809)
    ·
      refine ⟨5426436444063759189193357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7235248592085012252257809 5426436444063759189193357)
      ·
        refine ⟨2034913666523909695947509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5426436444063759189193357 2034913666523909695947509)
        ·
          refine ⟨190773156236616533995079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2034913666523909695947509 190773156236616533995079)
          ·
            refine ⟨286159734354924800992619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190773156236616533995079 286159734354924800992619)
            ·
              refine ⟨429239601532387201488929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286159734354924800992619 429239601532387201488929)
              ·
                refine ⟨321929701149290401116697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429239601532387201488929 321929701149290401116697)
                ·
                  refine ⟨241447275861967800837523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 321929701149290401116697 241447275861967800837523)
                  ·
                    refine ⟨362170913792951701256285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241447275861967800837523 362170913792951701256285)
                    ·
                      refine ⟨135814092672356887971107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 362170913792951701256285 135814092672356887971107)
                      ·
                        rfl

theorem cell23_264497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_264497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264497 prefixEnd_264497 := by exact prefixLift 264497
  have htrace : WordTrace (prefixWord ++ tailWord_264497) baseStart_264497 baseEnd_264497 := by
    simpa [prefixWord, tailWord_264497, baseEnd_264497] using wordTrace_append hprefix tailTrace_264497
  have hstable : (prefixWord ++ tailWord_264497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264497).length < 2 ^ (prefixWord ++ tailWord_264497).sum := by decide
  have hdescent : baseEnd_264497 < baseStart_264497 := by decide
  rcases family_descends (prefixWord ++ tailWord_264497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264499 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 4]
def baseStart_264499 : Nat := 118140960795 + 264499 * 2 ^ 59
def prefixEnd_264499 : Nat := 4983230072969 + 3 ^ 40 * 264499 * 2
def baseEnd_264499 : Nat := 135815119633665880146097

theorem tailTrace_264499 : CollatzResearch.WordTrace tailWord_264499 prefixEnd_264499 135815119633665880146097 := by
  unfold tailWord_264499
  simp only [CollatzResearch.WordTrace]
  refine ⟨9647071068772770677916551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6431380712515180451944367 9647071068772770677916551)
  ·
    refine ⟨14470606603159156016874827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9647071068772770677916551 14470606603159156016874827)
    ·
      refine ⟨21705909904738734025312241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14470606603159156016874827 21705909904738734025312241)
      ·
        refine ⟨16279432428554050518984181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21705909904738734025312241 16279432428554050518984181)
        ·
          refine ⟨1526196790176942236154767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16279432428554050518984181 1526196790176942236154767)
          ·
            refine ⟨2289295185265413354232151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526196790176942236154767 2289295185265413354232151)
            ·
              refine ⟨3433942777898120031348227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289295185265413354232151 3433942777898120031348227)
              ·
                refine ⟨5150914166847180047022341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3433942777898120031348227 5150914166847180047022341)
                ·
                  refine ⟨965796406283846258816689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5150914166847180047022341 965796406283846258816689)
                  ·
                    refine ⟨724347304712884694112517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 965796406283846258816689 724347304712884694112517)
                    ·
                      refine ⟨135815119633665880146097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 724347304712884694112517 135815119633665880146097)
                      ·
                        rfl

theorem cell23_264499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_264499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264499 prefixEnd_264499 := by exact prefixLift 264499
  have htrace : WordTrace (prefixWord ++ tailWord_264499) baseStart_264499 baseEnd_264499 := by
    simpa [prefixWord, tailWord_264499, baseEnd_264499] using wordTrace_append hprefix tailTrace_264499
  have hstable : (prefixWord ++ tailWord_264499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264499).length < 2 ^ (prefixWord ++ tailWord_264499).sum := by decide
  have hdescent : baseEnd_264499 < baseStart_264499 := by decide
  rcases family_descends (prefixWord ++ tailWord_264499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264559 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 4]
def baseStart_264559 : Nat := 118140960795 + 264559 * 2 ^ 59
def prefixEnd_264559 : Nat := 4983230072969 + 3 ^ 40 * 264559 * 2
def baseEnd_264559 : Nat := 135845928472935645395821

theorem tailTrace_264559 : CollatzResearch.WordTrace tailWord_264559 prefixEnd_264559 135845928472935645395821 := by
  unfold tailWord_264559
  simp only [CollatzResearch.WordTrace]
  refine ⟨9649259448555400925100731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6432839632370267283400487 9649259448555400925100731)
  ·
    refine ⟨14473889172833101387651097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9649259448555400925100731 14473889172833101387651097)
    ·
      refine ⟨10855416879624826040738323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14473889172833101387651097 10855416879624826040738323)
      ·
        refine ⟨16283125319437239061107485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10855416879624826040738323 16283125319437239061107485)
        ·
          refine ⟨6106171994788964647915307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16283125319437239061107485 6106171994788964647915307)
          ·
            refine ⟨9159257992183446971872961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6106171994788964647915307 9159257992183446971872961)
            ·
              refine ⟨6869443494137585228904721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9159257992183446971872961 6869443494137585228904721)
              ·
                refine ⟨5152082620603188921678541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6869443494137585228904721 5152082620603188921678541)
                ·
                  refine ⟨1932030982726195845629453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5152082620603188921678541 1932030982726195845629453)
                  ·
                    refine ⟨724511618522323442111045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1932030982726195845629453 724511618522323442111045)
                    ·
                      refine ⟨135845928472935645395821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 724511618522323442111045 135845928472935645395821)
                      ·
                        rfl

theorem cell23_264559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_264559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264559 prefixEnd_264559 := by exact prefixLift 264559
  have htrace : WordTrace (prefixWord ++ tailWord_264559) baseStart_264559 baseEnd_264559 := by
    simpa [prefixWord, tailWord_264559, baseEnd_264559] using wordTrace_append hprefix tailTrace_264559
  have hstable : (prefixWord ++ tailWord_264559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264559).length < 2 ^ (prefixWord ++ tailWord_264559).sum := by decide
  have hdescent : baseEnd_264559 < baseStart_264559 := by decide
  rcases family_descends (prefixWord ++ tailWord_264559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264599 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 10]
def baseStart_264599 : Nat := 118140960795 + 264599 * 2 ^ 59
def prefixEnd_264599 : Nat := 4983230072969 + 3 ^ 40 * 264599 * 2
def baseEnd_264599 : Nat := 15096274188790609877293

theorem tailTrace_264599 : CollatzResearch.WordTrace tailWord_264599 prefixEnd_264599 15096274188790609877293 := by
  unfold tailWord_264599
  simp only [CollatzResearch.WordTrace]
  refine ⟨9650718368410487756556851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6433812245606991837704567 9650718368410487756556851)
  ·
    refine ⟨14476077552615731634835277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9650718368410487756556851 14476077552615731634835277)
    ·
      refine ⟨5428529082230899363063229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14476077552615731634835277 5428529082230899363063229)
      ·
        refine ⟨2035698405836587261148711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5428529082230899363063229 2035698405836587261148711)
        ·
          refine ⟨3053547608754880891723067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2035698405836587261148711 3053547608754880891723067)
          ·
            refine ⟨4580321413132321337584601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3053547608754880891723067 4580321413132321337584601)
            ·
              refine ⟨3435241059849241003188451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4580321413132321337584601 3435241059849241003188451)
              ·
                refine ⟨5152861589773861504782677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3435241059849241003188451 5152861589773861504782677)
                ·
                  refine ⟨15096274188790609877293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 5152861589773861504782677 15096274188790609877293)
                  ·
                    rfl

theorem cell23_264599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 10].length) (baseStart_264599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264599 prefixEnd_264599 := by exact prefixLift 264599
  have htrace : WordTrace (prefixWord ++ tailWord_264599) baseStart_264599 baseEnd_264599 := by
    simpa [prefixWord, tailWord_264599, baseEnd_264599] using wordTrace_append hprefix tailTrace_264599
  have hstable : (prefixWord ++ tailWord_264599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264599).length < 2 ^ (prefixWord ++ tailWord_264599).sum := by decide
  have hdescent : baseEnd_264599 < baseStart_264599 := by decide
  rcases family_descends (prefixWord ++ tailWord_264599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264659 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 4, 10]
def baseStart_264659 : Nat := 118140960795 + 264659 * 2 ^ 59
def prefixEnd_264659 : Nat := 4983230072969 + 3 ^ 40 * 264659 * 2
def baseEnd_264659 : Nat := 45299092179461751381787

theorem tailTrace_264659 : CollatzResearch.WordTrace tailWord_264659 prefixEnd_264659 45299092179461751381787 := by
  unfold tailWord_264659
  simp only [CollatzResearch.WordTrace]
  refine ⟨9652906748193118003741031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6435271165462078669160687 9652906748193118003741031)
  ·
    refine ⟨14479360122289677005611547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9652906748193118003741031 14479360122289677005611547)
    ·
      refine ⟨21719040183434515508417321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14479360122289677005611547 21719040183434515508417321)
      ·
        refine ⟨16289280137575886631312991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21719040183434515508417321 16289280137575886631312991)
        ·
          refine ⟨24433920206363829946969487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16289280137575886631312991 24433920206363829946969487)
          ·
            refine ⟨36650880309545744920454231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24433920206363829946969487 36650880309545744920454231)
            ·
              refine ⟨54976320464318617380681347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36650880309545744920454231 54976320464318617380681347)
              ·
                refine ⟨82464480696477926071022021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54976320464318617380681347 82464480696477926071022021)
                ·
                  refine ⟨15462090130589611138316629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82464480696477926071022021 15462090130589611138316629)
                  ·
                    refine ⟨45299092179461751381787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 15462090130589611138316629 45299092179461751381787)
                    ·
                      rfl

theorem cell23_264659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 10].length) (baseStart_264659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264659 prefixEnd_264659 := by exact prefixLift 264659
  have htrace : WordTrace (prefixWord ++ tailWord_264659) baseStart_264659 baseEnd_264659 := by
    simpa [prefixWord, tailWord_264659, baseEnd_264659] using wordTrace_append hprefix tailTrace_264659
  have hstable : (prefixWord ++ tailWord_264659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264659).length < 2 ^ (prefixWord ++ tailWord_264659).sum := by decide
  have hdescent : baseEnd_264659 < baseStart_264659 := by decide
  rcases family_descends (prefixWord ++ tailWord_264659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264677 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 3, 1, 3]
def baseStart_264677 : Nat := 118140960795 + 264677 * 2 ^ 59
def prefixEnd_264677 : Nat := 4983230072969 + 3 ^ 40 * 264677 * 2
def baseEnd_264677 : Nat := 135906519190166183720279

theorem tailTrace_264677 : CollatzResearch.WordTrace tailWord_264677 prefixEnd_264677 135906519190166183720279 := by
  unfold tailWord_264677
  simp only [CollatzResearch.WordTrace]
  refine ⟨9653563262127907077896285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6435708841418604718597523 9653563262127907077896285)
  ·
    refine ⟨3620086223297965154211107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9653563262127907077896285 3620086223297965154211107)
    ·
      refine ⟨5430129334946947731316661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3620086223297965154211107 5430129334946947731316661)
      ·
        refine ⟨509074625151276349810937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5430129334946947731316661 509074625151276349810937)
        ·
          refine ⟨381805968863457262358203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509074625151276349810937 381805968863457262358203)
          ·
            refine ⟨572708953295185893537305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381805968863457262358203 572708953295185893537305)
            ·
              refine ⟨429531714971389420152979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572708953295185893537305 429531714971389420152979)
              ·
                refine ⟨644297572457084130229469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429531714971389420152979 644297572457084130229469)
                ·
                  refine ⟨241611589671406548836051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 644297572457084130229469 241611589671406548836051)
                  ·
                    refine ⟨362417384507109823254077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241611589671406548836051 362417384507109823254077)
                    ·
                      refine ⟨135906519190166183720279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 362417384507109823254077 135906519190166183720279)
                      ·
                        rfl

theorem cell23_264677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_264677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264677 prefixEnd_264677 := by exact prefixLift 264677
  have htrace : WordTrace (prefixWord ++ tailWord_264677) baseStart_264677 baseEnd_264677 := by
    simpa [prefixWord, tailWord_264677, baseEnd_264677] using wordTrace_append hprefix tailTrace_264677
  have hstable : (prefixWord ++ tailWord_264677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264677).length < 2 ^ (prefixWord ++ tailWord_264677).sum := by decide
  have hdescent : baseEnd_264677 < baseStart_264677 := by decide
  rcases family_descends (prefixWord ++ tailWord_264677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264696 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_264696 : Nat := 118140960795 + 264696 * 2 ^ 59
def prefixEnd_264696 : Nat := 4983230072969 + 3 ^ 40 * 264696 * 2
def baseEnd_264696 : Nat := 135916275322601609382691

theorem tailTrace_264696 : CollatzResearch.WordTrace tailWord_264696 prefixEnd_264696 135916275322601609382691 := by
  unfold tailWord_264696
  simp only [CollatzResearch.WordTrace]
  refine ⟨4827128124529536661418971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6436170832706048881891961 4827128124529536661418971)
  ·
    refine ⟨7240692186794304992128457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4827128124529536661418971 7240692186794304992128457)
    ·
      refine ⟨5430519140095728744096343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7240692186794304992128457 5430519140095728744096343)
      ·
        refine ⟨8145778710143593116144515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5430519140095728744096343 8145778710143593116144515)
        ·
          refine ⟨12218668065215389674216773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8145778710143593116144515 12218668065215389674216773)
          ·
            refine ⟨2291000262227885563915645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12218668065215389674216773 2291000262227885563915645)
            ·
              refine ⟨859125098335457086468367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2291000262227885563915645 859125098335457086468367)
              ·
                refine ⟨1288687647503185629702551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859125098335457086468367 1288687647503185629702551)
                ·
                  refine ⟨1933031471254778444553827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288687647503185629702551 1933031471254778444553827)
                  ·
                    refine ⟨2899547206882167666830741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1933031471254778444553827 2899547206882167666830741)
                    ·
                      refine ⟨135916275322601609382691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2899547206882167666830741 135916275322601609382691)
                      ·
                        rfl

theorem cell23_264696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_264696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264696 prefixEnd_264696 := by exact prefixLift 264696
  have htrace : WordTrace (prefixWord ++ tailWord_264696) baseStart_264696 baseEnd_264696 := by
    simpa [prefixWord, tailWord_264696, baseEnd_264696] using wordTrace_append hprefix tailTrace_264696
  have hstable : (prefixWord ++ tailWord_264696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264696).length < 2 ^ (prefixWord ++ tailWord_264696).sum := by decide
  have hdescent : baseEnd_264696 < baseStart_264696 := by decide
  rcases family_descends (prefixWord ++ tailWord_264696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264711 : List Nat := [1, 1, 4, 3, 4, 1, 1, 3, 1, 1, 3]
def baseStart_264711 : Nat := 118140960795 + 264711 * 2 ^ 59
def prefixEnd_264711 : Nat := 4983230072969 + 3 ^ 40 * 264711 * 2
def baseEnd_264711 : Nat := 135923977532419050695123

theorem tailTrace_264711 : CollatzResearch.WordTrace tailWord_264711 prefixEnd_264711 135923977532419050695123 := by
  unfold tailWord_264711
  simp only [CollatzResearch.WordTrace]
  refine ⟨9654803344004730884633987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6436535562669820589755991 9654803344004730884633987)
  ·
    refine ⟨14482205016007096326950981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9654803344004730884633987 14482205016007096326950981)
    ·
      refine ⟨2715413440501330561303309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14482205016007096326950981 2715413440501330561303309)
      ·
        refine ⟨1018280040187998960488741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2715413440501330561303309 1018280040187998960488741)
        ·
          refine ⟨190927507535249805091639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1018280040187998960488741 190927507535249805091639)
          ·
            refine ⟨286391261302874707637459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190927507535249805091639 286391261302874707637459)
            ·
              refine ⟨429586891954312061456189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286391261302874707637459 429586891954312061456189)
              ·
                refine ⟨161095084482867023046071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429586891954312061456189 161095084482867023046071)
                ·
                  refine ⟨241642626724300534569107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161095084482867023046071 241642626724300534569107)
                  ·
                    refine ⟨362463940086450801853661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241642626724300534569107 362463940086450801853661)
                    ·
                      refine ⟨135923977532419050695123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 362463940086450801853661 135923977532419050695123)
                      ·
                        rfl

theorem cell23_264711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_264711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264711 prefixEnd_264711 := by exact prefixLift 264711
  have htrace : WordTrace (prefixWord ++ tailWord_264711) baseStart_264711 baseEnd_264711 := by
    simpa [prefixWord, tailWord_264711, baseEnd_264711] using wordTrace_append hprefix tailTrace_264711
  have hstable : (prefixWord ++ tailWord_264711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264711).length < 2 ^ (prefixWord ++ tailWord_264711).sum := by decide
  have hdescent : baseEnd_264711 < baseStart_264711 := by decide
  rcases family_descends (prefixWord ++ tailWord_264711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264740 : List Nat := [2, 3, 1, 5, 1, 1, 2, 8]
def baseStart_264740 : Nat := 118140960795 + 264740 * 2 ^ 59
def prefixEnd_264740 : Nat := 4983230072969 + 3 ^ 40 * 264740 * 2
def baseEnd_264740 : Nat := 5034772906348127304907

theorem tailTrace_264740 : CollatzResearch.WordTrace tailWord_264740 prefixEnd_264740 5034772906348127304907 := by
  unfold tailWord_264740
  simp only [CollatzResearch.WordTrace]
  refine ⟨4827930530449834418719837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6437240707266445891626449 4827930530449834418719837)
  ·
    refine ⟨1810473948918687907019939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4827930530449834418719837 1810473948918687907019939)
    ·
      refine ⟨2715710923378031860529909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1810473948918687907019939 2715710923378031860529909)
      ·
        refine ⟨254597899066690486924679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2715710923378031860529909 254597899066690486924679)
        ·
          refine ⟨381896848600035730387019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254597899066690486924679 381896848600035730387019)
          ·
            refine ⟨572845272900053595580529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381896848600035730387019 572845272900053595580529)
            ·
              refine ⟨429633954675040196685397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572845272900053595580529 429633954675040196685397)
              ·
                refine ⟨5034772906348127304907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 429633954675040196685397 5034772906348127304907)
                ·
                  rfl

theorem cell23_264740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 8].length) (baseStart_264740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264740 prefixEnd_264740 := by exact prefixLift 264740
  have htrace : WordTrace (prefixWord ++ tailWord_264740) baseStart_264740 baseEnd_264740 := by
    simpa [prefixWord, tailWord_264740, baseEnd_264740] using wordTrace_append hprefix tailTrace_264740
  have hstable : (prefixWord ++ tailWord_264740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264740).length < 2 ^ (prefixWord ++ tailWord_264740).sum := by decide
  have hdescent : baseEnd_264740 < baseStart_264740 := by decide
  rcases family_descends (prefixWord ++ tailWord_264740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264744 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 2, 4]
def baseStart_264744 : Nat := 118140960795 + 264744 * 2 ^ 59
def prefixEnd_264744 : Nat := 4983230072969 + 3 ^ 40 * 264744 * 2
def baseEnd_264744 : Nat := 45313640798005807194157

theorem tailTrace_264744 : CollatzResearch.WordTrace tailWord_264744 prefixEnd_264744 45313640798005807194157 := by
  unfold tailWord_264744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4828003476442588760292643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6437337968590118347056857 4828003476442588760292643)
  ·
    refine ⟨7242005214663883140438965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4828003476442588760292643 7242005214663883140438965)
    ·
      refine ⟨678937988874739044416153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7242005214663883140438965 678937988874739044416153)
      ·
        refine ⟨509203491656054283312115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678937988874739044416153 509203491656054283312115)
        ·
          refine ⟨763805237484081424968173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509203491656054283312115 763805237484081424968173)
          ·
            refine ⟨286426964056530534363065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 763805237484081424968173 286426964056530534363065)
            ·
              refine ⟨214820223042397900772299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286426964056530534363065 214820223042397900772299)
              ·
                refine ⟨322230334563596851158449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214820223042397900772299 322230334563596851158449)
                ·
                  refine ⟨241672750922697638368837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322230334563596851158449 241672750922697638368837)
                  ·
                    refine ⟨45313640798005807194157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241672750922697638368837 45313640798005807194157)
                    ·
                      rfl

theorem cell23_264744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_264744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264744 prefixEnd_264744 := by exact prefixLift 264744
  have htrace : WordTrace (prefixWord ++ tailWord_264744) baseStart_264744 baseEnd_264744 := by
    simpa [prefixWord, tailWord_264744, baseEnd_264744] using wordTrace_append hprefix tailTrace_264744
  have hstable : (prefixWord ++ tailWord_264744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264744).length < 2 ^ (prefixWord ++ tailWord_264744).sum := by decide
  have hdescent : baseEnd_264744 < baseStart_264744 := by decide
  rcases family_descends (prefixWord ++ tailWord_264744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264760 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 3, 3, 2]
def baseStart_264760 : Nat := 118140960795 + 264760 * 2 ^ 59
def prefixEnd_264760 : Nat := 4983230072969 + 3 ^ 40 * 264760 * 2
def baseEnd_264760 : Nat := 135949138084489358982397

theorem tailTrace_264760 : CollatzResearch.WordTrace tailWord_264760 prefixEnd_264760 135949138084489358982397 := by
  unfold tailWord_264760
  simp only [CollatzResearch.WordTrace]
  refine ⟨4828295260413606126583867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6437727013884808168778489 4828295260413606126583867)
  ·
    refine ⟨7242442890620409189875801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4828295260413606126583867 7242442890620409189875801)
    ·
      refine ⟨5431832167965306892406851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7242442890620409189875801 5431832167965306892406851)
      ·
        refine ⟨8147748251947960338610277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5431832167965306892406851 8147748251947960338610277)
        ·
          refine ⟨1527702797240242563489427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8147748251947960338610277 1527702797240242563489427)
          ·
            refine ⟨2291554195860363845234141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527702797240242563489427 2291554195860363845234141)
            ·
              refine ⟨859332823447636441962803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2291554195860363845234141 859332823447636441962803)
              ·
                refine ⟨1288999235171454662944205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859332823447636441962803 1288999235171454662944205)
                ·
                  refine ⟨483374713189295498604077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1288999235171454662944205 483374713189295498604077)
                  ·
                    refine ⟨181265517445985811976529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483374713189295498604077 181265517445985811976529)
                    ·
                      refine ⟨135949138084489358982397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 181265517445985811976529 135949138084489358982397)
                      ·
                        rfl

theorem cell23_264760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 3, 2].length) (baseStart_264760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264760 prefixEnd_264760 := by exact prefixLift 264760
  have htrace : WordTrace (prefixWord ++ tailWord_264760) baseStart_264760 baseEnd_264760 := by
    simpa [prefixWord, tailWord_264760, baseEnd_264760] using wordTrace_append hprefix tailTrace_264760
  have hstable : (prefixWord ++ tailWord_264760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264760).length < 2 ^ (prefixWord ++ tailWord_264760).sum := by decide
  have hdescent : baseEnd_264760 < baseStart_264760 := by decide
  rcases family_descends (prefixWord ++ tailWord_264760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264803 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 4]
def baseStart_264803 : Nat := 118140960795 + 264803 * 2 ^ 59
def prefixEnd_264803 : Nat := 4983230072969 + 3 ^ 40 * 264803 * 2
def baseEnd_264803 : Nat := 135971217752632690744699

theorem tailTrace_264803 : CollatzResearch.WordTrace tailWord_264803 prefixEnd_264803 135971217752632690744699 := by
  unfold tailWord_264803
  simp only [CollatzResearch.WordTrace]
  refine ⟨9658158859671430596983063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6438772573114287064655375 9658158859671430596983063)
  ·
    refine ⟨14487238289507145895474595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9658158859671430596983063 14487238289507145895474595)
    ·
      refine ⟨21730857434260718843211893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14487238289507145895474595 21730857434260718843211893)
      ·
        refine ⟨2037267884461942391551115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21730857434260718843211893 2037267884461942391551115)
        ·
          refine ⟨3055901826692913587326673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2037267884461942391551115 3055901826692913587326673)
          ·
            refine ⟨2291926370019685190495005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3055901826692913587326673 2291926370019685190495005)
            ·
              refine ⟨859472388757381946435627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2291926370019685190495005 859472388757381946435627)
              ·
                refine ⟨1289208583136072919653441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859472388757381946435627 1289208583136072919653441)
                ·
                  refine ⟨966906437352054689740081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1289208583136072919653441 966906437352054689740081)
                  ·
                    refine ⟨725179828014041017305061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 966906437352054689740081 725179828014041017305061)
                    ·
                      refine ⟨135971217752632690744699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 725179828014041017305061 135971217752632690744699)
                      ·
                        rfl

theorem cell23_264803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_264803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264803 prefixEnd_264803 := by exact prefixLift 264803
  have htrace : WordTrace (prefixWord ++ tailWord_264803) baseStart_264803 baseEnd_264803 := by
    simpa [prefixWord, tailWord_264803, baseEnd_264803] using wordTrace_append hprefix tailTrace_264803
  have hstable : (prefixWord ++ tailWord_264803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264803).length < 2 ^ (prefixWord ++ tailWord_264803).sum := by decide
  have hdescent : baseEnd_264803 < baseStart_264803 := by decide
  rcases family_descends (prefixWord ++ tailWord_264803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264813 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 9]
def baseStart_264813 : Nat := 118140960795 + 264813 * 2 ^ 59
def prefixEnd_264813 : Nat := 4983230072969 + 3 ^ 40 * 264813 * 2
def baseEnd_264813 : Nat := 15108483617686405735517

theorem tailTrace_264813 : CollatzResearch.WordTrace tailWord_264813 prefixEnd_264813 15108483617686405735517 := by
  unfold tailWord_264813
  simp only [CollatzResearch.WordTrace]
  refine ⟨9658523589635202304847093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6439015726423468203231395 9658523589635202304847093)
  ·
    refine ⟨905486586528300216079415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9658523589635202304847093 905486586528300216079415)
    ·
      refine ⟨1358229879792450324119123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 905486586528300216079415 1358229879792450324119123)
      ·
        refine ⟨2037344819688675486178685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1358229879792450324119123 2037344819688675486178685)
        ·
          refine ⟨764004307383253307317007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2037344819688675486178685 764004307383253307317007)
          ·
            refine ⟨1146006461074879960975511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764004307383253307317007 1146006461074879960975511)
            ·
              refine ⟨1719009691612319941463267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146006461074879960975511 1719009691612319941463267)
              ·
                refine ⟨2578514537418479912194901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719009691612319941463267 2578514537418479912194901)
                ·
                  refine ⟨15108483617686405735517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2578514537418479912194901 15108483617686405735517)
                  ·
                    rfl

theorem cell23_264813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_264813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264813 prefixEnd_264813 := by exact prefixLift 264813
  have htrace : WordTrace (prefixWord ++ tailWord_264813) baseStart_264813 baseEnd_264813 := by
    simpa [prefixWord, tailWord_264813, baseEnd_264813] using wordTrace_append hprefix tailTrace_264813
  have hstable : (prefixWord ++ tailWord_264813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264813).length < 2 ^ (prefixWord ++ tailWord_264813).sum := by decide
  have hdescent : baseEnd_264813 < baseStart_264813 := by decide
  rcases family_descends (prefixWord ++ tailWord_264813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264858 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2]
def baseStart_264858 : Nat := 118140960795 + 264858 * 2 ^ 59
def prefixEnd_264858 : Nat := 4983230072969 + 3 ^ 40 * 264858 * 2
def baseEnd_264858 : Nat := 135999459188629975556947

theorem tailTrace_264858 : CollatzResearch.WordTrace tailWord_264858 prefixEnd_264858 135999459188629975556947 := by
  unfold tailWord_264858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415041218618043747558807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6440109916314783326823485 2415041218618043747558807)
  ·
    refine ⟨3622561827927065621338211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2415041218618043747558807 3622561827927065621338211)
    ·
      refine ⟨5433842741890598432007317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3622561827927065621338211 5433842741890598432007317)
      ·
        refine ⟨254711378526121801500343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5433842741890598432007317 254711378526121801500343)
        ·
          refine ⟨382067067789182702250515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254711378526121801500343 382067067789182702250515)
          ·
            refine ⟨573100601683774053375773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382067067789182702250515 573100601683774053375773)
            ·
              refine ⟨214912725631415270015915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573100601683774053375773 214912725631415270015915)
              ·
                refine ⟨322369088447122905023873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214912725631415270015915 322369088447122905023873)
                ·
                  refine ⟨241776816335342178767905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322369088447122905023873 241776816335342178767905)
                  ·
                    refine ⟨181332612251506634075929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241776816335342178767905 181332612251506634075929)
                    ·
                      refine ⟨135999459188629975556947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 181332612251506634075929 135999459188629975556947)
                      ·
                        rfl

theorem cell23_264858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_264858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264858 prefixEnd_264858 := by exact prefixLift 264858
  have htrace : WordTrace (prefixWord ++ tailWord_264858) baseStart_264858 baseEnd_264858 := by
    simpa [prefixWord, tailWord_264858, baseEnd_264858] using wordTrace_append hprefix tailTrace_264858
  have hstable : (prefixWord ++ tailWord_264858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264858).length < 2 ^ (prefixWord ++ tailWord_264858).sum := by decide
  have hdescent : baseEnd_264858 < baseStart_264858 := by decide
  rcases family_descends (prefixWord ++ tailWord_264858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264881 : List Nat := [1, 2, 2, 6, 2, 1, 1, 3, 5]
def baseStart_264881 : Nat := 118140960795 + 264881 * 2 ^ 59
def prefixEnd_264881 : Nat := 4983230072969 + 3 ^ 40 * 264881 * 2
def baseEnd_264881 : Nat := 15112363249298153952149

theorem tailTrace_264881 : CollatzResearch.WordTrace tailWord_264881 prefixEnd_264881 15112363249298153952149 := by
  unfold tailWord_264881
  simp only [CollatzResearch.WordTrace]
  refine ⟨9661003753388849918322497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6440669168925899945548331 9661003753388849918322497)
  ·
    refine ⟨7245752815041637438741873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9661003753388849918322497 7245752815041637438741873)
    ·
      refine ⟨5434314611281228079056405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7245752815041637438741873 5434314611281228079056405)
      ·
        refine ⟨254733497403807566205769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5434314611281228079056405 254733497403807566205769)
        ·
          refine ⟨191050123052855674654327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254733497403807566205769 191050123052855674654327)
          ·
            refine ⟨286575184579283511981491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191050123052855674654327 286575184579283511981491)
            ·
              refine ⟨429862776868925267972237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286575184579283511981491 429862776868925267972237)
              ·
                refine ⟨161198541325846975489589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429862776868925267972237 161198541325846975489589)
                ·
                  refine ⟨15112363249298153952149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161198541325846975489589 15112363249298153952149)
                  ·
                    rfl

theorem cell23_264881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 5].length) (baseStart_264881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264881 prefixEnd_264881 := by exact prefixLift 264881
  have htrace : WordTrace (prefixWord ++ tailWord_264881) baseStart_264881 baseEnd_264881 := by
    simpa [prefixWord, tailWord_264881, baseEnd_264881] using wordTrace_append hprefix tailTrace_264881
  have hstable : (prefixWord ++ tailWord_264881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264881).length < 2 ^ (prefixWord ++ tailWord_264881).sum := by decide
  have hdescent : baseEnd_264881 < baseStart_264881 := by decide
  rcases family_descends (prefixWord ++ tailWord_264881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264920 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 6]
def baseStart_264920 : Nat := 118140960795 + 264920 * 2 ^ 59
def prefixEnd_264920 : Nat := 4983230072969 + 3 ^ 40 * 264920 * 2
def baseEnd_264920 : Nat := 15114588332134303664629

theorem tailTrace_264920 : CollatzResearch.WordTrace tailWord_264920 prefixEnd_264920 15114588332134303664629 := by
  unfold tailWord_264920
  simp only [CollatzResearch.WordTrace]
  refine ⟨4831213100123779789496107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6441617466831706385994809 4831213100123779789496107)
  ·
    refine ⟨7246819650185669684244161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4831213100123779789496107 7246819650185669684244161)
    ·
      refine ⟨5435114737639252263183121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7246819650185669684244161 5435114737639252263183121)
      ·
        refine ⟨4076336053229439197387341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5435114737639252263183121 4076336053229439197387341)
        ·
          refine ⟨1528626019961039699020253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4076336053229439197387341 1528626019961039699020253)
          ·
            refine ⟨573234757485389887132595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1528626019961039699020253 573234757485389887132595)
            ·
              refine ⟨859852136228084830698893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573234757485389887132595 859852136228084830698893)
              ·
                refine ⟨322444551085531811512085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 859852136228084830698893 322444551085531811512085)
                ·
                  refine ⟨15114588332134303664629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 322444551085531811512085 15114588332134303664629)
                  ·
                    rfl

theorem cell23_264920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 6].length) (baseStart_264920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264920 prefixEnd_264920 := by exact prefixLift 264920
  have htrace : WordTrace (prefixWord ++ tailWord_264920) baseStart_264920 baseEnd_264920 := by
    simpa [prefixWord, tailWord_264920, baseEnd_264920] using wordTrace_append hprefix tailTrace_264920
  have hstable : (prefixWord ++ tailWord_264920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264920).length < 2 ^ (prefixWord ++ tailWord_264920).sum := by decide
  have hdescent : baseEnd_264920 < baseStart_264920 := by decide
  rcases family_descends (prefixWord ++ tailWord_264920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264957 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 2, 3, 2]
def baseStart_264957 : Nat := 118140960795 + 264957 * 2 ^ 59
def prefixEnd_264957 : Nat := 4983230072969 + 3 ^ 40 * 264957 * 2
def baseEnd_264957 : Nat := 136050293773425088218991

theorem tailTrace_264957 : CollatzResearch.WordTrace tailWord_264957 prefixEnd_264957 136050293773425088218991 := by
  unfold tailWord_264957
  simp only [CollatzResearch.WordTrace]
  refine ⟨9663775701113514898089125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6442517134075676598726083 9663775701113514898089125)
  ·
    refine ⟨1811957943958784043391711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9663775701113514898089125 1811957943958784043391711)
    ·
      refine ⟨2717936915938176065087567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1811957943958784043391711 2717936915938176065087567)
      ·
        refine ⟨4076905373907264097631351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717936915938176065087567 4076905373907264097631351)
        ·
          refine ⟨6115358060860896146447027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4076905373907264097631351 6115358060860896146447027)
          ·
            refine ⟨9173037091291344219670541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6115358060860896146447027 9173037091291344219670541)
            ·
              refine ⟨3439888909234254082376453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9173037091291344219670541 3439888909234254082376453)
              ·
                refine ⟨644979170481422640445585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3439888909234254082376453 644979170481422640445585)
                ·
                  refine ⟨483734377861066980334189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 644979170481422640445585 483734377861066980334189)
                  ·
                    refine ⟨181400391697900117625321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483734377861066980334189 181400391697900117625321)
                    ·
                      refine ⟨136050293773425088218991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 181400391697900117625321 136050293773425088218991)
                      ·
                        rfl

theorem cell23_264957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_264957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264957 prefixEnd_264957 := by exact prefixLift 264957
  have htrace : WordTrace (prefixWord ++ tailWord_264957) baseStart_264957 baseEnd_264957 := by
    simpa [prefixWord, tailWord_264957, baseEnd_264957] using wordTrace_append hprefix tailTrace_264957
  have hstable : (prefixWord ++ tailWord_264957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264957).length < 2 ^ (prefixWord ++ tailWord_264957).sum := by decide
  have hdescent : baseEnd_264957 < baseStart_264957 := by decide
  rcases family_descends (prefixWord ++ tailWord_264957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264958 : List Nat := [4, 2, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_264958 : Nat := 118140960795 + 264958 * 2 ^ 59
def prefixEnd_264958 : Nat := 4983230072969 + 3 ^ 40 * 264958 * 2
def baseEnd_264958 : Nat := 45350269084693194768829

theorem tailTrace_264958 : CollatzResearch.WordTrace tailWord_264958 prefixEnd_264958 45350269084693194768829 := by
  unfold tailWord_264958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1207976521763736508609441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6442541449406594712583685 1207976521763736508609441)
  ·
    refine ⟨905982391322802381457081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1207976521763736508609441 905982391322802381457081)
    ·
      refine ⟨679486793492101786092811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 905982391322802381457081 679486793492101786092811)
      ·
        refine ⟨1019230190238152679139217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679486793492101786092811 1019230190238152679139217)
        ·
          refine ⟨764422642678614509354413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019230190238152679139217 764422642678614509354413)
          ·
            refine ⟨286658491004480441007905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 764422642678614509354413 286658491004480441007905)
            ·
              refine ⟨214993868253360330755929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286658491004480441007905 214993868253360330755929)
              ·
                refine ⟨161245401190020248066947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214993868253360330755929 161245401190020248066947)
                ·
                  refine ⟨241868101785030372100421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161245401190020248066947 241868101785030372100421)
                  ·
                    refine ⟨45350269084693194768829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241868101785030372100421 45350269084693194768829)
                    ·
                      rfl

theorem cell23_264958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_264958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264958 prefixEnd_264958 := by exact prefixLift 264958
  have htrace : WordTrace (prefixWord ++ tailWord_264958) baseStart_264958 baseEnd_264958 := by
    simpa [prefixWord, tailWord_264958, baseEnd_264958] using wordTrace_append hprefix tailTrace_264958
  have hstable : (prefixWord ++ tailWord_264958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264958).length < 2 ^ (prefixWord ++ tailWord_264958).sum := by decide
  have hdescent : baseEnd_264958 < baseStart_264958 := by decide
  rcases family_descends (prefixWord ++ tailWord_264958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264963 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 5, 6]
def baseStart_264963 : Nat := 118140960795 + 264963 * 2 ^ 59
def prefixEnd_264963 : Nat := 4983230072969 + 3 ^ 40 * 264963 * 2
def baseEnd_264963 : Nat := 45351124885784021581321

theorem tailTrace_264963 : CollatzResearch.WordTrace tailWord_264963 prefixEnd_264963 45351124885784021581321 := by
  unfold tailWord_264963
  simp only [CollatzResearch.WordTrace]
  refine ⟨9663994539091777922807543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6442663026061185281871695 9663994539091777922807543)
  ·
    refine ⟨14495991808637666884211315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9663994539091777922807543 14495991808637666884211315)
    ·
      refine ⟨21743987712956500326316973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14495991808637666884211315 21743987712956500326316973)
      ·
        refine ⟨8153995392358687622368865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21743987712956500326316973 8153995392358687622368865)
        ·
          refine ⟨6115496544269015716776649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8153995392358687622368865 6115496544269015716776649)
          ·
            refine ⟨4586622408201761787582487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6115496544269015716776649 4586622408201761787582487)
            ·
              refine ⟨6879933612302642681373731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4586622408201761787582487 6879933612302642681373731)
              ·
                refine ⟨10319900418453964022060597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6879933612302642681373731 10319900418453964022060597)
                ·
                  refine ⟨967490664230059127068181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10319900418453964022060597 967490664230059127068181)
                  ·
                    refine ⟨45351124885784021581321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 967490664230059127068181 45351124885784021581321)
                    ·
                      rfl

theorem cell23_264963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 6].length) (baseStart_264963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264963 prefixEnd_264963 := by exact prefixLift 264963
  have htrace : WordTrace (prefixWord ++ tailWord_264963) baseStart_264963 baseEnd_264963 := by
    simpa [prefixWord, tailWord_264963, baseEnd_264963] using wordTrace_append hprefix tailTrace_264963
  have hstable : (prefixWord ++ tailWord_264963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264963).length < 2 ^ (prefixWord ++ tailWord_264963).sum := by decide
  have hdescent : baseEnd_264963 < baseStart_264963 := by decide
  rcases family_descends (prefixWord ++ tailWord_264963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264970 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_264970 : Nat := 118140960795 + 264970 * 2 ^ 59
def prefixEnd_264970 : Nat := 4983230072969 + 3 ^ 40 * 264970 * 2
def baseEnd_264970 : Nat := 136056969021933537356431

theorem tailTrace_264970 : CollatzResearch.WordTrace tailWord_264970 prefixEnd_264970 136056969021933537356431 := by
  unfold tailWord_264970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2416062462516604529578091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6442833233377612078874909 2416062462516604529578091)
  ·
    refine ⟨3624093693774906794367137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2416062462516604529578091 3624093693774906794367137)
    ·
      refine ⟨2718070270331180095775353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3624093693774906794367137 2718070270331180095775353)
      ·
        refine ⟨2038552702748385071831515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2718070270331180095775353 2038552702748385071831515)
        ·
          refine ⟨3057829054122577607747273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038552702748385071831515 3057829054122577607747273)
          ·
            refine ⟨2293371790591933205810455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3057829054122577607747273 2293371790591933205810455)
            ·
              refine ⟨3440057685887899808715683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293371790591933205810455 3440057685887899808715683)
              ·
                refine ⟨5160086528831849713073525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440057685887899808715683 5160086528831849713073525)
                ·
                  refine ⟨483758112077985910600643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5160086528831849713073525 483758112077985910600643)
                  ·
                    refine ⟨725637168116978865900965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 483758112077985910600643 725637168116978865900965)
                    ·
                      refine ⟨136056969021933537356431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 725637168116978865900965 136056969021933537356431)
                      ·
                        rfl

theorem cell23_264970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_264970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_264970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_264970 prefixEnd_264970 := by exact prefixLift 264970
  have htrace : WordTrace (prefixWord ++ tailWord_264970) baseStart_264970 baseEnd_264970 := by
    simpa [prefixWord, tailWord_264970, baseEnd_264970] using wordTrace_append hprefix tailTrace_264970
  have hstable : (prefixWord ++ tailWord_264970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264970).length < 2 ^ (prefixWord ++ tailWord_264970).sum := by decide
  have hdescent : baseEnd_264970 < baseStart_264970 := by decide
  rcases family_descends (prefixWord ++ tailWord_264970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265044 : List Nat := [2, 4, 1, 1, 4, 2, 2, 7]
def baseStart_265044 : Nat := 118140960795 + 265044 * 2 ^ 59
def prefixEnd_265044 : Nat := 4983230072969 + 3 ^ 40 * 265044 * 2
def baseEnd_265044 : Nat := 5040554318161712882633

theorem tailTrace_265044 : CollatzResearch.WordTrace tailWord_265044 prefixEnd_265044 5040554318161712882633 := by
  unfold tailWord_265044
  simp only [CollatzResearch.WordTrace]
  refine ⟨4833474425899164378253093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6444632567865552504337457 4833474425899164378253093)
  ·
    refine ⟨906276454856093320922455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4833474425899164378253093 906276454856093320922455)
    ·
      refine ⟨1359414682284139981383683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906276454856093320922455 1359414682284139981383683)
      ·
        refine ⟨2039122023426209972075525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359414682284139981383683 2039122023426209972075525)
        ·
          refine ⟨382335379392414369764161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2039122023426209972075525 382335379392414369764161)
          ·
            refine ⟨286751534544310777323121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382335379392414369764161 286751534544310777323121)
            ·
              refine ⟨215063650908233082992341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286751534544310777323121 215063650908233082992341)
              ·
                refine ⟨5040554318161712882633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 215063650908233082992341 5040554318161712882633)
                ·
                  rfl

theorem cell23_265044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 7].length) (baseStart_265044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265044 prefixEnd_265044 := by exact prefixLift 265044
  have htrace : WordTrace (prefixWord ++ tailWord_265044) baseStart_265044 baseEnd_265044 := by
    simpa [prefixWord, tailWord_265044, baseEnd_265044] using wordTrace_append hprefix tailTrace_265044
  have hstable : (prefixWord ++ tailWord_265044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265044).length < 2 ^ (prefixWord ++ tailWord_265044).sum := by decide
  have hdescent : baseEnd_265044 < baseStart_265044 := by decide
  rcases family_descends (prefixWord ++ tailWord_265044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265050 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_265050 : Nat := 118140960795 + 265050 * 2 ^ 59
def prefixEnd_265050 : Nat := 4983230072969 + 3 ^ 40 * 265050 * 2
def baseEnd_265050 : Nat := 136098047474293224356063

theorem tailTrace_265050 : CollatzResearch.WordTrace tailWord_265050 prefixEnd_265050 136098047474293224356063 := by
  unfold tailWord_265050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2416791922444147945306151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6444778459851061187483069 2416791922444147945306151)
  ·
    refine ⟨3625187883666221917959227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2416791922444147945306151 3625187883666221917959227)
    ·
      refine ⟨5437781825499332876938841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3625187883666221917959227 5437781825499332876938841)
      ·
        refine ⟨4078336369124499657704131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5437781825499332876938841 4078336369124499657704131)
        ·
          refine ⟨6117504553686749486556197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078336369124499657704131 6117504553686749486556197)
          ·
            refine ⟨1147032103816265528729287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6117504553686749486556197 1147032103816265528729287)
            ·
              refine ⟨1720548155724398293093931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147032103816265528729287 1720548155724398293093931)
              ·
                refine ⟨2580822233586597439640897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720548155724398293093931 2580822233586597439640897)
                ·
                  refine ⟨1935616675189948079730673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2580822233586597439640897 1935616675189948079730673)
                  ·
                    refine ⟨1451712506392461059798005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1935616675189948079730673 1451712506392461059798005)
                    ·
                      refine ⟨136098047474293224356063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1451712506392461059798005 136098047474293224356063)
                      ·
                        rfl

theorem cell23_265050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_265050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265050 prefixEnd_265050 := by exact prefixLift 265050
  have htrace : WordTrace (prefixWord ++ tailWord_265050) baseStart_265050 baseEnd_265050 := by
    simpa [prefixWord, tailWord_265050, baseEnd_265050] using wordTrace_append hprefix tailTrace_265050
  have hstable : (prefixWord ++ tailWord_265050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265050).length < 2 ^ (prefixWord ++ tailWord_265050).sum := by decide
  have hdescent : baseEnd_265050 < baseStart_265050 := by decide
  rcases family_descends (prefixWord ++ tailWord_265050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265098 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2]
def baseStart_265098 : Nat := 118140960795 + 265098 * 2 ^ 59
def prefixEnd_265098 : Nat := 4983230072969 + 3 ^ 40 * 265098 * 2
def baseEnd_265098 : Nat := 136122694545709036555843

theorem tailTrace_265098 : CollatzResearch.WordTrace tailWord_265098 prefixEnd_265098 136122694545709036555843 := by
  unfold tailWord_265098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417229598400673994742987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6445945595735130652647965 2417229598400673994742987)
  ·
    refine ⟨3625844397601010992114481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2417229598400673994742987 3625844397601010992114481)
    ·
      refine ⟨2719383298200758244085861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3625844397601010992114481 2719383298200758244085861)
      ·
        refine ⟨509884368412642170766099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2719383298200758244085861 509884368412642170766099)
        ·
          refine ⟨764826552618963256149149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509884368412642170766099 764826552618963256149149)
          ·
            refine ⟨286809957232111221055931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 764826552618963256149149 286809957232111221055931)
            ·
              refine ⟨430214935848166831583897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286809957232111221055931 430214935848166831583897)
              ·
                refine ⟨322661201886125123687923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430214935848166831583897 322661201886125123687923)
                ·
                  refine ⟨483991802829187685531885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322661201886125123687923 483991802829187685531885)
                  ·
                    refine ⟨181496926060945382074457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 483991802829187685531885 181496926060945382074457)
                    ·
                      refine ⟨136122694545709036555843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 181496926060945382074457 136122694545709036555843)
                      ·
                        rfl

theorem cell23_265098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_265098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265098 prefixEnd_265098 := by exact prefixLift 265098
  have htrace : WordTrace (prefixWord ++ tailWord_265098) baseStart_265098 baseEnd_265098 := by
    simpa [prefixWord, tailWord_265098, baseEnd_265098] using wordTrace_append hprefix tailTrace_265098
  have hstable : (prefixWord ++ tailWord_265098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265098).length < 2 ^ (prefixWord ++ tailWord_265098).sum := by decide
  have hdescent : baseEnd_265098 < baseStart_265098 := by decide
  rcases family_descends (prefixWord ++ tailWord_265098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265100 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 7]
def baseStart_265100 : Nat := 118140960795 + 265100 * 2 ^ 59
def prefixEnd_265100 : Nat := 4983230072969 + 3 ^ 40 * 265100 * 2
def baseEnd_265100 : Nat := 15124857945224225414537

theorem tailTrace_265100 : CollatzResearch.WordTrace tailWord_265100 prefixEnd_265100 15124857945224225414537 := by
  unfold tailWord_265100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4834495669797725160272377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6445994226396966880363169 4834495669797725160272377)
  ·
    refine ⟨3625871752348293870204283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4834495669797725160272377 3625871752348293870204283)
    ·
      refine ⟨5438807628522440805306425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3625871752348293870204283 5438807628522440805306425)
      ·
        refine ⟨4079105721391830603979819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5438807628522440805306425 4079105721391830603979819)
        ·
          refine ⟨6118658582087745905969729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079105721391830603979819 6118658582087745905969729)
          ·
            refine ⟨4588993936565809429477297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6118658582087745905969729 4588993936565809429477297)
            ·
              refine ⟨3441745452424357072107973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4588993936565809429477297 3441745452424357072107973)
              ·
                refine ⟨645327272329566951020245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3441745452424357072107973 645327272329566951020245)
                ·
                  refine ⟨15124857945224225414537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 645327272329566951020245 15124857945224225414537)
                  ·
                    rfl

theorem cell23_265100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_265100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265100 prefixEnd_265100 := by exact prefixLift 265100
  have htrace : WordTrace (prefixWord ++ tailWord_265100) baseStart_265100 baseEnd_265100 := by
    simpa [prefixWord, tailWord_265100, baseEnd_265100] using wordTrace_append hprefix tailTrace_265100
  have hstable : (prefixWord ++ tailWord_265100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265100).length < 2 ^ (prefixWord ++ tailWord_265100).sum := by decide
  have hdescent : baseEnd_265100 < baseStart_265100 := by decide
  rcases family_descends (prefixWord ++ tailWord_265100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265167 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 4]
def baseStart_265167 : Nat := 118140960795 + 265167 * 2 ^ 59
def prefixEnd_265167 : Nat := 4983230072969 + 3 ^ 40 * 265167 * 2
def baseEnd_265167 : Nat := 136158124710869266593025

theorem tailTrace_265167 : CollatzResearch.WordTrace tailWord_265167 prefixEnd_265167 136158124710869266593025 := by
  unfold tailWord_265167
  simp only [CollatzResearch.WordTrace]
  refine ⟨9671435030352720763233755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6447623353568480508822503 9671435030352720763233755)
  ·
    refine ⟨14507152545529081144850633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9671435030352720763233755 14507152545529081144850633)
    ·
      refine ⟨10880364409146810858637975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14507152545529081144850633 10880364409146810858637975)
      ·
        refine ⟨16320546613720216287956963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10880364409146810858637975 16320546613720216287956963)
        ·
          refine ⟨24480819920580324431935445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16320546613720216287956963 24480819920580324431935445)
          ·
            refine ⟨573769216888601353873487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 24480819920580324431935445 573769216888601353873487)
            ·
              refine ⟨860653825332902030810231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573769216888601353873487 860653825332902030810231)
              ·
                refine ⟨1290980737999353046215347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860653825332902030810231 1290980737999353046215347)
                ·
                  refine ⟨1936471106999029569323021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290980737999353046215347 1936471106999029569323021)
                  ·
                    refine ⟨726176665124636088496133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1936471106999029569323021 726176665124636088496133)
                    ·
                      refine ⟨136158124710869266593025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 726176665124636088496133 136158124710869266593025)
                      ·
                        rfl

theorem cell23_265167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_265167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265167 prefixEnd_265167 := by exact prefixLift 265167
  have htrace : WordTrace (prefixWord ++ tailWord_265167) baseStart_265167 baseEnd_265167 := by
    simpa [prefixWord, tailWord_265167, baseEnd_265167] using wordTrace_append hprefix tailTrace_265167
  have hstable : (prefixWord ++ tailWord_265167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265167).length < 2 ^ (prefixWord ++ tailWord_265167).sum := by decide
  have hdescent : baseEnd_265167 < baseStart_265167 := by decide
  rcases family_descends (prefixWord ++ tailWord_265167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265194 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 3, 4]
def baseStart_265194 : Nat := 118140960795 + 265194 * 2 ^ 59
def prefixEnd_265194 : Nat := 4983230072969 + 3 ^ 40 * 265194 * 2
def baseEnd_265194 : Nat := 45390662896180220318467

theorem tailTrace_265194 : CollatzResearch.WordTrace tailWord_265194 prefixEnd_265194 45390662896180220318467 := by
  unfold tailWord_265194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418104950313726093616659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6448279867503269582977757 2418104950313726093616659)
  ·
    refine ⟨3627157425470589140424989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2418104950313726093616659 3627157425470589140424989)
    ·
      refine ⟨1360184034551470927659371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3627157425470589140424989 1360184034551470927659371)
      ·
        refine ⟨2040276051827206391489057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1360184034551470927659371 2040276051827206391489057)
        ·
          refine ⟨1530207038870404793616793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2040276051827206391489057 1530207038870404793616793)
          ·
            refine ⟨1147655279152803595212595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1530207038870404793616793 1147655279152803595212595)
            ·
              refine ⟨1721482918729205392818893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147655279152803595212595 1721482918729205392818893)
              ·
                refine ⟨645556094523452022307085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1721482918729205392818893 645556094523452022307085)
                ·
                  refine ⟨242083535446294508365157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645556094523452022307085 242083535446294508365157)
                  ·
                    refine ⟨45390662896180220318467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242083535446294508365157 45390662896180220318467)
                    ·
                      rfl

theorem cell23_265194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_265194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265194 prefixEnd_265194 := by exact prefixLift 265194
  have htrace : WordTrace (prefixWord ++ tailWord_265194) baseStart_265194 baseEnd_265194 := by
    simpa [prefixWord, tailWord_265194, baseEnd_265194] using wordTrace_append hprefix tailTrace_265194
  have hstable : (prefixWord ++ tailWord_265194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265194).length < 2 ^ (prefixWord ++ tailWord_265194).sum := by decide
  have hdescent : baseEnd_265194 < baseStart_265194 := by decide
  rcases family_descends (prefixWord ++ tailWord_265194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265228 : List Nat := [2, 2, 1, 2, 3, 4, 1, 3, 1, 4]
def baseStart_265228 : Nat := 118140960795 + 265228 * 2 ^ 59
def prefixEnd_265228 : Nat := 4983230072969 + 3 ^ 40 * 265228 * 2
def baseEnd_265228 : Nat := 45396482343597842643415

theorem tailTrace_265228 : CollatzResearch.WordTrace tailWord_265228 prefixEnd_265228 45396482343597842643415 := by
  unfold tailWord_265228
  simp only [CollatzResearch.WordTrace]
  refine ⟨4836829941565864090602169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6449106588754485454136225 4836829941565864090602169)
  ·
    refine ⟨3627622456174398067951627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4836829941565864090602169 3627622456174398067951627)
    ·
      refine ⟨5441433684261597101927441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3627622456174398067951627 5441433684261597101927441)
      ·
        refine ⟨4081075263196197826445581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5441433684261597101927441 4081075263196197826445581)
        ·
          refine ⟨1530403223698574184917093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4081075263196197826445581 1530403223698574184917093)
          ·
            refine ⟨286950604443482659671955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1530403223698574184917093 286950604443482659671955)
            ·
              refine ⟨430425906665223989507933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286950604443482659671955 430425906665223989507933)
              ·
                refine ⟨161409714999458996065475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430425906665223989507933 161409714999458996065475)
                ·
                  refine ⟨242114572499188494098213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161409714999458996065475 242114572499188494098213)
                  ·
                    refine ⟨45396482343597842643415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242114572499188494098213 45396482343597842643415)
                    ·
                      rfl

theorem cell23_265228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_265228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265228 prefixEnd_265228 := by exact prefixLift 265228
  have htrace : WordTrace (prefixWord ++ tailWord_265228) baseStart_265228 baseEnd_265228 := by
    simpa [prefixWord, tailWord_265228, baseEnd_265228] using wordTrace_append hprefix tailTrace_265228
  have hstable : (prefixWord ++ tailWord_265228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265228).length < 2 ^ (prefixWord ++ tailWord_265228).sum := by decide
  have hdescent : baseEnd_265228 < baseStart_265228 := by decide
  rcases family_descends (prefixWord ++ tailWord_265228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265245 : List Nat := [1, 4, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_265245 : Nat := 118140960795 + 265245 * 2 ^ 59
def prefixEnd_265245 : Nat := 4983230072969 + 3 ^ 40 * 265245 * 2
def baseEnd_265245 : Nat := 45399392067306653805889

theorem tailTrace_265245 : CollatzResearch.WordTrace tailWord_265245 prefixEnd_265245 45399392067306653805889 := by
  unfold tailWord_265245
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674279924070140084573189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6449519949380093389715459 9674279924070140084573189)
  ·
    refine ⟨1813927485763151265857473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9674279924070140084573189 1813927485763151265857473)
    ·
      refine ⟨1360445614322363449393105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1813927485763151265857473 1360445614322363449393105)
      ·
        refine ⟨1020334210741772587044829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1360445614322363449393105 1020334210741772587044829)
        ·
          refine ⟨382625329028164720141811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1020334210741772587044829 382625329028164720141811)
          ·
            refine ⟨573937993542247080212717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382625329028164720141811 573937993542247080212717)
            ·
              refine ⟨215226747578342655079769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573937993542247080212717 215226747578342655079769)
              ·
                refine ⟨161420060683756991309827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215226747578342655079769 161420060683756991309827)
                ·
                  refine ⟨242130091025635486964741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161420060683756991309827 242130091025635486964741)
                  ·
                    refine ⟨45399392067306653805889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242130091025635486964741 45399392067306653805889)
                    ·
                      rfl

theorem cell23_265245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_265245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265245 prefixEnd_265245 := by exact prefixLift 265245
  have htrace : WordTrace (prefixWord ++ tailWord_265245) baseStart_265245 baseEnd_265245 := by
    simpa [prefixWord, tailWord_265245, baseEnd_265245] using wordTrace_append hprefix tailTrace_265245
  have hstable : (prefixWord ++ tailWord_265245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265245).length < 2 ^ (prefixWord ++ tailWord_265245).sum := by decide
  have hdescent : baseEnd_265245 < baseStart_265245 := by decide
  rcases family_descends (prefixWord ++ tailWord_265245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265251 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 3, 1, 3]
def baseStart_265251 : Nat := 118140960795 + 265251 * 2 ^ 59
def prefixEnd_265251 : Nat := 4983230072969 + 3 ^ 40 * 265251 * 2
def baseEnd_265251 : Nat := 136201257085846937942639

theorem tailTrace_265251 : CollatzResearch.WordTrace tailWord_265251 prefixEnd_265251 136201257085846937942639 := by
  unfold tailWord_265251
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674498762048403109291607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6449665841365602072861071 9674498762048403109291607)
  ·
    refine ⟨14511748143072604663937411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9674498762048403109291607 14511748143072604663937411)
    ·
      refine ⟨21767622214608906995906117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14511748143072604663937411 21767622214608906995906117)
      ·
        refine ⟨4081429165239170061732397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21767622214608906995906117 4081429165239170061732397)
        ·
          refine ⟨1530535936964688773149649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4081429165239170061732397 1530535936964688773149649)
          ·
            refine ⟨1147901952723516579862237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1530535936964688773149649 1147901952723516579862237)
            ·
              refine ⟨430463232271318717448339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1147901952723516579862237 430463232271318717448339)
              ·
                refine ⟨645694848406978076172509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430463232271318717448339 645694848406978076172509)
                ·
                  refine ⟨242135568152616778564691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645694848406978076172509 242135568152616778564691)
                  ·
                    refine ⟨363203352228925167847037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242135568152616778564691 363203352228925167847037)
                    ·
                      refine ⟨136201257085846937942639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 363203352228925167847037 136201257085846937942639)
                      ·
                        rfl

theorem cell23_265251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_265251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265251 prefixEnd_265251 := by exact prefixLift 265251
  have htrace : WordTrace (prefixWord ++ tailWord_265251) baseStart_265251 baseEnd_265251 := by
    simpa [prefixWord, tailWord_265251, baseEnd_265251] using wordTrace_append hprefix tailTrace_265251
  have hstable : (prefixWord ++ tailWord_265251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265251).length < 2 ^ (prefixWord ++ tailWord_265251).sum := by decide
  have hdescent : baseEnd_265251 < baseStart_265251 := by decide
  rcases family_descends (prefixWord ++ tailWord_265251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265258 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 6]
def baseStart_265258 : Nat := 118140960795 + 265258 * 2 ^ 59
def prefixEnd_265258 : Nat := 4983230072969 + 3 ^ 40 * 265258 * 2
def baseEnd_265258 : Nat := 15133872383380934506123

theorem tailTrace_265258 : CollatzResearch.WordTrace tailWord_265258 prefixEnd_265258 15133872383380934506123 := by
  unfold tailWord_265258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418688518255760826199107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6449836048682028869864285 2418688518255760826199107)
  ·
    refine ⟨3628032777383641239298661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2418688518255760826199107 3628032777383641239298661)
    ·
      refine ⟨680256145759432732368499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3628032777383641239298661 680256145759432732368499)
      ·
        refine ⟨1020384218639149098552749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680256145759432732368499 1020384218639149098552749)
        ·
          refine ⟨382644081989680911957281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1020384218639149098552749 382644081989680911957281)
          ·
            refine ⟨286983061492260683967961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382644081989680911957281 286983061492260683967961)
            ·
              refine ⟨215237296119195512975971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286983061492260683967961 215237296119195512975971)
              ·
                refine ⟨322855944178793269463957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215237296119195512975971 322855944178793269463957)
                ·
                  refine ⟨15133872383380934506123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 322855944178793269463957 15133872383380934506123)
                  ·
                    rfl

theorem cell23_265258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_265258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265258 prefixEnd_265258 := by exact prefixLift 265258
  have htrace : WordTrace (prefixWord ++ tailWord_265258) baseStart_265258 baseEnd_265258 := by
    simpa [prefixWord, tailWord_265258, baseEnd_265258] using wordTrace_append hprefix tailTrace_265258
  have hstable : (prefixWord ++ tailWord_265258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265258).length < 2 ^ (prefixWord ++ tailWord_265258).sum := by decide
  have hdescent : baseEnd_265258 < baseStart_265258 := by decide
  rcases family_descends (prefixWord ++ tailWord_265258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265267 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 1, 6]
def baseStart_265267 : Nat := 118140960795 + 265267 * 2 ^ 59
def prefixEnd_265267 : Nat := 4983230072969 + 3 ^ 40 * 265267 * 2
def baseEnd_265267 : Nat := 45403157592106291780855

theorem tailTrace_265267 : CollatzResearch.WordTrace tailWord_265267 prefixEnd_265267 45403157592106291780855 := by
  unfold tailWord_265267
  simp only [CollatzResearch.WordTrace]
  refine ⟨9675082329990437841874055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6450054886660291894582703 9675082329990437841874055)
  ·
    refine ⟨14512623494985656762811083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9675082329990437841874055 14512623494985656762811083)
    ·
      refine ⟨21768935242478485144216625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14512623494985656762811083 21768935242478485144216625)
      ·
        refine ⟨16326701431858863858162469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21768935242478485144216625 16326701431858863858162469)
        ·
          refine ⟨3061256518473536973405463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16326701431858863858162469 3061256518473536973405463)
          ·
            refine ⟨4591884777710305460108195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3061256518473536973405463 4591884777710305460108195)
            ·
              refine ⟨6887827166565458190162293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4591884777710305460108195 6887827166565458190162293)
              ·
                refine ⟨645733796865511705327715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6887827166565458190162293 645733796865511705327715)
                ·
                  refine ⟨968600695298267557991573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645733796865511705327715 968600695298267557991573)
                  ·
                    refine ⟨45403157592106291780855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 968600695298267557991573 45403157592106291780855)
                    ·
                      rfl

theorem cell23_265267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 6].length) (baseStart_265267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265267 prefixEnd_265267 := by exact prefixLift 265267
  have htrace : WordTrace (prefixWord ++ tailWord_265267) baseStart_265267 baseEnd_265267 := by
    simpa [prefixWord, tailWord_265267, baseEnd_265267] using wordTrace_append hprefix tailTrace_265267
  have hstable : (prefixWord ++ tailWord_265267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265267).length < 2 ^ (prefixWord ++ tailWord_265267).sum := by decide
  have hdescent : baseEnd_265267 < baseStart_265267 := by decide
  rcases family_descends (prefixWord ++ tailWord_265267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265274 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2]
def baseStart_265274 : Nat := 118140960795 + 265274 * 2 ^ 59
def prefixEnd_265274 : Nat := 4983230072969 + 3 ^ 40 * 265274 * 2
def baseEnd_265274 : Nat := 136213067140900347955033

theorem tailTrace_265274 : CollatzResearch.WordTrace tailWord_265274 prefixEnd_265274 136213067140900347955033 := by
  unfold tailWord_265274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418834410241269509344719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6450225093976718691585917 2418834410241269509344719)
  ·
    refine ⟨3628251615361904264017079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2418834410241269509344719 3628251615361904264017079)
    ·
      refine ⟨5442377423042856396025619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3628251615361904264017079 5442377423042856396025619)
      ·
        refine ⟨8163566134564284594038429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5442377423042856396025619 8163566134564284594038429)
        ·
          refine ⟨3061337300461606722764411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8163566134564284594038429 3061337300461606722764411)
          ·
            refine ⟨4592005950692410084146617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3061337300461606722764411 4592005950692410084146617)
            ·
              refine ⟨3444004463019307563109963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4592005950692410084146617 3444004463019307563109963)
              ·
                refine ⟨5166006694528961344664945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3444004463019307563109963 5166006694528961344664945)
                ·
                  refine ⟨3874505020896721008498709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5166006694528961344664945 3874505020896721008498709)
                  ·
                    refine ⟨181617422854533797273377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3874505020896721008498709 181617422854533797273377)
                    ·
                      refine ⟨136213067140900347955033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 181617422854533797273377 136213067140900347955033)
                      ·
                        rfl

theorem cell23_265274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2].length) (baseStart_265274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265274 prefixEnd_265274 := by exact prefixLift 265274
  have htrace : WordTrace (prefixWord ++ tailWord_265274) baseStart_265274 baseEnd_265274 := by
    simpa [prefixWord, tailWord_265274, baseEnd_265274] using wordTrace_append hprefix tailTrace_265274
  have hstable : (prefixWord ++ tailWord_265274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265274).length < 2 ^ (prefixWord ++ tailWord_265274).sum := by decide
  have hdescent : baseEnd_265274 < baseStart_265274 := by decide
  rcases family_descends (prefixWord ++ tailWord_265274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265278 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_265278 : Nat := 118140960795 + 265278 * 2 ^ 59
def prefixEnd_265278 : Nat := 4983230072969 + 3 ^ 40 * 265278 * 2
def baseEnd_265278 : Nat := 136215121063518332305015

theorem tailTrace_265278 : CollatzResearch.WordTrace tailWord_265278 prefixEnd_265278 136215121063518332305015 := by
  unfold tailWord_265278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209435441618823340065561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6450322355300391147016325 1209435441618823340065561)
  ·
    refine ⟨907076581214117505049171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1209435441618823340065561 907076581214117505049171)
    ·
      refine ⟨1360614871821176257573757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 907076581214117505049171 1360614871821176257573757)
      ·
        refine ⟨510230576932941096590159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1360614871821176257573757 510230576932941096590159)
        ·
          refine ⟨765345865399411644885239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510230576932941096590159 765345865399411644885239)
          ·
            refine ⟨1148018798099117467327859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765345865399411644885239 1148018798099117467327859)
            ·
              refine ⟨1722028197148676200991789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148018798099117467327859 1722028197148676200991789)
              ·
                refine ⟨645760573930753575371921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1722028197148676200991789 645760573930753575371921)
                ·
                  refine ⟨484320430448065181528941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 645760573930753575371921 484320430448065181528941)
                  ·
                    refine ⟨181620161418024443073353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 484320430448065181528941 181620161418024443073353)
                    ·
                      refine ⟨136215121063518332305015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 181620161418024443073353 136215121063518332305015)
                      ·
                        rfl

theorem cell23_265278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_265278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265278 prefixEnd_265278 := by exact prefixLift 265278
  have htrace : WordTrace (prefixWord ++ tailWord_265278) baseStart_265278 baseEnd_265278 := by
    simpa [prefixWord, tailWord_265278, baseEnd_265278] using wordTrace_append hprefix tailTrace_265278
  have hstable : (prefixWord ++ tailWord_265278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265278).length < 2 ^ (prefixWord ++ tailWord_265278).sum := by decide
  have hdescent : baseEnd_265278 < baseStart_265278 := by decide
  rcases family_descends (prefixWord ++ tailWord_265278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265301 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 2, 4]
def baseStart_265301 : Nat := 118140960795 + 265301 * 2 ^ 59
def prefixEnd_265301 : Nat := 4983230072969 + 3 ^ 40 * 265301 * 2
def baseEnd_265301 : Nat := 45408977039523914105803

theorem tailTrace_265301 : CollatzResearch.WordTrace tailWord_265301 prefixEnd_265301 45408977039523914105803 := by
  unfold tailWord_265301
  simp only [CollatzResearch.WordTrace]
  refine ⟨9676322411867261648611757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6450881607911507765741171 9676322411867261648611757)
  ·
    refine ⟨3628620904450223118229409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9676322411867261648611757 3628620904450223118229409)
    ·
      refine ⟨2721465678337667338672057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3628620904450223118229409 2721465678337667338672057)
      ·
        refine ⟨2041099258753250504004043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2721465678337667338672057 2041099258753250504004043)
        ·
          refine ⟨3061648888129875756006065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2041099258753250504004043 3061648888129875756006065)
          ·
            refine ⟨2296236666097406817004549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3061648888129875756006065 2296236666097406817004549)
            ·
              refine ⟨430544374893263778188353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2296236666097406817004549 430544374893263778188353)
              ·
                refine ⟨322908281169947833641265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430544374893263778188353 322908281169947833641265)
                ·
                  refine ⟨242181210877460875230949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322908281169947833641265 242181210877460875230949)
                  ·
                    refine ⟨45408977039523914105803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242181210877460875230949 45408977039523914105803)
                    ·
                      rfl

theorem cell23_265301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_265301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265301 prefixEnd_265301 := by exact prefixLift 265301
  have htrace : WordTrace (prefixWord ++ tailWord_265301) baseStart_265301 baseEnd_265301 := by
    simpa [prefixWord, tailWord_265301, baseEnd_265301] using wordTrace_append hprefix tailTrace_265301
  have hstable : (prefixWord ++ tailWord_265301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265301).length < 2 ^ (prefixWord ++ tailWord_265301).sum := by decide
  have hdescent : baseEnd_265301 < baseStart_265301 := by decide
  rcases family_descends (prefixWord ++ tailWord_265301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265308 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_265308 : Nat := 118140960795 + 265308 * 2 ^ 59
def prefixEnd_265308 : Nat := 4983230072969 + 3 ^ 40 * 265308 * 2
def baseEnd_265308 : Nat := 136230525483153214929877

theorem tailTrace_265308 : CollatzResearch.WordTrace tailWord_265308 prefixEnd_265308 136230525483153214929877 := by
  unfold tailWord_265308
  simp only [CollatzResearch.WordTrace]
  refine ⟨4838288861420950922058289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6451051815227934562744385 4838288861420950922058289)
  ·
    refine ⟨3628716646065713191543717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4838288861420950922058289 3628716646065713191543717)
    ·
      refine ⟨680384371137321223414447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3628716646065713191543717 680384371137321223414447)
      ·
        refine ⟨1020576556705981835121671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680384371137321223414447 1020576556705981835121671)
        ·
          refine ⟨1530864835058972752682507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020576556705981835121671 1530864835058972752682507)
          ·
            refine ⟨2296297252588459129023761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530864835058972752682507 2296297252588459129023761)
            ·
              refine ⟨1722222939441344346767821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2296297252588459129023761 1722222939441344346767821)
              ·
                refine ⟨645833602290504130037933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1722222939441344346767821 645833602290504130037933)
                ·
                  refine ⟨242187600858939048764225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645833602290504130037933 242187600858939048764225)
                  ·
                    refine ⟨181640700644204286573169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 242187600858939048764225 181640700644204286573169)
                    ·
                      refine ⟨136230525483153214929877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 181640700644204286573169 136230525483153214929877)
                      ·
                        rfl

theorem cell23_265308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_265308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265308 prefixEnd_265308 := by exact prefixLift 265308
  have htrace : WordTrace (prefixWord ++ tailWord_265308) baseStart_265308 baseEnd_265308 := by
    simpa [prefixWord, tailWord_265308, baseEnd_265308] using wordTrace_append hprefix tailTrace_265308
  have hstable : (prefixWord ++ tailWord_265308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265308).length < 2 ^ (prefixWord ++ tailWord_265308).sum := by decide
  have hdescent : baseEnd_265308 < baseStart_265308 := by decide
  rcases family_descends (prefixWord ++ tailWord_265308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265327 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 2, 7]
def baseStart_265327 : Nat := 118140960795 + 265327 * 2 ^ 59
def prefixEnd_265327 : Nat := 4983230072969 + 3 ^ 40 * 265327 * 2
def baseEnd_265327 : Nat := 45413427205196213530763

theorem tailTrace_265327 : CollatzResearch.WordTrace tailWord_265327 prefixEnd_265327 45413427205196213530763 := by
  unfold tailWord_265327
  simp only [CollatzResearch.WordTrace]
  refine ⟨9677270709773068089058235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6451513806515378726038823 9677270709773068089058235)
  ·
    refine ⟨14515906064659602133587353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9677270709773068089058235 14515906064659602133587353)
    ·
      refine ⟨10886929548494701600190515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14515906064659602133587353 10886929548494701600190515)
      ·
        refine ⟨16330394322742052400285773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10886929548494701600190515 16330394322742052400285773)
        ·
          refine ⟨6123897871028269650107165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16330394322742052400285773 6123897871028269650107165)
          ·
            refine ⟨2296461701635601118790187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6123897871028269650107165 2296461701635601118790187)
            ·
              refine ⟨3444692552453401678185281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296461701635601118790187 3444692552453401678185281)
              ·
                refine ⟨2583519414340051258638961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3444692552453401678185281 2583519414340051258638961)
                ·
                  refine ⟨1937639560755038443979221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2583519414340051258638961 1937639560755038443979221)
                  ·
                    refine ⟨45413427205196213530763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1937639560755038443979221 45413427205196213530763)
                    ·
                      rfl

theorem cell23_265327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_265327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265327 prefixEnd_265327 := by exact prefixLift 265327
  have htrace : WordTrace (prefixWord ++ tailWord_265327) baseStart_265327 baseEnd_265327 := by
    simpa [prefixWord, tailWord_265327, baseEnd_265327] using wordTrace_append hprefix tailTrace_265327
  have hstable : (prefixWord ++ tailWord_265327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265327).length < 2 ^ (prefixWord ++ tailWord_265327).sum := by decide
  have hdescent : baseEnd_265327 < baseStart_265327 := by decide
  rcases family_descends (prefixWord ++ tailWord_265327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265341 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_265341 : Nat := 118140960795 + 265341 * 2 ^ 59
def prefixEnd_265341 : Nat := 4983230072969 + 3 ^ 40 * 265341 * 2
def baseEnd_265341 : Nat := 136247470344751585817225

theorem tailTrace_265341 : CollatzResearch.WordTrace tailWord_265341 prefixEnd_265341 136247470344751585817225 := by
  unfold tailWord_265341
  simp only [CollatzResearch.WordTrace]
  refine ⟨9677781331722348480067877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6451854221148232320045251 9677781331722348480067877)
  ·
    refine ⟨1814583999697940340012727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9677781331722348480067877 1814583999697940340012727)
    ·
      refine ⟨2721875999546910510019091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1814583999697940340012727 2721875999546910510019091)
      ·
        refine ⟨4082813999320365765028637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2721875999546910510019091 4082813999320365765028637)
        ·
          refine ⟨1531055249745137161885739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4082813999320365765028637 1531055249745137161885739)
          ·
            refine ⟨2296582874617705742828609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531055249745137161885739 2296582874617705742828609)
            ·
              refine ⟨1722437155963279307121457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2296582874617705742828609 1722437155963279307121457)
              ·
                refine ⟨1291827866972459480341093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722437155963279307121457 1291827866972459480341093)
                ·
                  refine ⟨242217725057336152563955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291827866972459480341093 242217725057336152563955)
                  ·
                    refine ⟨363326587586004228845933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242217725057336152563955 363326587586004228845933)
                    ·
                      refine ⟨136247470344751585817225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 363326587586004228845933 136247470344751585817225)
                      ·
                        rfl

theorem cell23_265341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_265341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265341 prefixEnd_265341 := by exact prefixLift 265341
  have htrace : WordTrace (prefixWord ++ tailWord_265341) baseStart_265341 baseEnd_265341 := by
    simpa [prefixWord, tailWord_265341, baseEnd_265341] using wordTrace_append hprefix tailTrace_265341
  have hstable : (prefixWord ++ tailWord_265341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265341).length < 2 ^ (prefixWord ++ tailWord_265341).sum := by decide
  have hdescent : baseEnd_265341 < baseStart_265341 := by decide
  rcases family_descends (prefixWord ++ tailWord_265341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265342 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_265342 : Nat := 118140960795 + 265342 * 2 ^ 59
def prefixEnd_265342 : Nat := 4983230072969 + 3 ^ 40 * 265342 * 2
def baseEnd_265342 : Nat := 136247983825406081904721

theorem tailTrace_265342 : CollatzResearch.WordTrace tailWord_265342 prefixEnd_265342 136247983825406081904721 := by
  unfold tailWord_265342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209727225589840706356785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6451878536479150433902853 1209727225589840706356785)
  ·
    refine ⟨907295419192380529767589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1209727225589840706356785 907295419192380529767589)
    ·
      refine ⟨170117891098571349331423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 907295419192380529767589 170117891098571349331423)
      ·
        refine ⟨255176836647857023997135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170117891098571349331423 255176836647857023997135)
        ·
          refine ⟨382765254971785535995703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255176836647857023997135 382765254971785535995703)
          ·
            refine ⟨574147882457678303993555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382765254971785535995703 574147882457678303993555)
            ·
              refine ⟨861221823686517455990333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574147882457678303993555 861221823686517455990333)
              ·
                refine ⟨322958183882444045996375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 861221823686517455990333 322958183882444045996375)
                ·
                  refine ⟨484437275823666068994563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322958183882444045996375 484437275823666068994563)
                  ·
                    refine ⟨726655913735499103491845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 484437275823666068994563 726655913735499103491845)
                    ·
                      refine ⟨136247983825406081904721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 726655913735499103491845 136247983825406081904721)
                      ·
                        rfl

theorem cell23_265342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_265342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265342 prefixEnd_265342 := by exact prefixLift 265342
  have htrace : WordTrace (prefixWord ++ tailWord_265342) baseStart_265342 baseEnd_265342 := by
    simpa [prefixWord, tailWord_265342, baseEnd_265342] using wordTrace_append hprefix tailTrace_265342
  have hstable : (prefixWord ++ tailWord_265342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265342).length < 2 ^ (prefixWord ++ tailWord_265342).sum := by decide
  have hdescent : baseEnd_265342 < baseStart_265342 := by decide
  rcases family_descends (prefixWord ++ tailWord_265342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265345 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_265345 : Nat := 118140960795 + 265345 * 2 ^ 59
def prefixEnd_265345 : Nat := 4983230072969 + 3 ^ 40 * 265345 * 2
def baseEnd_265345 : Nat := 136249524267369570167207

theorem tailTrace_265345 : CollatzResearch.WordTrace tailWord_265345 prefixEnd_265345 136249524267369570167207 := by
  unfold tailWord_265345
  simp only [CollatzResearch.WordTrace]
  refine ⟨9677927223707857163213489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6451951482471904775475659 9677927223707857163213489)
  ·
    refine ⟨7258445417780892872410117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9677927223707857163213489 7258445417780892872410117)
    ·
      refine ⟨1360958515833917413576897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7258445417780892872410117 1360958515833917413576897)
      ·
        refine ⟨1020718886875438060182673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1360958515833917413576897 1020718886875438060182673)
        ·
          refine ⟨765539165156578545137005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020718886875438060182673 765539165156578545137005)
          ·
            refine ⟨287077186933716954426377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 765539165156578545137005 287077186933716954426377)
            ·
              refine ⟨215307890200287715819783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287077186933716954426377 215307890200287715819783)
              ·
                refine ⟨322961835300431573729675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215307890200287715819783 322961835300431573729675)
                ·
                  refine ⟨484442752950647360594513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322961835300431573729675 484442752950647360594513)
                  ·
                    refine ⟨363332064712985520445885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 484442752950647360594513 363332064712985520445885)
                    ·
                      refine ⟨136249524267369570167207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 363332064712985520445885 136249524267369570167207)
                      ·
                        rfl

theorem cell23_265345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_265345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265345 prefixEnd_265345 := by exact prefixLift 265345
  have htrace : WordTrace (prefixWord ++ tailWord_265345) baseStart_265345 baseEnd_265345 := by
    simpa [prefixWord, tailWord_265345, baseEnd_265345] using wordTrace_append hprefix tailTrace_265345
  have hstable : (prefixWord ++ tailWord_265345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265345).length < 2 ^ (prefixWord ++ tailWord_265345).sum := by decide
  have hdescent : baseEnd_265345 < baseStart_265345 := by decide
  rcases family_descends (prefixWord ++ tailWord_265345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265358 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_265358 : Nat := 118140960795 + 265358 * 2 ^ 59
def prefixEnd_265358 : Nat := 4983230072969 + 3 ^ 40 * 265358 * 2
def baseEnd_265358 : Nat := 136256199515878019304647

theorem tailTrace_265358 : CollatzResearch.WordTrace tailWord_265358 prefixEnd_265358 136256199515878019304647 := by
  unfold tailWord_265358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209800171582595047929591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6452267581773840255624485 1209800171582595047929591)
  ·
    refine ⟨1814700257373892571894387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1209800171582595047929591 1814700257373892571894387)
    ·
      refine ⟨2722050386060838857841581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1814700257373892571894387 2722050386060838857841581)
      ·
        refine ⟨1020768894772814571690593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2722050386060838857841581 1020768894772814571690593)
        ·
          refine ⟨765576671079610928767945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020768894772814571690593 765576671079610928767945)
          ·
            refine ⟨574182503309708196575959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765576671079610928767945 574182503309708196575959)
            ·
              refine ⟨861273754964562294863939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574182503309708196575959 861273754964562294863939)
              ·
                refine ⟨1291910632446843442295909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 861273754964562294863939 1291910632446843442295909)
                ·
                  refine ⟨242233243583783145430483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291910632446843442295909 242233243583783145430483)
                  ·
                    refine ⟨363349865375674718145725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242233243583783145430483 363349865375674718145725)
                    ·
                      refine ⟨136256199515878019304647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 363349865375674718145725 136256199515878019304647)
                      ·
                        rfl

theorem cell23_265358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_265358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265358 prefixEnd_265358 := by exact prefixLift 265358
  have htrace : WordTrace (prefixWord ++ tailWord_265358) baseStart_265358 baseEnd_265358 := by
    simpa [prefixWord, tailWord_265358, baseEnd_265358] using wordTrace_append hprefix tailTrace_265358
  have hstable : (prefixWord ++ tailWord_265358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265358).length < 2 ^ (prefixWord ++ tailWord_265358).sum := by decide
  have hdescent : baseEnd_265358 < baseStart_265358 := by decide
  rcases family_descends (prefixWord ++ tailWord_265358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265375 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 1, 3, 3]
def baseStart_265375 : Nat := 118140960795 + 265375 * 2 ^ 59
def prefixEnd_265375 : Nat := 4983230072969 + 3 ^ 40 * 265375 * 2
def baseEnd_265375 : Nat := 136264928687004452792069

theorem tailTrace_265375 : CollatzResearch.WordTrace tailWord_265375 prefixEnd_265375 136264928687004452792069 := by
  unfold tailWord_265375
  simp only [CollatzResearch.WordTrace]
  refine ⟨9679021413599172286805579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6452680942399448191203719 9679021413599172286805579)
  ·
    refine ⟨14518532120398758430208369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9679021413599172286805579 14518532120398758430208369)
    ·
      refine ⟨10888899090299068822656277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14518532120398758430208369 10888899090299068822656277)
      ·
        refine ⟨510417144857768851062013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10888899090299068822656277 510417144857768851062013)
        ·
          refine ⟨191406429321663319148255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510417144857768851062013 191406429321663319148255)
          ·
            refine ⟨287109643982494978722383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191406429321663319148255 287109643982494978722383)
            ·
              refine ⟨430664465973742468083575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287109643982494978722383 430664465973742468083575)
              ·
                refine ⟨645996698960613702125363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430664465973742468083575 645996698960613702125363)
                ·
                  refine ⟨968995048440920553188045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645996698960613702125363 968995048440920553188045)
                  ·
                    refine ⟨363373143165345207445517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 968995048440920553188045 363373143165345207445517)
                    ·
                      refine ⟨136264928687004452792069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 363373143165345207445517 136264928687004452792069)
                      ·
                        rfl

theorem cell23_265375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_265375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265375 prefixEnd_265375 := by exact prefixLift 265375
  have htrace : WordTrace (prefixWord ++ tailWord_265375) baseStart_265375 baseEnd_265375 := by
    simpa [prefixWord, tailWord_265375, baseEnd_265375] using wordTrace_append hprefix tailTrace_265375
  have hstable : (prefixWord ++ tailWord_265375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265375).length < 2 ^ (prefixWord ++ tailWord_265375).sum := by decide
  have hdescent : baseEnd_265375 < baseStart_265375 := by decide
  rcases family_descends (prefixWord ++ tailWord_265375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265434 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_265434 : Nat := 118140960795 + 265434 * 2 ^ 59
def prefixEnd_265434 : Nat := 4983230072969 + 3 ^ 40 * 265434 * 2
def baseEnd_265434 : Nat := 45431741348539907318099

theorem tailTrace_265434 : CollatzResearch.WordTrace tailWord_265434 prefixEnd_265434 45431741348539907318099 := by
  unfold tailWord_265434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2420293330096356340800839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6454115546923616908802237 2420293330096356340800839)
  ·
    refine ⟨3630439995144534511201259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2420293330096356340800839 3630439995144534511201259)
    ·
      refine ⟨5445659992716801766801889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3630439995144534511201259 5445659992716801766801889)
      ·
        refine ⟨4084244994537601325101417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5445659992716801766801889 4084244994537601325101417)
        ·
          refine ⟨3063183745903200993826063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4084244994537601325101417 3063183745903200993826063)
          ·
            refine ⟨4594775618854801490739095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063183745903200993826063 4594775618854801490739095)
            ·
              refine ⟨6892163428282202236108643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594775618854801490739095 6892163428282202236108643)
              ·
                refine ⟨10338245142423303354162965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6892163428282202236108643 10338245142423303354162965)
                ·
                  refine ⟨484605241051092344726389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10338245142423303354162965 484605241051092344726389)
                  ·
                    refine ⟨45431741348539907318099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 484605241051092344726389 45431741348539907318099)
                    ·
                      rfl

theorem cell23_265434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_265434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265434 prefixEnd_265434 := by exact prefixLift 265434
  have htrace : WordTrace (prefixWord ++ tailWord_265434) baseStart_265434 baseEnd_265434 := by
    simpa [prefixWord, tailWord_265434, baseEnd_265434] using wordTrace_append hprefix tailTrace_265434
  have hstable : (prefixWord ++ tailWord_265434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265434).length < 2 ^ (prefixWord ++ tailWord_265434).sum := by decide
  have hdescent : baseEnd_265434 < baseStart_265434 := by decide
  rcases family_descends (prefixWord ++ tailWord_265434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265451 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 2, 5]
def baseStart_265451 : Nat := 118140960795 + 265451 * 2 ^ 59
def prefixEnd_265451 : Nat := 4983230072969 + 3 ^ 40 * 265451 * 2
def baseEnd_265451 : Nat := 45434651072248718480573

theorem tailTrace_265451 : CollatzResearch.WordTrace tailWord_265451 prefixEnd_265451 45434651072248718480573 := by
  unfold tailWord_265451
  simp only [CollatzResearch.WordTrace]
  refine ⟨9681793361323837266572207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6454528907549224844381471 9681793361323837266572207)
  ·
    refine ⟨14522690041985755899858311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9681793361323837266572207 14522690041985755899858311)
    ·
      refine ⟨21784035062978633849787467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14522690041985755899858311 21784035062978633849787467)
      ·
        refine ⟨32676052594467950774681201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21784035062978633849787467 32676052594467950774681201)
        ·
          refine ⟨24507039445850963081010901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32676052594467950774681201 24507039445850963081010901)
          ·
            refine ⟨574383737012131947211193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 24507039445850963081010901 574383737012131947211193)
            ·
              refine ⟨430787802759098960408395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574383737012131947211193 430787802759098960408395)
              ·
                refine ⟨646181704138648440612593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430787802759098960408395 646181704138648440612593)
                ·
                  refine ⟨484636278103986330459445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646181704138648440612593 484636278103986330459445)
                  ·
                    refine ⟨45434651072248718480573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 484636278103986330459445 45434651072248718480573)
                    ·
                      rfl

theorem cell23_265451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 5].length) (baseStart_265451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265451 prefixEnd_265451 := by exact prefixLift 265451
  have htrace : WordTrace (prefixWord ++ tailWord_265451) baseStart_265451 baseEnd_265451 := by
    simpa [prefixWord, tailWord_265451, baseEnd_265451] using wordTrace_append hprefix tailTrace_265451
  have hstable : (prefixWord ++ tailWord_265451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265451).length < 2 ^ (prefixWord ++ tailWord_265451).sum := by decide
  have hdescent : baseEnd_265451 < baseStart_265451 := by decide
  rcases family_descends (prefixWord ++ tailWord_265451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265471 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 4]
def baseStart_265471 : Nat := 118140960795 + 265471 * 2 ^ 59
def prefixEnd_265471 : Nat := 4983230072969 + 3 ^ 40 * 265471 * 2
def baseEnd_265471 : Nat := 136314222829836077191627

theorem tailTrace_265471 : CollatzResearch.WordTrace tailWord_265471 prefixEnd_265471 136314222829836077191627 := by
  unfold tailWord_265471
  simp only [CollatzResearch.WordTrace]
  refine ⟨9682522821251380682300267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6455015214167587121533511 9682522821251380682300267)
  ·
    refine ⟨14523784231877071023450401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9682522821251380682300267 14523784231877071023450401)
    ·
      refine ⟨10892838173907803267587801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14523784231877071023450401 10892838173907803267587801)
      ·
        refine ⟨8169628630430852450690851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10892838173907803267587801 8169628630430852450690851)
        ·
          refine ⟨12254442945646278676036277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8169628630430852450690851 12254442945646278676036277)
          ·
            refine ⟨1148854026154338625878401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12254442945646278676036277 1148854026154338625878401)
            ·
              refine ⟨861640519615753969408801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1148854026154338625878401 861640519615753969408801)
              ·
                refine ⟨646230389711815477056601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861640519615753969408801 646230389711815477056601)
                ·
                  refine ⟨484672792283861607792451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646230389711815477056601 484672792283861607792451)
                  ·
                    refine ⟨727009188425792411688677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 484672792283861607792451 727009188425792411688677)
                    ·
                      refine ⟨136314222829836077191627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 727009188425792411688677 136314222829836077191627)
                      ·
                        rfl

theorem cell23_265471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_265471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265471 prefixEnd_265471 := by exact prefixLift 265471
  have htrace : WordTrace (prefixWord ++ tailWord_265471) baseStart_265471 baseEnd_265471 := by
    simpa [prefixWord, tailWord_265471, baseEnd_265471] using wordTrace_append hprefix tailTrace_265471
  have hstable : (prefixWord ++ tailWord_265471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265471).length < 2 ^ (prefixWord ++ tailWord_265471).sum := by decide
  have hdescent : baseEnd_265471 < baseStart_265471 := by decide
  rcases family_descends (prefixWord ++ tailWord_265471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265481 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 3, 4]
def baseStart_265481 : Nat := 118140960795 + 265481 * 2 ^ 59
def prefixEnd_265481 : Nat := 4983230072969 + 3 ^ 40 * 265481 * 2
def baseEnd_265481 : Nat := 45439785878793679355527

theorem tailTrace_265481 : CollatzResearch.WordTrace tailWord_265481 prefixEnd_265481 45439785878793679355527 := by
  unfold tailWord_265481
  simp only [CollatzResearch.WordTrace]
  refine ⟨9682887551215152390164297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6455258367476768260109531 9682887551215152390164297)
  ·
    refine ⟨7262165663411364292623223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9682887551215152390164297 7262165663411364292623223)
    ·
      refine ⟨10893248495117046438934835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7262165663411364292623223 10893248495117046438934835)
      ·
        refine ⟨16339872742675569658402253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10893248495117046438934835 16339872742675569658402253)
        ·
          refine ⟨6127452278503338621900845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16339872742675569658402253 6127452278503338621900845)
          ·
            refine ⟨2297794604438751983212817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6127452278503338621900845 2297794604438751983212817)
            ·
              refine ⟨1723345953329063987409613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2297794604438751983212817 1723345953329063987409613)
              ·
                refine ⟨646254732498398995278605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1723345953329063987409613 646254732498398995278605)
                ·
                  refine ⟨242345524686899623229477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646254732498398995278605 242345524686899623229477)
                  ·
                    refine ⟨45439785878793679355527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242345524686899623229477 45439785878793679355527)
                    ·
                      rfl

theorem cell23_265481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 4].length) (baseStart_265481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265481 prefixEnd_265481 := by exact prefixLift 265481
  have htrace : WordTrace (prefixWord ++ tailWord_265481) baseStart_265481 baseEnd_265481 := by
    simpa [prefixWord, tailWord_265481, baseEnd_265481] using wordTrace_append hprefix tailTrace_265481
  have hstable : (prefixWord ++ tailWord_265481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265481).length < 2 ^ (prefixWord ++ tailWord_265481).sum := by decide
  have hdescent : baseEnd_265481 < baseStart_265481 := by decide
  rcases family_descends (prefixWord ++ tailWord_265481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265498 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 3, 4]
def baseStart_265498 : Nat := 118140960795 + 265498 * 2 ^ 59
def prefixEnd_265498 : Nat := 4983230072969 + 3 ^ 40 * 265498 * 2
def baseEnd_265498 : Nat := 45442695602502490518001

theorem tailTrace_265498 : CollatzResearch.WordTrace tailWord_265498 prefixEnd_265498 45442695602502490518001 := by
  unfold tailWord_265498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2420876898038391073383287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6455671728102376195688765 2420876898038391073383287)
  ·
    refine ⟨3631315347057586610074931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2420876898038391073383287 3631315347057586610074931)
    ·
      refine ⟨5446973020586379915112397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631315347057586610074931 5446973020586379915112397)
      ·
        refine ⟨2042614882719892468167149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5446973020586379915112397 2042614882719892468167149)
        ·
          refine ⟨765980581019959675562681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2042614882719892468167149 765980581019959675562681)
          ·
            refine ⟨574485435764969756672011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765980581019959675562681 574485435764969756672011)
            ·
              refine ⟨861728153647454635008017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574485435764969756672011 861728153647454635008017)
              ·
                refine ⟨646296115235590976256013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861728153647454635008017 646296115235590976256013)
                ·
                  refine ⟨242361043213346616096005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646296115235590976256013 242361043213346616096005)
                  ·
                    refine ⟨45442695602502490518001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242361043213346616096005 45442695602502490518001)
                    ·
                      rfl

theorem cell23_265498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_265498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265498 prefixEnd_265498 := by exact prefixLift 265498
  have htrace : WordTrace (prefixWord ++ tailWord_265498) baseStart_265498 baseEnd_265498 := by
    simpa [prefixWord, tailWord_265498, baseEnd_265498] using wordTrace_append hprefix tailTrace_265498
  have hstable : (prefixWord ++ tailWord_265498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265498).length < 2 ^ (prefixWord ++ tailWord_265498).sum := by decide
  have hdescent : baseEnd_265498 < baseStart_265498 := by decide
  rcases family_descends (prefixWord ++ tailWord_265498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265502 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_265502 : Nat := 118140960795 + 265502 * 2 ^ 59
def prefixEnd_265502 : Nat := 4983230072969 + 3 ^ 40 * 265502 * 2
def baseEnd_265502 : Nat := 45443380243375151967995

theorem tailTrace_265502 : CollatzResearch.WordTrace tailWord_265502 prefixEnd_265502 45443380243375151967995 := by
  unfold tailWord_265502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1210456685517384122084845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6455768989426048651119173 1210456685517384122084845)
  ·
    refine ⟨453921257069019045781817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1210456685517384122084845 453921257069019045781817)
    ·
      refine ⟨340440942801764284336363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453921257069019045781817 340440942801764284336363)
      ·
        refine ⟨510661414202646426504545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340440942801764284336363 510661414202646426504545)
        ·
          refine ⟨382996060651984819878409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510661414202646426504545 382996060651984819878409)
          ·
            refine ⟨287247045488988614908807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382996060651984819878409 287247045488988614908807)
            ·
              refine ⟨430870568233482922363211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287247045488988614908807 430870568233482922363211)
              ·
                refine ⟨646305852350224383544817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430870568233482922363211 646305852350224383544817)
                ·
                  refine ⟨484729389262668287658613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646305852350224383544817 484729389262668287658613)
                  ·
                    refine ⟨45443380243375151967995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 484729389262668287658613 45443380243375151967995)
                    ·
                      rfl

theorem cell23_265502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_265502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265502 prefixEnd_265502 := by exact prefixLift 265502
  have htrace : WordTrace (prefixWord ++ tailWord_265502) baseStart_265502 baseEnd_265502 := by
    simpa [prefixWord, tailWord_265502, baseEnd_265502] using wordTrace_append hprefix tailTrace_265502
  have hstable : (prefixWord ++ tailWord_265502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265502).length < 2 ^ (prefixWord ++ tailWord_265502).sum := by decide
  have hdescent : baseEnd_265502 < baseStart_265502 := by decide
  rcases family_descends (prefixWord ++ tailWord_265502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265548 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 1, 5, 2]
def baseStart_265548 : Nat := 118140960795 + 265548 * 2 ^ 59
def prefixEnd_265548 : Nat := 4983230072969 + 3 ^ 40 * 265548 * 2
def baseEnd_265548 : Nat := 136353760840232275928773

theorem tailTrace_265548 : CollatzResearch.WordTrace tailWord_265548 prefixEnd_265548 136353760840232275928773 := by
  unfold tailWord_265548
  simp only [CollatzResearch.WordTrace]
  refine ⟨4842665620986211416426649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6456887494648281888568865 4842665620986211416426649)
  ·
    refine ⟨3631999215739658562319987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4842665620986211416426649 3631999215739658562319987)
    ·
      refine ⟨5447998823609487843479981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631999215739658562319987 5447998823609487843479981)
      ·
        refine ⟨2042999558853557941304993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5447998823609487843479981 2042999558853557941304993)
        ·
          refine ⟨1532249669140168455978745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2042999558853557941304993 1532249669140168455978745)
          ·
            refine ⟨1149187251855126341984059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1532249669140168455978745 1149187251855126341984059)
            ·
              refine ⟨1723780877782689512976089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149187251855126341984059 1723780877782689512976089)
              ·
                refine ⟨1292835658337017134732067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1723780877782689512976089 1292835658337017134732067)
                ·
                  refine ⟨1939253487505525702098101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292835658337017134732067 1939253487505525702098101)
                  ·
                    refine ⟨181805014453643034571697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1939253487505525702098101 181805014453643034571697)
                    ·
                      refine ⟨136353760840232275928773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 181805014453643034571697 136353760840232275928773)
                      ·
                        rfl

theorem cell23_265548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_265548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265548 prefixEnd_265548 := by exact prefixLift 265548
  have htrace : WordTrace (prefixWord ++ tailWord_265548) baseStart_265548 baseEnd_265548 := by
    simpa [prefixWord, tailWord_265548, baseEnd_265548] using wordTrace_append hprefix tailTrace_265548
  have hstable : (prefixWord ++ tailWord_265548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265548).length < 2 ^ (prefixWord ++ tailWord_265548).sum := by decide
  have hdescent : baseEnd_265548 < baseStart_265548 := by decide
  rcases family_descends (prefixWord ++ tailWord_265548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265561 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 4]
def baseStart_265561 : Nat := 118140960795 + 265561 * 2 ^ 59
def prefixEnd_265561 : Nat := 4983230072969 + 3 ^ 40 * 265561 * 2
def baseEnd_265561 : Nat := 136360436088740725066213

theorem tailTrace_265561 : CollatzResearch.WordTrace tailWord_265561 prefixEnd_265561 136360436088740725066213 := by
  unfold tailWord_265561
  simp only [CollatzResearch.WordTrace]
  refine ⟨9685805390925326053076537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6457203593950217368717691 9685805390925326053076537)
  ·
    refine ⟨7264354043193994539807403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9685805390925326053076537 7264354043193994539807403)
    ·
      refine ⟨10896531064790991809711105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7264354043193994539807403 10896531064790991809711105)
      ·
        refine ⟨8172398298593243857283329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10896531064790991809711105 8172398298593243857283329)
        ·
          refine ⟨6129298723944932892962497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8172398298593243857283329 6129298723944932892962497)
          ·
            refine ⟨4596974042958699669721873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6129298723944932892962497 4596974042958699669721873)
            ·
              refine ⟨3447730532219024752291405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4596974042958699669721873 3447730532219024752291405)
              ·
                refine ⟨1292898949582134282109277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3447730532219024752291405 1292898949582134282109277)
                ·
                  refine ⟨484837106093300355790979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1292898949582134282109277 484837106093300355790979)
                  ·
                    refine ⟨727255659139950533686469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 484837106093300355790979 727255659139950533686469)
                    ·
                      refine ⟨136360436088740725066213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 727255659139950533686469 136360436088740725066213)
                      ·
                        rfl

theorem cell23_265561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_265561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265561 prefixEnd_265561 := by exact prefixLift 265561
  have htrace : WordTrace (prefixWord ++ tailWord_265561) baseStart_265561 baseEnd_265561 := by
    simpa [prefixWord, tailWord_265561, baseEnd_265561] using wordTrace_append hprefix tailTrace_265561
  have hstable : (prefixWord ++ tailWord_265561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265561).length < 2 ^ (prefixWord ++ tailWord_265561).sum := by decide
  have hdescent : baseEnd_265561 < baseStart_265561 := by decide
  rcases family_descends (prefixWord ++ tailWord_265561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265572 : List Nat := [2, 3, 1, 1, 3, 2, 3, 3, 1, 1, 3]
def baseStart_265572 : Nat := 118140960795 + 265572 * 2 ^ 59
def prefixEnd_265572 : Nat := 4983230072969 + 3 ^ 40 * 265572 * 2
def baseEnd_265572 : Nat := 136366084375940182028663

theorem tailTrace_265572 : CollatzResearch.WordTrace tailWord_265572 prefixEnd_265572 136366084375940182028663 := by
  unfold tailWord_265572
  simp only [CollatzResearch.WordTrace]
  refine ⟨4843103296942737465863485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6457471062590316621151313 4843103296942737465863485)
  ·
    refine ⟨1816163736353526549698807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4843103296942737465863485 1816163736353526549698807)
    ·
      refine ⟨2724245604530289824548211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1816163736353526549698807 2724245604530289824548211)
      ·
        refine ⟨4086368406795434736822317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2724245604530289824548211 4086368406795434736822317)
        ·
          refine ⟨1532388152548288026308369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4086368406795434736822317 1532388152548288026308369)
          ·
            refine ⟨1149291114411216019731277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1532388152548288026308369 1149291114411216019731277)
            ·
              refine ⟨430984167904206007399229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1149291114411216019731277 430984167904206007399229)
              ·
                refine ⟨161619062964077252774711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430984167904206007399229 161619062964077252774711)
                ·
                  refine ⟨242428594446115879162067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161619062964077252774711 242428594446115879162067)
                  ·
                    refine ⟨363642891669173818743101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242428594446115879162067 363642891669173818743101)
                    ·
                      refine ⟨136366084375940182028663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 363642891669173818743101 136366084375940182028663)
                      ·
                        rfl

theorem cell23_265572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_265572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265572 prefixEnd_265572 := by exact prefixLift 265572
  have htrace : WordTrace (prefixWord ++ tailWord_265572) baseStart_265572 baseEnd_265572 := by
    simpa [prefixWord, tailWord_265572, baseEnd_265572] using wordTrace_append hprefix tailTrace_265572
  have hstable : (prefixWord ++ tailWord_265572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265572).length < 2 ^ (prefixWord ++ tailWord_265572).sum := by decide
  have hdescent : baseEnd_265572 < baseStart_265572 := by decide
  rcases family_descends (prefixWord ++ tailWord_265572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265589 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_265589 : Nat := 118140960795 + 265589 * 2 ^ 59
def prefixEnd_265589 : Nat := 4983230072969 + 3 ^ 40 * 265589 * 2
def baseEnd_265589 : Nat := 136374813547066615516085

theorem tailTrace_265589 : CollatzResearch.WordTrace tailWord_265589 prefixEnd_265589 136374813547066615516085 := by
  unfold tailWord_265589
  simp only [CollatzResearch.WordTrace]
  refine ⟨9686826634823886835095821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6457884423215924556730547 9686826634823886835095821)
  ·
    refine ⟨3632559988058957563160933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9686826634823886835095821 3632559988058957563160933)
    ·
      refine ⟨681104997761054543092675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3632559988058957563160933 681104997761054543092675)
      ·
        refine ⟨1021657496641581814639013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681104997761054543092675 1021657496641581814639013)
        ·
          refine ⟨191560780620296590244815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1021657496641581814639013 191560780620296590244815)
          ·
            refine ⟨287341170930444885367223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191560780620296590244815 287341170930444885367223)
            ·
              refine ⟨431011756395667328050835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287341170930444885367223 431011756395667328050835)
              ·
                refine ⟨646517634593500992076253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431011756395667328050835 646517634593500992076253)
                ·
                  refine ⟨242444112972562872028595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 646517634593500992076253 242444112972562872028595)
                  ·
                    refine ⟨363666169458844308042893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242444112972562872028595 363666169458844308042893)
                    ·
                      refine ⟨136374813547066615516085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 363666169458844308042893 136374813547066615516085)
                      ·
                        rfl

theorem cell23_265589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_265589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265589 prefixEnd_265589 := by exact prefixLift 265589
  have htrace : WordTrace (prefixWord ++ tailWord_265589) baseStart_265589 baseEnd_265589 := by
    simpa [prefixWord, tailWord_265589, baseEnd_265589] using wordTrace_append hprefix tailTrace_265589
  have hstable : (prefixWord ++ tailWord_265589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265589).length < 2 ^ (prefixWord ++ tailWord_265589).sum := by decide
  have hdescent : baseEnd_265589 < baseStart_265589 := by decide
  rcases family_descends (prefixWord ++ tailWord_265589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265605 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 2, 4]
def baseStart_265605 : Nat := 118140960795 + 265605 * 2 ^ 59
def prefixEnd_265605 : Nat := 4983230072969 + 3 ^ 40 * 265605 * 2
def baseEnd_265605 : Nat := 45461009745846184305337

theorem tailTrace_265605 : CollatzResearch.WordTrace tailWord_265605 prefixEnd_265605 45461009745846184305337 := by
  unfold tailWord_265605
  simp only [CollatzResearch.WordTrace]
  refine ⟨9687410202765921567678269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6458273468510614378452179 9687410202765921567678269)
  ·
    refine ⟨3632778826037220587879351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9687410202765921567678269 3632778826037220587879351)
    ·
      refine ⟨5449168239055830881819027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3632778826037220587879351 5449168239055830881819027)
      ·
        refine ⟨8173752358583746322728541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5449168239055830881819027 8173752358583746322728541)
        ·
          refine ⟨3065157134468904871023203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8173752358583746322728541 3065157134468904871023203)
          ·
            refine ⟨4597735701703357306534805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065157134468904871023203 4597735701703357306534805)
            ·
              refine ⟨215518861017344873743819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4597735701703357306534805 215518861017344873743819)
              ·
                refine ⟨323278291526017310615729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215518861017344873743819 323278291526017310615729)
                ·
                  refine ⟨242458718644512982961797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323278291526017310615729 242458718644512982961797)
                  ·
                    refine ⟨45461009745846184305337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242458718644512982961797 45461009745846184305337)
                    ·
                      rfl

theorem cell23_265605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_265605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265605 prefixEnd_265605 := by exact prefixLift 265605
  have htrace : WordTrace (prefixWord ++ tailWord_265605) baseStart_265605 baseEnd_265605 := by
    simpa [prefixWord, tailWord_265605, baseEnd_265605] using wordTrace_append hprefix tailTrace_265605
  have hstable : (prefixWord ++ tailWord_265605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265605).length < 2 ^ (prefixWord ++ tailWord_265605).sum := by decide
  have hdescent : baseEnd_265605 < baseStart_265605 := by decide
  rcases family_descends (prefixWord ++ tailWord_265605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265685 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 1, 4, 2]
def baseStart_265685 : Nat := 118140960795 + 265685 * 2 ^ 59
def prefixEnd_265685 : Nat := 4983230072969 + 3 ^ 40 * 265685 * 2
def baseEnd_265685 : Nat := 136424107689898239915643

theorem tailTrace_265685 : CollatzResearch.WordTrace tailWord_265685 prefixEnd_265685 136424107689898239915643 := by
  unfold tailWord_265685
  simp only [CollatzResearch.WordTrace]
  refine ⟨9690328042476095230590509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6460218694984063487060339 9690328042476095230590509)
  ·
    refine ⟨3633873015928535711471441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9690328042476095230590509 3633873015928535711471441)
    ·
      refine ⟨2725404761946401783603581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3633873015928535711471441 2725404761946401783603581)
      ·
        refine ⟨1022026785729900668851343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2725404761946401783603581 1022026785729900668851343)
        ·
          refine ⟨1533040178594851003277015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022026785729900668851343 1533040178594851003277015)
          ·
            refine ⟨2299560267892276504915523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533040178594851003277015 2299560267892276504915523)
            ·
              refine ⟨3449340401838414757373285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2299560267892276504915523 3449340401838414757373285)
              ·
                refine ⟨646751325344702767007491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3449340401838414757373285 646751325344702767007491)
                ·
                  refine ⟨970126988017054150511237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646751325344702767007491 970126988017054150511237)
                  ·
                    refine ⟨181898810253197653220857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 970126988017054150511237 181898810253197653220857)
                    ·
                      refine ⟨136424107689898239915643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 181898810253197653220857 136424107689898239915643)
                      ·
                        rfl

theorem cell23_265685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_265685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265685 prefixEnd_265685 := by exact prefixLift 265685
  have htrace : WordTrace (prefixWord ++ tailWord_265685) baseStart_265685 baseEnd_265685 := by
    simpa [prefixWord, tailWord_265685, baseEnd_265685] using wordTrace_append hprefix tailTrace_265685
  have hstable : (prefixWord ++ tailWord_265685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265685).length < 2 ^ (prefixWord ++ tailWord_265685).sum := by decide
  have hdescent : baseEnd_265685 < baseStart_265685 := by decide
  rcases family_descends (prefixWord ++ tailWord_265685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265689 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 1, 3, 2]
def baseStart_265689 : Nat := 118140960795 + 265689 * 2 ^ 59
def prefixEnd_265689 : Nat := 4983230072969 + 3 ^ 40 * 265689 * 2
def baseEnd_265689 : Nat := 136426161612516224265625

theorem tailTrace_265689 : CollatzResearch.WordTrace tailWord_265689 prefixEnd_265689 136426161612516224265625 := by
  unfold tailWord_265689
  simp only [CollatzResearch.WordTrace]
  refine ⟨9690473934461603913736121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6460315956307735942490747 9690473934461603913736121)
  ·
    refine ⟨7267855450846202935302091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9690473934461603913736121 7267855450846202935302091)
    ·
      refine ⟨10901783176269304402953137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7267855450846202935302091 10901783176269304402953137)
      ·
        refine ⟨8176337382201978302214853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10901783176269304402953137 8176337382201978302214853)
        ·
          refine ⟨1533063259162870931665285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8176337382201978302214853 1533063259162870931665285)
          ·
            refine ⟨287449361093038299687241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1533063259162870931665285 287449361093038299687241)
            ·
              refine ⟨215587020819778724765431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287449361093038299687241 215587020819778724765431)
              ·
                refine ⟨323380531229668087148147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215587020819778724765431 323380531229668087148147)
                ·
                  refine ⟨485070796844502130722221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323380531229668087148147 485070796844502130722221)
                  ·
                    refine ⟨181901548816688299020833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 485070796844502130722221 181901548816688299020833)
                    ·
                      refine ⟨136426161612516224265625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 181901548816688299020833 136426161612516224265625)
                      ·
                        rfl

theorem cell23_265689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 3, 2].length) (baseStart_265689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265689 prefixEnd_265689 := by exact prefixLift 265689
  have htrace : WordTrace (prefixWord ++ tailWord_265689) baseStart_265689 baseEnd_265689 := by
    simpa [prefixWord, tailWord_265689, baseEnd_265689] using wordTrace_append hprefix tailTrace_265689
  have hstable : (prefixWord ++ tailWord_265689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265689).length < 2 ^ (prefixWord ++ tailWord_265689).sum := by decide
  have hdescent : baseEnd_265689 < baseStart_265689 := by decide
  rcases family_descends (prefixWord ++ tailWord_265689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265731 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 7]
def baseStart_265731 : Nat := 118140960795 + 265731 * 2 ^ 59
def prefixEnd_265731 : Nat := 4983230072969 + 3 ^ 40 * 265731 * 2
def baseEnd_265731 : Nat := 136447727800005059940431

theorem tailTrace_265731 : CollatzResearch.WordTrace tailWord_265731 prefixEnd_265731 136447727800005059940431 := by
  unfold tailWord_265731
  simp only [CollatzResearch.WordTrace]
  refine ⟨9692005800309445086765047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6461337200206296724510031 9692005800309445086765047)
  ·
    refine ⟨14538008700464167630147571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9692005800309445086765047 14538008700464167630147571)
    ·
      refine ⟨21807013050696251445221357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14538008700464167630147571 21807013050696251445221357)
      ·
        refine ⟨8177629894011094291958009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21807013050696251445221357 8177629894011094291958009)
        ·
          refine ⟨6133222420508320718968507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8177629894011094291958009 6133222420508320718968507)
          ·
            refine ⟨9199833630762481078452761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6133222420508320718968507 9199833630762481078452761)
            ·
              refine ⟨6899875223071860808839571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9199833630762481078452761 6899875223071860808839571)
              ·
                refine ⟨10349812834607791213259357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6899875223071860808839571 10349812834607791213259357)
                ·
                  refine ⟨3881179812977921704972259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10349812834607791213259357 3881179812977921704972259)
                  ·
                    refine ⟨5821769719466882557458389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3881179812977921704972259 5821769719466882557458389)
                    ·
                      refine ⟨136447727800005059940431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5821769719466882557458389 136447727800005059940431)
                      ·
                        rfl

theorem cell23_265731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_265731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265731 prefixEnd_265731 := by exact prefixLift 265731
  have htrace : WordTrace (prefixWord ++ tailWord_265731) baseStart_265731 baseEnd_265731 := by
    simpa [prefixWord, tailWord_265731, baseEnd_265731] using wordTrace_append hprefix tailTrace_265731
  have hstable : (prefixWord ++ tailWord_265731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265731).length < 2 ^ (prefixWord ++ tailWord_265731).sum := by decide
  have hdescent : baseEnd_265731 < baseStart_265731 := by decide
  rcases family_descends (prefixWord ++ tailWord_265731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265738 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_265738 : Nat := 118140960795 + 265738 * 2 ^ 59
def prefixEnd_265738 : Nat := 4983230072969 + 3 ^ 40 * 265738 * 2
def baseEnd_265738 : Nat := 45483774054862177517633

theorem tailTrace_265738 : CollatzResearch.WordTrace tailWord_265738 prefixEnd_265738 45483774054862177517633 := by
  unfold tailWord_265738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423065277821021320567467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6461507407522723521513245 2423065277821021320567467)
  ·
    refine ⟨3634597916731531980851201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2423065277821021320567467 3634597916731531980851201)
    ·
      refine ⟨2725948437548648985638401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3634597916731531980851201 2725948437548648985638401)
      ·
        refine ⟨2044461328161486739228801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2725948437548648985638401 2044461328161486739228801)
        ·
          refine ⟨1533345996121115054421601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2044461328161486739228801 1533345996121115054421601)
          ·
            refine ⟨1150009497090836290816201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1533345996121115054421601 1150009497090836290816201)
            ·
              refine ⟨862507122818127218112151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150009497090836290816201 862507122818127218112151)
              ·
                refine ⟨1293760684227190827168227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862507122818127218112151 1293760684227190827168227)
                ·
                  refine ⟨1940641026340786240752341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293760684227190827168227 1940641026340786240752341)
                  ·
                    refine ⟨45483774054862177517633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1940641026340786240752341 45483774054862177517633)
                    ·
                      rfl

theorem cell23_265738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_265738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265738 prefixEnd_265738 := by exact prefixLift 265738
  have htrace : WordTrace (prefixWord ++ tailWord_265738) baseStart_265738 baseEnd_265738 := by
    simpa [prefixWord, tailWord_265738, baseEnd_265738] using wordTrace_append hprefix tailTrace_265738
  have hstable : (prefixWord ++ tailWord_265738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265738).length < 2 ^ (prefixWord ++ tailWord_265738).sum := by decide
  have hdescent : baseEnd_265738 < baseStart_265738 := by decide
  rcases family_descends (prefixWord ++ tailWord_265738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265802 : List Nat := [3, 1, 2, 1, 1, 3, 2, 5, 1, 4]
def baseStart_265802 : Nat := 118140960795 + 265802 * 2 ^ 59
def prefixEnd_265802 : Nat := 4983230072969 + 3 ^ 40 * 265802 * 2
def baseEnd_265802 : Nat := 45494728308824760717535

theorem tailTrace_265802 : CollatzResearch.WordTrace tailWord_265802 prefixEnd_265802 45494728308824760717535 := by
  unfold tailWord_265802
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423648845763056053149915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6463063588701482808399773 2423648845763056053149915)
  ·
    refine ⟨3635473268644584079724873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2423648845763056053149915 3635473268644584079724873)
    ·
      refine ⟨2726604951483438059793655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3635473268644584079724873 2726604951483438059793655)
      ·
        refine ⟨4089907427225157089690483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2726604951483438059793655 4089907427225157089690483)
        ·
          refine ⟨6134861140837735634535725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4089907427225157089690483 6134861140837735634535725)
          ·
            refine ⟨2300572927814150862950897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6134861140837735634535725 2300572927814150862950897)
            ·
              refine ⟨1725429695860613147213173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2300572927814150862950897 1725429695860613147213173)
              ·
                refine ⟨161759033986932482551235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1725429695860613147213173 161759033986932482551235)
                ·
                  refine ⟨242638550980398723826853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161759033986932482551235 242638550980398723826853)
                  ·
                    refine ⟨45494728308824760717535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242638550980398723826853 45494728308824760717535)
                    ·
                      rfl

theorem cell23_265802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_265802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265802 prefixEnd_265802 := by exact prefixLift 265802
  have htrace : WordTrace (prefixWord ++ tailWord_265802) baseStart_265802 baseEnd_265802 := by
    simpa [prefixWord, tailWord_265802, baseEnd_265802] using wordTrace_append hprefix tailTrace_265802
  have hstable : (prefixWord ++ tailWord_265802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265802).length < 2 ^ (prefixWord ++ tailWord_265802).sum := by decide
  have hdescent : baseEnd_265802 < baseStart_265802 := by decide
  rcases family_descends (prefixWord ++ tailWord_265802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265815 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 6]
def baseStart_265815 : Nat := 118140960795 + 265815 * 2 ^ 59
def prefixEnd_265815 : Nat := 4983230072969 + 3 ^ 40 * 265815 * 2
def baseEnd_265815 : Nat := 15165651130553636810005

theorem tailTrace_265815 : CollatzResearch.WordTrace tailWord_265815 prefixEnd_265815 15165651130553636810005 := by
  unfold tailWord_265815
  simp only [CollatzResearch.WordTrace]
  refine ⟨9695069532005127432822899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6463379688003418288548599 9695069532005127432822899)
  ·
    refine ⟨14542604298007691149234349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9695069532005127432822899 14542604298007691149234349)
    ·
      refine ⟨5453476611752884180962881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14542604298007691149234349 5453476611752884180962881)
      ·
        refine ⟨4090107458814663135722161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5453476611752884180962881 4090107458814663135722161)
        ·
          refine ⟨3067580594110997351791621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4090107458814663135722161 3067580594110997351791621)
          ·
            refine ⟨575171361395812003460929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3067580594110997351791621 575171361395812003460929)
            ·
              refine ⟨431378521046859002595697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575171361395812003460929 431378521046859002595697)
              ·
                refine ⟨323533890785144251946773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431378521046859002595697 323533890785144251946773)
                ·
                  refine ⟨15165651130553636810005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 323533890785144251946773 15165651130553636810005)
                  ·
                    rfl

theorem cell23_265815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 6].length) (baseStart_265815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265815 prefixEnd_265815 := by exact prefixLift 265815
  have htrace : WordTrace (prefixWord ++ tailWord_265815) baseStart_265815 baseEnd_265815 := by
    simpa [prefixWord, tailWord_265815, baseEnd_265815] using wordTrace_append hprefix tailTrace_265815
  have hstable : (prefixWord ++ tailWord_265815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265815).length < 2 ^ (prefixWord ++ tailWord_265815).sum := by decide
  have hdescent : baseEnd_265815 < baseStart_265815 := by decide
  rcases family_descends (prefixWord ++ tailWord_265815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265842 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_265842 : Nat := 118140960795 + 265842 * 2 ^ 59
def prefixEnd_265842 : Nat := 4983230072969 + 3 ^ 40 * 265842 * 2
def baseEnd_265842 : Nat := 136504724152654125652421

theorem tailTrace_265842 : CollatzResearch.WordTrace tailWord_265842 prefixEnd_265842 136504724152654125652421 := by
  unfold tailWord_265842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2424013575726827761013945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6464036201938207362703853 2424013575726827761013945)
  ·
    refine ⟨1818010181795120820760459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2424013575726827761013945 1818010181795120820760459)
    ·
      refine ⟨2727015272692681231140689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818010181795120820760459 2727015272692681231140689)
      ·
        refine ⟨2045261454519510923355517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2727015272692681231140689 2045261454519510923355517)
        ·
          refine ⟨766973045444816596258319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2045261454519510923355517 766973045444816596258319)
          ·
            refine ⟨1150459568167224894387479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766973045444816596258319 1150459568167224894387479)
            ·
              refine ⟨1725689352250837341581219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150459568167224894387479 1725689352250837341581219)
              ·
                refine ⟨2588534028376256012371829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1725689352250837341581219 2588534028376256012371829)
                ·
                  refine ⟨242675065160274001159859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2588534028376256012371829 242675065160274001159859)
                  ·
                    refine ⟨364012597740411001739789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242675065160274001159859 364012597740411001739789)
                    ·
                      refine ⟨136504724152654125652421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 364012597740411001739789 136504724152654125652421)
                      ·
                        rfl

theorem cell23_265842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_265842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265842 prefixEnd_265842 := by exact prefixLift 265842
  have htrace : WordTrace (prefixWord ++ tailWord_265842) baseStart_265842 baseEnd_265842 := by
    simpa [prefixWord, tailWord_265842, baseEnd_265842] using wordTrace_append hprefix tailTrace_265842
  have hstable : (prefixWord ++ tailWord_265842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265842).length < 2 ^ (prefixWord ++ tailWord_265842).sum := by decide
  have hdescent : baseEnd_265842 < baseStart_265842 := by decide
  rcases family_descends (prefixWord ++ tailWord_265842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265876 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_265876 : Nat := 118140960795 + 265876 * 2 ^ 59
def prefixEnd_265876 : Nat := 4983230072969 + 3 ^ 40 * 265876 * 2
def baseEnd_265876 : Nat := 136522182494906992627265

theorem tailTrace_265876 : CollatzResearch.WordTrace tailWord_265876 prefixEnd_265876 136522182494906992627265 := by
  unfold tailWord_265876
  simp only [CollatzResearch.WordTrace]
  refine ⟨4848647192392067425396741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6464862923189423233862321 4848647192392067425396741)
  ·
    refine ⟨909121348573512642261889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4848647192392067425396741 909121348573512642261889)
    ·
      refine ⟨681841011430134481696417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 909121348573512642261889 681841011430134481696417)
      ·
        refine ⟨511380758572600861272313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681841011430134481696417 511380758572600861272313)
        ·
          refine ⟨383535568929450645954235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511380758572600861272313 383535568929450645954235)
          ·
            refine ⟨575303353394175968931353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383535568929450645954235 575303353394175968931353)
            ·
              refine ⟨431477515045631976698515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575303353394175968931353 431477515045631976698515)
              ·
                refine ⟨647216272568447965047773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431477515045631976698515 647216272568447965047773)
                ·
                  refine ⟨242706102213167986892915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647216272568447965047773 242706102213167986892915)
                  ·
                    refine ⟨364059153319751980339373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242706102213167986892915 364059153319751980339373)
                    ·
                      refine ⟨136522182494906992627265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 364059153319751980339373 136522182494906992627265)
                      ·
                        rfl

theorem cell23_265876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_265876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265876 prefixEnd_265876 := by exact prefixLift 265876
  have htrace : WordTrace (prefixWord ++ tailWord_265876) baseStart_265876 baseEnd_265876 := by
    simpa [prefixWord, tailWord_265876, baseEnd_265876] using wordTrace_append hprefix tailTrace_265876
  have hstable : (prefixWord ++ tailWord_265876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265876).length < 2 ^ (prefixWord ++ tailWord_265876).sum := by decide
  have hdescent : baseEnd_265876 < baseStart_265876 := by decide
  rcases family_descends (prefixWord ++ tailWord_265876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265892 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_265892 : Nat := 118140960795 + 265892 * 2 ^ 59
def prefixEnd_265892 : Nat := 4983230072969 + 3 ^ 40 * 265892 * 2
def baseEnd_265892 : Nat := 45510132728459643342397

theorem tailTrace_265892 : CollatzResearch.WordTrace tailWord_265892 prefixEnd_265892 45510132728459643342397 := by
  unfold tailWord_265892
  simp only [CollatzResearch.WordTrace]
  refine ⟨4848938976363084791687965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6465251968484113055583953 4848938976363084791687965)
  ·
    refine ⟨1818352116136156796882987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4848938976363084791687965 1818352116136156796882987)
    ·
      refine ⟨2727528174204235195324481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818352116136156796882987 2727528174204235195324481)
      ·
        refine ⟨2045646130653176396493361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2727528174204235195324481 2045646130653176396493361)
        ·
          refine ⟨1534234597989882297370021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2045646130653176396493361 1534234597989882297370021)
          ·
            refine ⟨287668987123102930756879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1534234597989882297370021 287668987123102930756879)
            ·
              refine ⟨431503480684654396135319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287668987123102930756879 431503480684654396135319)
              ·
                refine ⟨647255221026981594202979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431503480684654396135319 647255221026981594202979)
                ·
                  refine ⟨970882831540472391304469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647255221026981594202979 970882831540472391304469)
                  ·
                    refine ⟨45510132728459643342397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 970882831540472391304469 45510132728459643342397)
                    ·
                      rfl

theorem cell23_265892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_265892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265892 prefixEnd_265892 := by exact prefixLift 265892
  have htrace : WordTrace (prefixWord ++ tailWord_265892) baseStart_265892 baseEnd_265892 := by
    simpa [prefixWord, tailWord_265892, baseEnd_265892] using wordTrace_append hprefix tailTrace_265892
  have hstable : (prefixWord ++ tailWord_265892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265892).length < 2 ^ (prefixWord ++ tailWord_265892).sum := by decide
  have hdescent : baseEnd_265892 < baseStart_265892 := by decide
  rcases family_descends (prefixWord ++ tailWord_265892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265910 : List Nat := [5, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_265910 : Nat := 118140960795 + 265910 * 2 ^ 59
def prefixEnd_265910 : Nat := 4983230072969 + 3 ^ 40 * 265910 * 2
def baseEnd_265910 : Nat := 136539640837159859602109

theorem tailTrace_265910 : CollatzResearch.WordTrace tailWord_265910 prefixEnd_265910 136539640837159859602109 := by
  unfold tailWord_265910
  simp only [CollatzResearch.WordTrace]
  refine ⟨606158404166309916095699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6465689644440639105020789 606158404166309916095699)
  ·
    refine ⟨909237606249464874143549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 606158404166309916095699 909237606249464874143549)
    ·
      refine ⟨340964102343549327803831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 909237606249464874143549 340964102343549327803831)
      ·
        refine ⟨511446153515323991705747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340964102343549327803831 511446153515323991705747)
        ·
          refine ⟨767169230272985987558621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511446153515323991705747 767169230272985987558621)
          ·
            refine ⟨287688461352369745334483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 767169230272985987558621 287688461352369745334483)
            ·
              refine ⟨431532692028554618001725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287688461352369745334483 431532692028554618001725)
              ·
                refine ⟨161824759510707981750647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431532692028554618001725 161824759510707981750647)
                ·
                  refine ⟨242737139266061972625971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161824759510707981750647 242737139266061972625971)
                  ·
                    refine ⟨364105708899092958938957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242737139266061972625971 364105708899092958938957)
                    ·
                      refine ⟨136539640837159859602109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 364105708899092958938957 136539640837159859602109)
                      ·
                        rfl

theorem cell23_265910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_265910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265910 prefixEnd_265910 := by exact prefixLift 265910
  have htrace : WordTrace (prefixWord ++ tailWord_265910) baseStart_265910 baseEnd_265910 := by
    simpa [prefixWord, tailWord_265910, baseEnd_265910] using wordTrace_append hprefix tailTrace_265910
  have hstable : (prefixWord ++ tailWord_265910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265910).length < 2 ^ (prefixWord ++ tailWord_265910).sum := by decide
  have hdescent : baseEnd_265910 < baseStart_265910 := by decide
  rcases family_descends (prefixWord ++ tailWord_265910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265915 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 3]
def baseStart_265915 : Nat := 118140960795 + 265915 * 2 ^ 59
def prefixEnd_265915 : Nat := 4983230072969 + 3 ^ 40 * 265915 * 2
def baseEnd_265915 : Nat := 136542208240432340039585

theorem tailTrace_265915 : CollatzResearch.WordTrace tailWord_265915 prefixEnd_265915 136542208240432340039585 := by
  unfold tailWord_265915
  simp only [CollatzResearch.WordTrace]
  refine ⟨9698716831642844511463199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6465811221095229674308799 9698716831642844511463199)
  ·
    refine ⟨14548075247464266767194799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9698716831642844511463199 14548075247464266767194799)
    ·
      refine ⟨21822112871196400150792199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14548075247464266767194799 21822112871196400150792199)
      ·
        refine ⟨32733169306794600226188299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21822112871196400150792199 32733169306794600226188299)
        ·
          refine ⟨49099753960191900339282449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32733169306794600226188299 49099753960191900339282449)
          ·
            refine ⟨36824815470143925254461837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49099753960191900339282449 36824815470143925254461837)
            ·
              refine ⟨13809305801303971970423189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36824815470143925254461837 13809305801303971970423189)
              ·
                refine ⟨647311209436123686113587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13809305801303971970423189 647311209436123686113587)
                ·
                  refine ⟨970966814154185529170381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647311209436123686113587 970966814154185529170381)
                  ·
                    refine ⟨364112555307819573438893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 970966814154185529170381 364112555307819573438893)
                    ·
                      refine ⟨136542208240432340039585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 364112555307819573438893 136542208240432340039585)
                      ·
                        rfl

theorem cell23_265915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 3].length) (baseStart_265915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265915 prefixEnd_265915 := by exact prefixLift 265915
  have htrace : WordTrace (prefixWord ++ tailWord_265915) baseStart_265915 baseEnd_265915 := by
    simpa [prefixWord, tailWord_265915, baseEnd_265915] using wordTrace_append hprefix tailTrace_265915
  have hstable : (prefixWord ++ tailWord_265915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265915).length < 2 ^ (prefixWord ++ tailWord_265915).sum := by decide
  have hdescent : baseEnd_265915 < baseStart_265915 := by decide
  rcases family_descends (prefixWord ++ tailWord_265915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265926 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_265926 : Nat := 118140960795 + 265926 * 2 ^ 59
def prefixEnd_265926 : Nat := 4983230072969 + 3 ^ 40 * 265926 * 2
def baseEnd_265926 : Nat := 45515952175877265667345

theorem tailTrace_265926 : CollatzResearch.WordTrace tailWord_265926 prefixEnd_265926 45515952175877265667345 := by
  unfold tailWord_265926
  simp only [CollatzResearch.WordTrace]
  refine ⟨303097438581343543441051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6466078689735328926742421 303097438581343543441051)
  ·
    refine ⟨454646157872015315161577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303097438581343543441051 454646157872015315161577)
    ·
      refine ⟨340984618404011486371183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454646157872015315161577 340984618404011486371183)
      ·
        refine ⟨511476927606017229556775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340984618404011486371183 511476927606017229556775)
        ·
          refine ⟨767215391409025844335163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511476927606017229556775 767215391409025844335163)
          ·
            refine ⟨1150823087113538766502745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767215391409025844335163 1150823087113538766502745)
            ·
              refine ⟨863117315335154074877059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150823087113538766502745 863117315335154074877059)
              ·
                refine ⟨1294675973002731112315589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863117315335154074877059 1294675973002731112315589)
                ·
                  refine ⟨242751744938012083559173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1294675973002731112315589 242751744938012083559173)
                  ·
                    refine ⟨45515952175877265667345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242751744938012083559173 45515952175877265667345)
                    ·
                      rfl

theorem cell23_265926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_265926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265926 prefixEnd_265926 := by exact prefixLift 265926
  have htrace : WordTrace (prefixWord ++ tailWord_265926) baseStart_265926 baseEnd_265926 := by
    simpa [prefixWord, tailWord_265926, baseEnd_265926] using wordTrace_append hprefix tailTrace_265926
  have hstable : (prefixWord ++ tailWord_265926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265926).length < 2 ^ (prefixWord ++ tailWord_265926).sum := by decide
  have hdescent : baseEnd_265926 < baseStart_265926 := by decide
  rcases family_descends (prefixWord ++ tailWord_265926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265933 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_265933 : Nat := 118140960795 + 265933 * 2 ^ 59
def prefixEnd_265933 : Nat := 4983230072969 + 3 ^ 40 * 265933 * 2
def baseEnd_265933 : Nat := 136551450892213269614503

theorem tailTrace_265933 : CollatzResearch.WordTrace tailWord_265933 prefixEnd_265933 136551450892213269614503 := by
  unfold tailWord_265933
  simp only [CollatzResearch.WordTrace]
  refine ⟨9699373345577633585618453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6466248897051755723745635 9699373345577633585618453)
  ·
    refine ⟨454658125573951574325865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9699373345577633585618453 454658125573951574325865)
    ·
      refine ⟨340993594180463680744399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454658125573951574325865 340993594180463680744399)
      ·
        refine ⟨511490391270695521116599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340993594180463680744399 511490391270695521116599)
        ·
          refine ⟨767235586906043281674899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511490391270695521116599 767235586906043281674899)
          ·
            refine ⟨1150853380359064922512349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767235586906043281674899 1150853380359064922512349)
            ·
              refine ⟨431570017634649345942131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1150853380359064922512349 431570017634649345942131)
              ·
                refine ⟨647355026451974018913197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431570017634649345942131 647355026451974018913197)
                ·
                  refine ⟨242758134919490257092449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647355026451974018913197 242758134919490257092449)
                  ·
                    refine ⟨182068601189617692819337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 242758134919490257092449 182068601189617692819337)
                    ·
                      refine ⟨136551450892213269614503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182068601189617692819337 136551450892213269614503)
                      ·
                        rfl

theorem cell23_265933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_265933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265933 prefixEnd_265933 := by exact prefixLift 265933
  have htrace : WordTrace (prefixWord ++ tailWord_265933) baseStart_265933 baseEnd_265933 := by
    simpa [prefixWord, tailWord_265933, baseEnd_265933] using wordTrace_append hprefix tailTrace_265933
  have hstable : (prefixWord ++ tailWord_265933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265933).length < 2 ^ (prefixWord ++ tailWord_265933).sum := by decide
  have hdescent : baseEnd_265933 < baseStart_265933 := by decide
  rcases family_descends (prefixWord ++ tailWord_265933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265975 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_265975 : Nat := 118140960795 + 265975 * 2 ^ 59
def prefixEnd_265975 : Nat := 4983230072969 + 3 ^ 40 * 265975 * 2
def baseEnd_265975 : Nat := 136573017079702105289309

theorem tailTrace_265975 : CollatzResearch.WordTrace tailWord_265975 prefixEnd_265975 136573017079702105289309 := by
  unfold tailWord_265975
  simp only [CollatzResearch.WordTrace]
  refine ⟨9700905211425474758647379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6467270140950316505764919 9700905211425474758647379)
  ·
    refine ⟨14551357817138212137971069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9700905211425474758647379 14551357817138212137971069)
    ·
      refine ⟨5456759181426829551739151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14551357817138212137971069 5456759181426829551739151)
      ·
        refine ⟨8185138772140244327608727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5456759181426829551739151 8185138772140244327608727)
        ·
          refine ⟨12277708158210366491413091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8185138772140244327608727 12277708158210366491413091)
          ·
            refine ⟨18416562237315549737119637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12277708158210366491413091 18416562237315549737119637)
            ·
              refine ⟨863276354874166393927483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18416562237315549737119637 863276354874166393927483)
              ·
                refine ⟨1294914532311249590891225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863276354874166393927483 1294914532311249590891225)
                ·
                  refine ⟨971185899233437193168419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1294914532311249590891225 971185899233437193168419)
                  ·
                    refine ⟨1456778848850155789752629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 971185899233437193168419 1456778848850155789752629)
                    ·
                      refine ⟨136573017079702105289309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1456778848850155789752629 136573017079702105289309)
                      ·
                        rfl

theorem cell23_265975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_265975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265975 prefixEnd_265975 := by exact prefixLift 265975
  have htrace : WordTrace (prefixWord ++ tailWord_265975) baseStart_265975 baseEnd_265975 := by
    simpa [prefixWord, tailWord_265975, baseEnd_265975] using wordTrace_append hprefix tailTrace_265975
  have hstable : (prefixWord ++ tailWord_265975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265975).length < 2 ^ (prefixWord ++ tailWord_265975).sum := by decide
  have hdescent : baseEnd_265975 < baseStart_265975 := by decide
  rcases family_descends (prefixWord ++ tailWord_265975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265990 : List Nat := [6, 2, 2, 1, 1, 2, 1, 8]
def baseStart_265990 : Nat := 118140960795 + 265990 * 2 ^ 59
def prefixEnd_265990 : Nat := 4983230072969 + 3 ^ 40 * 265990 * 2
def baseEnd_265990 : Nat := 5058545158871094318583

theorem tailTrace_265990 : CollatzResearch.WordTrace tailWord_265990 prefixEnd_265990 5058545158871094318583 := by
  unfold tailWord_265990
  simp only [CollatzResearch.WordTrace]
  refine ⟨303170384574097885013857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6467634870914088213628949 303170384574097885013857)
  ·
    refine ⟨227377788430573413760393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303170384574097885013857 227377788430573413760393)
    ·
      refine ⟨170533341322930060320295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227377788430573413760393 170533341322930060320295)
      ·
        refine ⟨255800011984395090480443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170533341322930060320295 255800011984395090480443)
        ·
          refine ⟨383700017976592635720665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255800011984395090480443 383700017976592635720665)
          ·
            refine ⟨287775013482444476790499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383700017976592635720665 287775013482444476790499)
            ·
              refine ⟨431662520223666715185749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287775013482444476790499 431662520223666715185749)
              ·
                refine ⟨5058545158871094318583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 431662520223666715185749 5058545158871094318583)
                ·
                  rfl

theorem cell23_265990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_265990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_265990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_265990 prefixEnd_265990 := by exact prefixLift 265990
  have htrace : WordTrace (prefixWord ++ tailWord_265990) baseStart_265990 baseEnd_265990 := by
    simpa [prefixWord, tailWord_265990, baseEnd_265990] using wordTrace_append hprefix tailTrace_265990
  have hstable : (prefixWord ++ tailWord_265990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265990).length < 2 ^ (prefixWord ++ tailWord_265990).sum := by decide
  have hdescent : baseEnd_265990 < baseStart_265990 := by decide
  rcases family_descends (prefixWord ++ tailWord_265990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266119 : List Nat := [1, 1, 4, 2, 4, 1, 1, 3, 6]
def baseStart_266119 : Nat := 118140960795 + 266119 * 2 ^ 59
def prefixEnd_266119 : Nat := 4983230072969 + 3 ^ 40 * 266119 * 2
def baseEnd_266119 : Nat := 15182995365994393543183

theorem tailTrace_266119 : CollatzResearch.WordTrace tailWord_266119 prefixEnd_266119 15182995365994393543183 := by
  unfold tailWord_266119
  simp only [CollatzResearch.WordTrace]
  refine ⟨9706157322903787351889411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6470771548602524901259607 9706157322903787351889411)
  ·
    refine ⟨14559235984355681027834117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9706157322903787351889411 14559235984355681027834117)
    ·
      refine ⟨2729856747066690192718897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14559235984355681027834117 2729856747066690192718897)
      ·
        refine ⟨2047392560300017644539173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2729856747066690192718897 2047392560300017644539173)
        ·
          refine ⟨383886105056253308351095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2047392560300017644539173 383886105056253308351095)
          ·
            refine ⟨575829157584379962526643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383886105056253308351095 575829157584379962526643)
            ·
              refine ⟨863743736376569943789965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575829157584379962526643 863743736376569943789965)
              ·
                refine ⟨323903901141213728921237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863743736376569943789965 323903901141213728921237)
                ·
                  refine ⟨15182995365994393543183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 323903901141213728921237 15182995365994393543183)
                  ·
                    rfl

theorem cell23_266119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 6].length) (baseStart_266119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266119 prefixEnd_266119 := by exact prefixLift 266119
  have htrace : WordTrace (prefixWord ++ tailWord_266119) baseStart_266119 baseEnd_266119 := by
    simpa [prefixWord, tailWord_266119, baseEnd_266119] using wordTrace_append hprefix tailTrace_266119
  have hstable : (prefixWord ++ tailWord_266119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266119).length < 2 ^ (prefixWord ++ tailWord_266119).sum := by decide
  have hdescent : baseEnd_266119 < baseStart_266119 := by decide
  rcases family_descends (prefixWord ++ tailWord_266119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266129 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 3, 1, 3]
def baseStart_266129 : Nat := 118140960795 + 266129 * 2 ^ 59
def prefixEnd_266129 : Nat := 4983230072969 + 3 ^ 40 * 266129 * 2
def baseEnd_266129 : Nat := 136652093100494502763601

theorem tailTrace_266129 : CollatzResearch.WordTrace tailWord_266129 prefixEnd_266129 136652093100494502763601 := by
  unfold tailWord_266129
  simp only [CollatzResearch.WordTrace]
  refine ⟨9706522052867559059753441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6471014701911706039835627 9706522052867559059753441)
  ·
    refine ⟨7279891539650669294815081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9706522052867559059753441 7279891539650669294815081)
    ·
      refine ⟨5459918654738001971111311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7279891539650669294815081 5459918654738001971111311)
      ·
        refine ⟨8189877982107002956666967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5459918654738001971111311 8189877982107002956666967)
        ·
          refine ⟨12284816973160504435000451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8189877982107002956666967 12284816973160504435000451)
          ·
            refine ⟨18427225459740756652500677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12284816973160504435000451 18427225459740756652500677)
            ·
              refine ⟨3455104773701391872343877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18427225459740756652500677 3455104773701391872343877)
              ·
                refine ⟨647832145069010976064477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3455104773701391872343877 647832145069010976064477)
                ·
                  refine ⟨242937054400879116024179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 647832145069010976064477 242937054400879116024179)
                  ·
                    refine ⟨364405581601318674036269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242937054400879116024179 364405581601318674036269)
                    ·
                      refine ⟨136652093100494502763601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 364405581601318674036269 136652093100494502763601)
                      ·
                        rfl

theorem cell23_266129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_266129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266129 prefixEnd_266129 := by exact prefixLift 266129
  have htrace : WordTrace (prefixWord ++ tailWord_266129) baseStart_266129 baseEnd_266129 := by
    simpa [prefixWord, tailWord_266129, baseEnd_266129] using wordTrace_append hprefix tailTrace_266129
  have hstable : (prefixWord ++ tailWord_266129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266129).length < 2 ^ (prefixWord ++ tailWord_266129).sum := by decide
  have hdescent : baseEnd_266129 < baseStart_266129 := by decide
  rcases family_descends (prefixWord ++ tailWord_266129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266186 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2]
def baseStart_266186 : Nat := 118140960795 + 266186 * 2 ^ 59
def prefixEnd_266186 : Nat := 4983230072969 + 3 ^ 40 * 266186 * 2
def baseEnd_266186 : Nat := 136681361497800779750839

theorem tailTrace_266186 : CollatzResearch.WordTrace tailWord_266186 prefixEnd_266186 136681361497800779750839 := by
  unfold tailWord_266186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2427150253415264448644603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6472400675774038529718941 2427150253415264448644603)
  ·
    refine ⟨3640725380122896672966905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2427150253415264448644603 3640725380122896672966905)
    ·
      refine ⟨2730544035092172504725179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3640725380122896672966905 2730544035092172504725179)
      ·
        refine ⟨4095816052638258757087769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730544035092172504725179 4095816052638258757087769)
        ·
          refine ⟨3071862039478694067815827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4095816052638258757087769 3071862039478694067815827)
          ·
            refine ⟨4607793059218041101723741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071862039478694067815827 4607793059218041101723741)
            ·
              refine ⟨1727922397206765413146403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4607793059218041101723741 1727922397206765413146403)
              ·
                refine ⟨2591883595810148119719605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727922397206765413146403 2591883595810148119719605)
                ·
                  refine ⟨242989087107201386223713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2591883595810148119719605 242989087107201386223713)
                  ·
                    refine ⟨182241815330401039667785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 242989087107201386223713 182241815330401039667785)
                    ·
                      refine ⟨136681361497800779750839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182241815330401039667785 136681361497800779750839)
                      ·
                        rfl

theorem cell23_266186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_266186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266186 prefixEnd_266186 := by exact prefixLift 266186
  have htrace : WordTrace (prefixWord ++ tailWord_266186) baseStart_266186 baseEnd_266186 := by
    simpa [prefixWord, tailWord_266186, baseEnd_266186] using wordTrace_append hprefix tailTrace_266186
  have hstable : (prefixWord ++ tailWord_266186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266186).length < 2 ^ (prefixWord ++ tailWord_266186).sum := by decide
  have hdescent : baseEnd_266186 < baseStart_266186 := by decide
  rcases family_descends (prefixWord ++ tailWord_266186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266230 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_266230 : Nat := 118140960795 + 266230 * 2 ^ 59
def prefixEnd_266230 : Nat := 4983230072969 + 3 ^ 40 * 266230 * 2
def baseEnd_266230 : Nat := 45567984882199535866879

theorem tailTrace_266230 : CollatzResearch.WordTrace tailWord_266230 prefixEnd_266230 45567984882199535866879 := by
  unfold tailWord_266230
  simp only [CollatzResearch.WordTrace]
  refine ⟨606887864093853331823759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6473470550334435539453429 606887864093853331823759)
  ·
    refine ⟨910331796140779997735639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 606887864093853331823759 910331796140779997735639)
    ·
      refine ⟨1365497694211169996603459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910331796140779997735639 1365497694211169996603459)
      ·
        refine ⟨2048246541316754994905189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1365497694211169996603459 2048246541316754994905189)
        ·
          refine ⟨384046226496891561544723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2048246541316754994905189 384046226496891561544723)
          ·
            refine ⟨576069339745337342317085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384046226496891561544723 576069339745337342317085)
            ·
              refine ⟨216026002404501503368907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576069339745337342317085 216026002404501503368907)
              ·
                refine ⟨324039003606752255053361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216026002404501503368907 324039003606752255053361)
                ·
                  refine ⟨243029252705064191290021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324039003606752255053361 243029252705064191290021)
                  ·
                    refine ⟨45567984882199535866879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243029252705064191290021 45567984882199535866879)
                    ·
                      rfl

theorem cell23_266230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_266230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266230 prefixEnd_266230 := by exact prefixLift 266230
  have htrace : WordTrace (prefixWord ++ tailWord_266230) baseStart_266230 baseEnd_266230 := by
    simpa [prefixWord, tailWord_266230, baseEnd_266230] using wordTrace_append hprefix tailTrace_266230
  have hstable : (prefixWord ++ tailWord_266230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266230).length < 2 ^ (prefixWord ++ tailWord_266230).sum := by decide
  have hdescent : baseEnd_266230 < baseStart_266230 := by decide
  rcases family_descends (prefixWord ++ tailWord_266230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266297 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 1, 3, 2]
def baseStart_266297 : Nat := 118140960795 + 266297 * 2 ^ 59
def prefixEnd_266297 : Nat := 4983230072969 + 3 ^ 40 * 266297 * 2
def baseEnd_266297 : Nat := 136738357850449845462829

theorem tailTrace_266297 : CollatzResearch.WordTrace tailWord_266297 prefixEnd_266297 136738357850449845462829 := by
  unfold tailWord_266297
  simp only [CollatzResearch.WordTrace]
  refine ⟨9712649516258923751869145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6475099677505949167912763 9712649516258923751869145)
  ·
    refine ⟨7284487137194192813901859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9712649516258923751869145 7284487137194192813901859)
    ·
      refine ⟨10926730705791289220852789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7284487137194192813901859 10926730705791289220852789)
      ·
        refine ⟨1024381003667933364454949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10926730705791289220852789 1024381003667933364454949)
        ·
          refine ⟨192071438187737505835303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1024381003667933364454949 192071438187737505835303)
          ·
            refine ⟨288107157281606258752955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192071438187737505835303 288107157281606258752955)
            ·
              refine ⟨432160735922409388129433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288107157281606258752955 432160735922409388129433)
              ·
                refine ⟨324120551941807041097075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432160735922409388129433 324120551941807041097075)
                ·
                  refine ⟨486180827912710561645613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324120551941807041097075 486180827912710561645613)
                  ·
                    refine ⟨182317810467266460617105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486180827912710561645613 182317810467266460617105)
                    ·
                      refine ⟨136738357850449845462829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182317810467266460617105 136738357850449845462829)
                      ·
                        rfl

theorem cell23_266297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_266297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266297 prefixEnd_266297 := by exact prefixLift 266297
  have htrace : WordTrace (prefixWord ++ tailWord_266297) baseStart_266297 baseEnd_266297 := by
    simpa [prefixWord, tailWord_266297, baseEnd_266297] using wordTrace_append hprefix tailTrace_266297
  have hstable : (prefixWord ++ tailWord_266297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266297).length < 2 ^ (prefixWord ++ tailWord_266297).sum := by decide
  have hdescent : baseEnd_266297 < baseStart_266297 := by decide
  rcases family_descends (prefixWord ++ tailWord_266297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266309 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 4, 3, 3]
def baseStart_266309 : Nat := 118140960795 + 266309 * 2 ^ 59
def prefixEnd_266309 : Nat := 4983230072969 + 3 ^ 40 * 266309 * 2
def baseEnd_266309 : Nat := 136744519618303798512773

theorem tailTrace_266309 : CollatzResearch.WordTrace tailWord_266309 prefixEnd_266309 136744519618303798512773 := by
  unfold tailWord_266309
  simp only [CollatzResearch.WordTrace]
  refine ⟨9713087192215449801305981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6475391461476966534203987 9713087192215449801305981)
  ·
    refine ⟨3642407697080793675489743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9713087192215449801305981 3642407697080793675489743)
    ·
      refine ⟨5463611545621190513234615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3642407697080793675489743 5463611545621190513234615)
      ·
        refine ⟨8195417318431785769851923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5463611545621190513234615 8195417318431785769851923)
        ·
          refine ⟨12293125977647678654777885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8195417318431785769851923 12293125977647678654777885)
          ·
            refine ⟨4609922241617879495541707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12293125977647678654777885 4609922241617879495541707)
            ·
              refine ⟨6914883362426819243312561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4609922241617879495541707 6914883362426819243312561)
              ·
                refine ⟨5186162521820114432484421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6914883362426819243312561 5186162521820114432484421)
                ·
                  refine ⟨972405472841271456090829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5186162521820114432484421 972405472841271456090829)
                  ·
                    refine ⟨364652052315476796034061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 972405472841271456090829 364652052315476796034061)
                    ·
                      refine ⟨136744519618303798512773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 364652052315476796034061 136744519618303798512773)
                      ·
                        rfl

theorem cell23_266309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_266309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266309 prefixEnd_266309 := by exact prefixLift 266309
  have htrace : WordTrace (prefixWord ++ tailWord_266309) baseStart_266309 baseEnd_266309 := by
    simpa [prefixWord, tailWord_266309, baseEnd_266309] using wordTrace_append hprefix tailTrace_266309
  have hstable : (prefixWord ++ tailWord_266309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266309).length < 2 ^ (prefixWord ++ tailWord_266309).sum := by decide
  have hdescent : baseEnd_266309 < baseStart_266309 := by decide
  rcases family_descends (prefixWord ++ tailWord_266309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266310 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_266310 : Nat := 118140960795 + 266310 * 2 ^ 59
def prefixEnd_266310 : Nat := 4983230072969 + 3 ^ 40 * 266310 * 2
def baseEnd_266310 : Nat := 136745033098958294600269

theorem tailTrace_266310 : CollatzResearch.WordTrace tailWord_266310 prefixEnd_266310 136745033098958294600269 := by
  unfold tailWord_266310
  simp only [CollatzResearch.WordTrace]
  refine ⟨303535114537869592877887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6475415776807884648061589 303535114537869592877887)
  ·
    refine ⟨455302671806804389316831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303535114537869592877887 455302671806804389316831)
    ·
      refine ⟨682954007710206583975247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455302671806804389316831 682954007710206583975247)
      ·
        refine ⟨1024431011565309875962871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682954007710206583975247 1024431011565309875962871)
        ·
          refine ⟨1536646517347964813944307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024431011565309875962871 1536646517347964813944307)
          ·
            refine ⟨2304969776021947220916461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536646517347964813944307 2304969776021947220916461)
            ·
              refine ⟨864363666008230207843673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2304969776021947220916461 864363666008230207843673)
              ·
                refine ⟨648272749506172655882755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864363666008230207843673 648272749506172655882755)
                ·
                  refine ⟨972409124259258983824133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648272749506172655882755 972409124259258983824133)
                  ·
                    refine ⟨182326710798611059467025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 972409124259258983824133 182326710798611059467025)
                    ·
                      refine ⟨136745033098958294600269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182326710798611059467025 136745033098958294600269)
                      ·
                        rfl

theorem cell23_266310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_266310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266310 prefixEnd_266310 := by exact prefixLift 266310
  have htrace : WordTrace (prefixWord ++ tailWord_266310) baseStart_266310 baseEnd_266310 := by
    simpa [prefixWord, tailWord_266310, baseEnd_266310] using wordTrace_append hprefix tailTrace_266310
  have hstable : (prefixWord ++ tailWord_266310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266310).length < 2 ^ (prefixWord ++ tailWord_266310).sum := by decide
  have hdescent : baseEnd_266310 < baseStart_266310 := by decide
  rcases family_descends (prefixWord ++ tailWord_266310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266329 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 2, 5]
def baseStart_266329 : Nat := 118140960795 + 266329 * 2 ^ 59
def prefixEnd_266329 : Nat := 4983230072969 + 3 ^ 40 * 266329 * 2
def baseEnd_266329 : Nat := 45584929743797906754227

theorem tailTrace_266329 : CollatzResearch.WordTrace tailWord_266329 prefixEnd_266329 45584929743797906754227 := by
  unfold tailWord_266329
  simp only [CollatzResearch.WordTrace]
  refine ⟨9713816652142993217034041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6475877768095328811356027 9713816652142993217034041)
  ·
    refine ⟨7285362489107244912775531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9713816652142993217034041 7285362489107244912775531)
    ·
      refine ⟨10928043733660867369163297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7285362489107244912775531 10928043733660867369163297)
      ·
        refine ⟨8196032800245650526872473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10928043733660867369163297 8196032800245650526872473)
        ·
          refine ⟨6147024600184237895154355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8196032800245650526872473 6147024600184237895154355)
          ·
            refine ⟨9220536900276356842731533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6147024600184237895154355 9220536900276356842731533)
            ·
              refine ⟨3457701337603633816024325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9220536900276356842731533 3457701337603633816024325)
              ·
                refine ⟨648319000800681340504561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3457701337603633816024325 648319000800681340504561)
                ·
                  refine ⟨486239250600511005378421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 648319000800681340504561 486239250600511005378421)
                  ·
                    refine ⟨45584929743797906754227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 486239250600511005378421 45584929743797906754227)
                    ·
                      rfl

theorem cell23_266329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_266329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266329 prefixEnd_266329 := by exact prefixLift 266329
  have htrace : WordTrace (prefixWord ++ tailWord_266329) baseStart_266329 baseEnd_266329 := by
    simpa [prefixWord, tailWord_266329, baseEnd_266329] using wordTrace_append hprefix tailTrace_266329
  have hstable : (prefixWord ++ tailWord_266329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266329).length < 2 ^ (prefixWord ++ tailWord_266329).sum := by decide
  have hdescent : baseEnd_266329 < baseStart_266329 := by decide
  rcases family_descends (prefixWord ++ tailWord_266329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266336 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 2, 5, 2]
def baseStart_266336 : Nat := 118140960795 + 266336 * 2 ^ 59
def prefixEnd_266336 : Nat := 4983230072969 + 3 ^ 40 * 266336 * 2
def baseEnd_266336 : Nat := 136758383595975192875149

theorem tailTrace_266336 : CollatzResearch.WordTrace tailWord_266336 prefixEnd_266336 136758383595975192875149 := by
  unfold tailWord_266336
  simp only [CollatzResearch.WordTrace]
  refine ⟨4857035981558816706269431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6476047975411755608359241 4857035981558816706269431)
  ·
    refine ⟨7285553972338225059404147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4857035981558816706269431 7285553972338225059404147)
    ·
      refine ⟨10928330958507337589106221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7285553972338225059404147 10928330958507337589106221)
      ·
        refine ⟨4098124109440251595914833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10928330958507337589106221 4098124109440251595914833)
        ·
          refine ⟨3073593082080188696936125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4098124109440251595914833 3073593082080188696936125)
          ·
            refine ⟨1152597405780070761351047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3073593082080188696936125 1152597405780070761351047)
            ·
              refine ⟨1728896108670106142026571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152597405780070761351047 1728896108670106142026571)
              ·
                refine ⟨2593344163005159213039857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1728896108670106142026571 2593344163005159213039857)
                ·
                  refine ⟨1945008122253869409779893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2593344163005159213039857 1945008122253869409779893)
                  ·
                    refine ⟨182344511461300257166865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1945008122253869409779893 182344511461300257166865)
                    ·
                      refine ⟨136758383595975192875149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182344511461300257166865 136758383595975192875149)
                      ·
                        rfl

theorem cell23_266336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_266336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266336 prefixEnd_266336 := by exact prefixLift 266336
  have htrace : WordTrace (prefixWord ++ tailWord_266336) baseStart_266336 baseEnd_266336 := by
    simpa [prefixWord, tailWord_266336, baseEnd_266336] using wordTrace_append hprefix tailTrace_266336
  have hstable : (prefixWord ++ tailWord_266336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266336).length < 2 ^ (prefixWord ++ tailWord_266336).sum := by decide
  have hdescent : baseEnd_266336 < baseStart_266336 := by decide
  rcases family_descends (prefixWord ++ tailWord_266336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266339 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 5]
def baseStart_266339 : Nat := 118140960795 + 266339 * 2 ^ 59
def prefixEnd_266339 : Nat := 4983230072969 + 3 ^ 40 * 266339 * 2
def baseEnd_266339 : Nat := 136759924037938681137635

theorem tailTrace_266339 : CollatzResearch.WordTrace tailWord_266339 prefixEnd_266339 136759924037938681137635 := by
  unfold tailWord_266339
  simp only [CollatzResearch.WordTrace]
  refine ⟨9714181382106764924898071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6476120921404509949932047 9714181382106764924898071)
  ·
    refine ⟨14571272073160147387347107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9714181382106764924898071 14571272073160147387347107)
    ·
      refine ⟨21856908109740221081020661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14571272073160147387347107 21856908109740221081020661)
      ·
        refine ⟨2049085135288145726345687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21856908109740221081020661 2049085135288145726345687)
        ·
          refine ⟨3073627702932218589518531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2049085135288145726345687 3073627702932218589518531)
          ·
            refine ⟨4610441554398327884277797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073627702932218589518531 4610441554398327884277797)
            ·
              refine ⟨864457791449686478302087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4610441554398327884277797 864457791449686478302087)
              ·
                refine ⟨1296686687174529717453131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864457791449686478302087 1296686687174529717453131)
                ·
                  refine ⟨1945030030761794576179697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296686687174529717453131 1945030030761794576179697)
                  ·
                    refine ⟨1458772523071345932134773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1945030030761794576179697 1458772523071345932134773)
                    ·
                      refine ⟨136759924037938681137635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1458772523071345932134773 136759924037938681137635)
                      ·
                        rfl

theorem cell23_266339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_266339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266339 prefixEnd_266339 := by exact prefixLift 266339
  have htrace : WordTrace (prefixWord ++ tailWord_266339) baseStart_266339 baseEnd_266339 := by
    simpa [prefixWord, tailWord_266339, baseEnd_266339] using wordTrace_append hprefix tailTrace_266339
  have hstable : (prefixWord ++ tailWord_266339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266339).length < 2 ^ (prefixWord ++ tailWord_266339).sum := by decide
  have hdescent : baseEnd_266339 < baseStart_266339 := by decide
  rcases family_descends (prefixWord ++ tailWord_266339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266389 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 8]
def baseStart_266389 : Nat := 118140960795 + 266389 * 2 ^ 59
def prefixEnd_266389 : Nat := 4983230072969 + 3 ^ 40 * 266389 * 2
def baseEnd_266389 : Nat := 15198399785629276168045

theorem tailTrace_266389 : CollatzResearch.WordTrace tailWord_266389 prefixEnd_266389 15198399785629276168045 := by
  unfold tailWord_266389
  simp only [CollatzResearch.WordTrace]
  refine ⟨9716005031925623464218221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6477336687950415642812147 9716005031925623464218221)
  ·
    refine ⟨3643501886972108799081833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9716005031925623464218221 3643501886972108799081833)
    ·
      refine ⟨2732626415229081599311375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3643501886972108799081833 2732626415229081599311375)
      ·
        refine ⟨4098939622843622398967063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2732626415229081599311375 4098939622843622398967063)
        ·
          refine ⟨6148409434265433598450595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4098939622843622398967063 6148409434265433598450595)
          ·
            refine ⟨9222614151398150397675893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6148409434265433598450595 9222614151398150397675893)
            ·
              refine ⟨864620076693576599782115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9222614151398150397675893 864620076693576599782115)
              ·
                refine ⟨1296930115040364899673173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864620076693576599782115 1296930115040364899673173)
                ·
                  refine ⟨15198399785629276168045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1296930115040364899673173 15198399785629276168045)
                  ·
                    rfl

theorem cell23_266389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_266389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266389 prefixEnd_266389 := by exact prefixLift 266389
  have htrace : WordTrace (prefixWord ++ tailWord_266389) baseStart_266389 baseEnd_266389 := by
    simpa [prefixWord, tailWord_266389, baseEnd_266389] using wordTrace_append hprefix tailTrace_266389
  have hstable : (prefixWord ++ tailWord_266389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266389).length < 2 ^ (prefixWord ++ tailWord_266389).sum := by decide
  have hdescent : baseEnd_266389 < baseStart_266389 := by decide
  rcases family_descends (prefixWord ++ tailWord_266389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266443 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 2, 3, 2]
def baseStart_266443 : Nat := 118140960795 + 266443 * 2 ^ 59
def prefixEnd_266443 : Nat := 4983230072969 + 3 ^ 40 * 266443 * 2
def baseEnd_266443 : Nat := 136813326026006274237157

theorem tailTrace_266443 : CollatzResearch.WordTrace tailWord_266443 prefixEnd_266443 136813326026006274237157 := by
  unfold tailWord_266443
  simp only [CollatzResearch.WordTrace]
  refine ⟨9717974573729990686683983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6478649715819993791122655 9717974573729990686683983)
  ·
    refine ⟨14576961860594986030025975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9717974573729990686683983 14576961860594986030025975)
    ·
      refine ⟨21865442790892479045038963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14576961860594986030025975 21865442790892479045038963)
      ·
        refine ⟨32798164186338718567558445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21865442790892479045038963 32798164186338718567558445)
        ·
          refine ⟨12299311569877019462834417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32798164186338718567558445 12299311569877019462834417)
          ·
            refine ⟨9224483677407764597125813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12299311569877019462834417 9224483677407764597125813)
            ·
              refine ⟨864795344756977930980545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9224483677407764597125813 864795344756977930980545)
              ·
                refine ⟨648596508567733448235409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864795344756977930980545 648596508567733448235409)
                ·
                  refine ⟨486447381425800086176557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 648596508567733448235409 486447381425800086176557)
                  ·
                    refine ⟨182417768034675032316209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486447381425800086176557 182417768034675032316209)
                    ·
                      refine ⟨136813326026006274237157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182417768034675032316209 136813326026006274237157)
                      ·
                        rfl

theorem cell23_266443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 3, 2].length) (baseStart_266443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266443 prefixEnd_266443 := by exact prefixLift 266443
  have htrace : WordTrace (prefixWord ++ tailWord_266443) baseStart_266443 baseEnd_266443 := by
    simpa [prefixWord, tailWord_266443, baseEnd_266443] using wordTrace_append hprefix tailTrace_266443
  have hstable : (prefixWord ++ tailWord_266443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266443).length < 2 ^ (prefixWord ++ tailWord_266443).sum := by decide
  have hdescent : baseEnd_266443 < baseStart_266443 := by decide
  rcases family_descends (prefixWord ++ tailWord_266443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266444 : List Nat := [2, 2, 1, 6, 1, 1, 3, 2, 1, 4]
def baseStart_266444 : Nat := 118140960795 + 266444 * 2 ^ 59
def prefixEnd_266444 : Nat := 4983230072969 + 3 ^ 40 * 266444 * 2
def baseEnd_266444 : Nat := 45604613168886923441551

theorem tailTrace_266444 : CollatzResearch.WordTrace tailWord_266444 prefixEnd_266444 45604613168886923441551 := by
  unfold tailWord_266444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4859005523363183928735193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6478674031150911904980257 4859005523363183928735193)
  ·
    refine ⟨3644254142522387946551395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4859005523363183928735193 3644254142522387946551395)
    ·
      refine ⟨5466381213783581919827093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3644254142522387946551395 5466381213783581919827093)
      ·
        refine ⟨256236619396105402491895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5466381213783581919827093 256236619396105402491895)
        ·
          refine ⟨384354929094158103737843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256236619396105402491895 384354929094158103737843)
          ·
            refine ⟨576532393641237155606765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384354929094158103737843 576532393641237155606765)
            ·
              refine ⟨216199647615463933352537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576532393641237155606765 216199647615463933352537)
              ·
                refine ⟨162149735711597950014403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216199647615463933352537 162149735711597950014403)
                ·
                  refine ⟨243224603567396925021605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162149735711597950014403 243224603567396925021605)
                  ·
                    refine ⟨45604613168886923441551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243224603567396925021605 45604613168886923441551)
                    ·
                      rfl

theorem cell23_266444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_266444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266444 prefixEnd_266444 := by exact prefixLift 266444
  have htrace : WordTrace (prefixWord ++ tailWord_266444) baseStart_266444 baseEnd_266444 := by
    simpa [prefixWord, tailWord_266444, baseEnd_266444] using wordTrace_append hprefix tailTrace_266444
  have hstable : (prefixWord ++ tailWord_266444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266444).length < 2 ^ (prefixWord ++ tailWord_266444).sum := by decide
  have hdescent : baseEnd_266444 < baseStart_266444 := by decide
  rcases family_descends (prefixWord ++ tailWord_266444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266450 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_266450 : Nat := 118140960795 + 266450 * 2 ^ 59
def prefixEnd_266450 : Nat := 4983230072969 + 3 ^ 40 * 266450 * 2
def baseEnd_266450 : Nat := 136816920390587746849625

theorem tailTrace_266450 : CollatzResearch.WordTrace tailWord_266450 prefixEnd_266450 136816920390587746849625 := by
  unfold tailWord_266450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2429557471176157720547201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6478819923136420588125869 2429557471176157720547201)
  ·
    refine ⟨1822168103382118290410401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2429557471176157720547201 1822168103382118290410401)
    ·
      refine ⟨1366626077536588717807801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1822168103382118290410401 1366626077536588717807801)
      ·
        refine ⟨1024969558152441538355851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1366626077536588717807801 1024969558152441538355851)
        ·
          refine ⟨1537454337228662307533777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024969558152441538355851 1537454337228662307533777)
          ·
            refine ⟨1153090752921496730650333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1537454337228662307533777 1153090752921496730650333)
            ·
              refine ⟨432409032345561273993875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1153090752921496730650333 432409032345561273993875)
              ·
                refine ⟨648613548518341910990813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432409032345561273993875 648613548518341910990813)
                ·
                  refine ⟨243230080694378216621555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 648613548518341910990813 243230080694378216621555)
                  ·
                    refine ⟨364845121041567324932333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243230080694378216621555 364845121041567324932333)
                    ·
                      refine ⟨136816920390587746849625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 364845121041567324932333 136816920390587746849625)
                      ·
                        rfl

theorem cell23_266450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_266450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266450 prefixEnd_266450 := by exact prefixLift 266450
  have htrace : WordTrace (prefixWord ++ tailWord_266450) baseStart_266450 baseEnd_266450 := by
    simpa [prefixWord, tailWord_266450, baseEnd_266450] using wordTrace_append hprefix tailTrace_266450
  have hstable : (prefixWord ++ tailWord_266450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266450).length < 2 ^ (prefixWord ++ tailWord_266450).sum := by decide
  have hdescent : baseEnd_266450 < baseStart_266450 := by decide
  rcases family_descends (prefixWord ++ tailWord_266450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266477 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_266477 : Nat := 118140960795 + 266477 * 2 ^ 59
def prefixEnd_266477 : Nat := 4983230072969 + 3 ^ 40 * 266477 * 2
def baseEnd_266477 : Nat := 136830784368259141212001

theorem tailTrace_266477 : CollatzResearch.WordTrace tailWord_266477 prefixEnd_266477 136830784368259141212001 := by
  unfold tailWord_266477
  simp only [CollatzResearch.WordTrace]
  refine ⟨9719214655606814493421685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6479476437071209662281123 9719214655606814493421685)
  ·
    refine ⟨911176373963138858758283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9719214655606814493421685 911176373963138858758283)
    ·
      refine ⟨1366764560944708288137425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 911176373963138858758283 1366764560944708288137425)
      ·
        refine ⟨1025073420708531216103069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1366764560944708288137425 1025073420708531216103069)
        ·
          refine ⟨384402532765699206038651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1025073420708531216103069 384402532765699206038651)
          ·
            refine ⟨576603799148548809057977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384402532765699206038651 576603799148548809057977)
            ·
              refine ⟨432452849361411606793483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576603799148548809057977 432452849361411606793483)
              ·
                refine ⟨648679274042117410190225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432452849361411606793483 648679274042117410190225)
                ·
                  refine ⟨486509455531588057642669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 648679274042117410190225 486509455531588057642669)
                  ·
                    refine ⟨182441045824345521616001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 486509455531588057642669 182441045824345521616001)
                    ·
                      refine ⟨136830784368259141212001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182441045824345521616001 136830784368259141212001)
                      ·
                        rfl

theorem cell23_266477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_266477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266477 prefixEnd_266477 := by exact prefixLift 266477
  have htrace : WordTrace (prefixWord ++ tailWord_266477) baseStart_266477 baseEnd_266477 := by
    simpa [prefixWord, tailWord_266477, baseEnd_266477] using wordTrace_append hprefix tailTrace_266477
  have hstable : (prefixWord ++ tailWord_266477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266477).length < 2 ^ (prefixWord ++ tailWord_266477).sum := by decide
  have hdescent : baseEnd_266477 < baseStart_266477 := by decide
  rcases family_descends (prefixWord ++ tailWord_266477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266490 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4]
def baseStart_266490 : Nat := 118140960795 + 266490 * 2 ^ 59
def prefixEnd_266490 : Nat := 4983230072969 + 3 ^ 40 * 266490 * 2
def baseEnd_266490 : Nat := 136837459616767590349441

theorem tailTrace_266490 : CollatzResearch.WordTrace tailWord_266490 prefixEnd_266490 136837459616767590349441 := by
  unfold tailWord_266490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2429922201139929428411231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6479792536373145142429949 2429922201139929428411231)
  ·
    refine ⟨3644883301709894142616847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2429922201139929428411231 3644883301709894142616847)
    ·
      refine ⟨5467324952564841213925271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3644883301709894142616847 5467324952564841213925271)
      ·
        refine ⟨8200987428847261820887907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5467324952564841213925271 8200987428847261820887907)
        ·
          refine ⟨12301481143270892731331861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8200987428847261820887907 12301481143270892731331861)
          ·
            refine ⟨576631928590823096781181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12301481143270892731331861 576631928590823096781181)
            ·
              refine ⟨216236973221558661292943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576631928590823096781181 216236973221558661292943)
              ·
                refine ⟨324355459832337991939415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216236973221558661292943 324355459832337991939415)
                ·
                  refine ⟨486533189748506987909123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324355459832337991939415 486533189748506987909123)
                  ·
                    refine ⟨729799784622760481863685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 486533189748506987909123 729799784622760481863685)
                    ·
                      refine ⟨136837459616767590349441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 729799784622760481863685 136837459616767590349441)
                      ·
                        rfl

theorem cell23_266490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4].length) (baseStart_266490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266490 prefixEnd_266490 := by exact prefixLift 266490
  have htrace : WordTrace (prefixWord ++ tailWord_266490) baseStart_266490 baseEnd_266490 := by
    simpa [prefixWord, tailWord_266490, baseEnd_266490] using wordTrace_append hprefix tailTrace_266490
  have hstable : (prefixWord ++ tailWord_266490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266490).length < 2 ^ (prefixWord ++ tailWord_266490).sum := by decide
  have hdescent : baseEnd_266490 < baseStart_266490 := by decide
  rcases family_descends (prefixWord ++ tailWord_266490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266493 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_266493 : Nat := 118140960795 + 266493 * 2 ^ 59
def prefixEnd_266493 : Nat := 4983230072969 + 3 ^ 40 * 266493 * 2
def baseEnd_266493 : Nat := 136839000058731078611927

theorem tailTrace_266493 : CollatzResearch.WordTrace tailWord_266493 prefixEnd_266493 136839000058731078611927 := by
  unfold tailWord_266493
  simp only [CollatzResearch.WordTrace]
  refine ⟨9719798223548849226004133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6479865482365899484002755 9719798223548849226004133)
  ·
    refine ⟨1822462166915409229875775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9719798223548849226004133 1822462166915409229875775)
    ·
      refine ⟨2733693250373113844813663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1822462166915409229875775 2733693250373113844813663)
      ·
        refine ⟨4100539875559670767220495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2733693250373113844813663 4100539875559670767220495)
        ·
          refine ⟨6150809813339506150830743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4100539875559670767220495 6150809813339506150830743)
          ·
            refine ⟨9226214720009259226246115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6150809813339506150830743 9226214720009259226246115)
            ·
              refine ⟨13839322080013888839369173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9226214720009259226246115 13839322080013888839369173)
              ·
                refine ⟨324359111250325519672715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13839322080013888839369173 324359111250325519672715)
                ·
                  refine ⟨486538666875488279509073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324359111250325519672715 486538666875488279509073)
                  ·
                    refine ⟨364904000156616209631805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 486538666875488279509073 364904000156616209631805)
                    ·
                      refine ⟨136839000058731078611927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 364904000156616209631805 136839000058731078611927)
                      ·
                        rfl

theorem cell23_266493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_266493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266493 prefixEnd_266493 := by exact prefixLift 266493
  have htrace : WordTrace (prefixWord ++ tailWord_266493) baseStart_266493 baseEnd_266493 := by
    simpa [prefixWord, tailWord_266493, baseEnd_266493] using wordTrace_append hprefix tailTrace_266493
  have hstable : (prefixWord ++ tailWord_266493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266493).length < 2 ^ (prefixWord ++ tailWord_266493).sum := by decide
  have hdescent : baseEnd_266493 < baseStart_266493 := by decide
  rcases family_descends (prefixWord ++ tailWord_266493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266507 : List Nat := [1, 1, 1, 1, 5, 2, 3, 4, 1, 2, 2]
def baseStart_266507 : Nat := 118140960795 + 266507 * 2 ^ 59
def prefixEnd_266507 : Nat := 4983230072969 + 3 ^ 40 * 266507 * 2
def baseEnd_266507 : Nat := 136846188787894023836863

theorem tailTrace_266507 : CollatzResearch.WordTrace tailWord_266507 prefixEnd_266507 136846188787894023836863 := by
  unfold tailWord_266507
  simp only [CollatzResearch.WordTrace]
  refine ⟨9720308845498129617013775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6480205896998753078009183 9720308845498129617013775)
  ·
    refine ⟨14580463268247194425520663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9720308845498129617013775 14580463268247194425520663)
    ·
      refine ⟨21870694902370791638280995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14580463268247194425520663 21870694902370791638280995)
      ·
        refine ⟨32806042353556187457421493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21870694902370791638280995 32806042353556187457421493)
        ·
          refine ⟨3075566470645892574133265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32806042353556187457421493 3075566470645892574133265)
          ·
            refine ⟨2306674852984419430599949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3075566470645892574133265 2306674852984419430599949)
            ·
              refine ⟨865003069869157286474981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2306674852984419430599949 865003069869157286474981)
              ·
                refine ⟨162188075600466991214059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 865003069869157286474981 162188075600466991214059)
                ·
                  refine ⟨243282113400700486821089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162188075600466991214059 243282113400700486821089)
                  ·
                    refine ⟨182461585050525365115817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 243282113400700486821089 182461585050525365115817)
                    ·
                      refine ⟨136846188787894023836863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182461585050525365115817 136846188787894023836863)
                      ·
                        rfl

theorem cell23_266507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 1, 2, 2].length) (baseStart_266507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266507 prefixEnd_266507 := by exact prefixLift 266507
  have htrace : WordTrace (prefixWord ++ tailWord_266507) baseStart_266507 baseEnd_266507 := by
    simpa [prefixWord, tailWord_266507, baseEnd_266507] using wordTrace_append hprefix tailTrace_266507
  have hstable : (prefixWord ++ tailWord_266507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266507).length < 2 ^ (prefixWord ++ tailWord_266507).sum := by decide
  have hdescent : baseEnd_266507 < baseStart_266507 := by decide
  rcases family_descends (prefixWord ++ tailWord_266507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266541 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_266541 : Nat := 118140960795 + 266541 * 2 ^ 59
def prefixEnd_266541 : Nat := 4983230072969 + 3 ^ 40 * 266541 * 2
def baseEnd_266541 : Nat := 136863647130146890811707

theorem tailTrace_266541 : CollatzResearch.WordTrace tailWord_266541 prefixEnd_266541 136863647130146890811707 := by
  unfold tailWord_266541
  simp only [CollatzResearch.WordTrace]
  refine ⟨9721548927374953423751477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6481032618249968949167651 9721548927374953423751477)
  ·
    refine ⟨911395211941401883476701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9721548927374953423751477 911395211941401883476701)
    ·
      refine ⟨341773204478025706303763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 911395211941401883476701 341773204478025706303763)
      ·
        refine ⟨512659806717038559455645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341773204478025706303763 512659806717038559455645)
        ·
          refine ⟨192247427518889459795867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512659806717038559455645 192247427518889459795867)
          ·
            refine ⟨288371141278334189693801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192247427518889459795867 288371141278334189693801)
            ·
              refine ⟨216278355958750642270351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288371141278334189693801 216278355958750642270351)
              ·
                refine ⟨324417533938125963405527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216278355958750642270351 324417533938125963405527)
                ·
                  refine ⟨486626300907188945108291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324417533938125963405527 486626300907188945108291)
                  ·
                    refine ⟨729939451360783417662437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 486626300907188945108291 729939451360783417662437)
                    ·
                      refine ⟨136863647130146890811707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 729939451360783417662437 136863647130146890811707)
                      ·
                        rfl

theorem cell23_266541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_266541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266541 prefixEnd_266541 := by exact prefixLift 266541
  have htrace : WordTrace (prefixWord ++ tailWord_266541) baseStart_266541 baseEnd_266541 := by
    simpa [prefixWord, tailWord_266541, baseEnd_266541] using wordTrace_append hprefix tailTrace_266541
  have hstable : (prefixWord ++ tailWord_266541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266541).length < 2 ^ (prefixWord ++ tailWord_266541).sum := by decide
  have hdescent : baseEnd_266541 < baseStart_266541 := by decide
  rcases family_descends (prefixWord ++ tailWord_266541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266556 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_266556 : Nat := 118140960795 + 266556 * 2 ^ 59
def prefixEnd_266556 : Nat := 4983230072969 + 3 ^ 40 * 266556 * 2
def baseEnd_266556 : Nat := 45623783113321444041379

theorem tailTrace_266556 : CollatzResearch.WordTrace tailWord_266556 prefixEnd_266556 45623783113321444041379 := by
  unfold tailWord_266556
  simp only [CollatzResearch.WordTrace]
  refine ⟨4861048011160305492773761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6481397348213740657031681 4861048011160305492773761)
  ·
    refine ⟨3645786008370229119580321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4861048011160305492773761 3645786008370229119580321)
    ·
      refine ⟨2734339506277671839685241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3645786008370229119580321 2734339506277671839685241)
      ·
        refine ⟨2050754629708253879763931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2734339506277671839685241 2050754629708253879763931)
        ·
          refine ⟨3076131944562380819645897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050754629708253879763931 3076131944562380819645897)
          ·
            refine ⟨2307098958421785614734423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3076131944562380819645897 2307098958421785614734423)
            ·
              refine ⟨3460648437632678422101635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307098958421785614734423 3460648437632678422101635)
              ·
                refine ⟨5190972656449017633152453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3460648437632678422101635 5190972656449017633152453)
                ·
                  refine ⟨973307373084190806216085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5190972656449017633152453 973307373084190806216085)
                  ·
                    refine ⟨45623783113321444041379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 973307373084190806216085 45623783113321444041379)
                    ·
                      rfl

theorem cell23_266556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_266556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266556 prefixEnd_266556 := by exact prefixLift 266556
  have htrace : WordTrace (prefixWord ++ tailWord_266556) baseStart_266556 baseEnd_266556 := by
    simpa [prefixWord, tailWord_266556, baseEnd_266556] using wordTrace_append hprefix tailTrace_266556
  have hstable : (prefixWord ++ tailWord_266556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266556).length < 2 ^ (prefixWord ++ tailWord_266556).sum := by decide
  have hdescent : baseEnd_266556 < baseStart_266556 := by decide
  rcases family_descends (prefixWord ++ tailWord_266556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266563 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 3, 4, 2]
def baseStart_266563 : Nat := 118140960795 + 266563 * 2 ^ 59
def prefixEnd_266563 : Nat := 4983230072969 + 3 ^ 40 * 266563 * 2
def baseEnd_266563 : Nat := 136874943704545804736605

theorem tailTrace_266563 : CollatzResearch.WordTrace tailWord_266563 prefixEnd_266563 136874943704545804736605 := by
  unfold tailWord_266563
  simp only [CollatzResearch.WordTrace]
  refine ⟨9722351333295251181052343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6481567555530167454034895 9722351333295251181052343)
  ·
    refine ⟨14583526999942876771578515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9722351333295251181052343 14583526999942876771578515)
    ·
      refine ⟨21875290499914315157367773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14583526999942876771578515 21875290499914315157367773)
      ·
        refine ⟨8203233937467868184012915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21875290499914315157367773 8203233937467868184012915)
        ·
          refine ⟨12304850906201802276019373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8203233937467868184012915 12304850906201802276019373)
          ·
            refine ⟨4614319089825675853507265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12304850906201802276019373 4614319089825675853507265)
            ·
              refine ⟨3460739317369256890130449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4614319089825675853507265 3460739317369256890130449)
              ·
                refine ⟨2595554488026942667597837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3460739317369256890130449 2595554488026942667597837)
                ·
                  refine ⟨973332933010103500349189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2595554488026942667597837 973332933010103500349189)
                  ·
                    refine ⟨182499924939394406315473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 973332933010103500349189 182499924939394406315473)
                    ·
                      refine ⟨136874943704545804736605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182499924939394406315473 136874943704545804736605)
                      ·
                        rfl

theorem cell23_266563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 4, 2].length) (baseStart_266563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266563 prefixEnd_266563 := by exact prefixLift 266563
  have htrace : WordTrace (prefixWord ++ tailWord_266563) baseStart_266563 baseEnd_266563 := by
    simpa [prefixWord, tailWord_266563, baseEnd_266563] using wordTrace_append hprefix tailTrace_266563
  have hstable : (prefixWord ++ tailWord_266563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266563).length < 2 ^ (prefixWord ++ tailWord_266563).sum := by decide
  have hdescent : baseEnd_266563 < baseStart_266563 := by decide
  rcases family_descends (prefixWord ++ tailWord_266563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266623 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 1, 7, 2]
def baseStart_266623 : Nat := 118140960795 + 266623 * 2 ^ 59
def prefixEnd_266623 : Nat := 4983230072969 + 3 ^ 40 * 266623 * 2
def baseEnd_266623 : Nat := 136905752543815569986329

theorem tailTrace_266623 : CollatzResearch.WordTrace tailWord_266623 prefixEnd_266623 136905752543815569986329 := by
  unfold tailWord_266623
  simp only [CollatzResearch.WordTrace]
  refine ⟨9724539713077881428236523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6483026475385254285491015 9724539713077881428236523)
  ·
    refine ⟨14586809569616822142354785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9724539713077881428236523 14586809569616822142354785)
    ·
      refine ⟨10940107177212616606766089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14586809569616822142354785 10940107177212616606766089)
      ·
        refine ⟨8205080382909462455074567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10940107177212616606766089 8205080382909462455074567)
        ·
          refine ⟨12307620574364193682611851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8205080382909462455074567 12307620574364193682611851)
          ·
            refine ⟨18461430861546290523917777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12307620574364193682611851 18461430861546290523917777)
            ·
              refine ⟨13846073146159717892938333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18461430861546290523917777 13846073146159717892938333)
              ·
                refine ⟨5192277429809894209851875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13846073146159717892938333 5192277429809894209851875)
                ·
                  refine ⟨7788416144714841314777813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5192277429809894209851875 7788416144714841314777813)
                  ·
                    refine ⟨182541003391754093315105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7788416144714841314777813 182541003391754093315105)
                    ·
                      refine ⟨136905752543815569986329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182541003391754093315105 136905752543815569986329)
                      ·
                        rfl

theorem cell23_266623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 7, 2].length) (baseStart_266623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266623 prefixEnd_266623 := by exact prefixLift 266623
  have htrace : WordTrace (prefixWord ++ tailWord_266623) baseStart_266623 baseEnd_266623 := by
    simpa [prefixWord, tailWord_266623, baseEnd_266623] using wordTrace_append hprefix tailTrace_266623
  have hstable : (prefixWord ++ tailWord_266623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266623).length < 2 ^ (prefixWord ++ tailWord_266623).sum := by decide
  have hdescent : baseEnd_266623 < baseStart_266623 := by decide
  rcases family_descends (prefixWord ++ tailWord_266623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266650 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 2, 5]
def baseStart_266650 : Nat := 118140960795 + 266650 * 2 ^ 59
def prefixEnd_266650 : Nat := 4983230072969 + 3 ^ 40 * 266650 * 2
def baseEnd_266650 : Nat := 45639872173828988116235

theorem tailTrace_266650 : CollatzResearch.WordTrace tailWord_266650 prefixEnd_266650 45639872173828988116235 := by
  unfold tailWord_266650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431381120995016259867351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6483682989320043359646269 2431381120995016259867351)
  ·
    refine ⟨3647071681492524389801027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2431381120995016259867351 3647071681492524389801027)
    ·
      refine ⟨5470607522238786584701541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3647071681492524389801027 5470607522238786584701541)
      ·
        refine ⟨1025738910419772484631539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5470607522238786584701541 1025738910419772484631539)
        ·
          refine ⟨1538608365629658726947309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025738910419772484631539 1538608365629658726947309)
          ·
            refine ⟨576978137111122022605241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1538608365629658726947309 576978137111122022605241)
            ·
              refine ⟨432733602833341516953931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576978137111122022605241 432733602833341516953931)
              ·
                refine ⟨649100404250012275430897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432733602833341516953931 649100404250012275430897)
                ·
                  refine ⟨486825303187509206573173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 649100404250012275430897 486825303187509206573173)
                  ·
                    refine ⟨45639872173828988116235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 486825303187509206573173 45639872173828988116235)
                    ·
                      rfl

theorem cell23_266650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_266650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266650 prefixEnd_266650 := by exact prefixLift 266650
  have htrace : WordTrace (prefixWord ++ tailWord_266650) baseStart_266650 baseEnd_266650 := by
    simpa [prefixWord, tailWord_266650, baseEnd_266650] using wordTrace_append hprefix tailTrace_266650
  have hstable : (prefixWord ++ tailWord_266650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266650).length < 2 ^ (prefixWord ++ tailWord_266650).sum := by decide
  have hdescent : baseEnd_266650 < baseStart_266650 := by decide
  rcases family_descends (prefixWord ++ tailWord_266650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266710 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_266710 : Nat := 118140960795 + 266710 * 2 ^ 59
def prefixEnd_266710 : Nat := 4983230072969 + 3 ^ 40 * 266710 * 2
def baseEnd_266710 : Nat := 15216713928972969955381

theorem tailTrace_266710 : CollatzResearch.WordTrace tailWord_266710 prefixEnd_266710 15216713928972969955381 := by
  unfold tailWord_266710
  simp only [CollatzResearch.WordTrace]
  refine ⟨607982053985168455415849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6485141909175130191102389 607982053985168455415849)
  ·
    refine ⟨455986540488876341561887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 607982053985168455415849 455986540488876341561887)
    ·
      refine ⟨683979810733314512342831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455986540488876341561887 683979810733314512342831)
      ·
        refine ⟨1025969716099971768514247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683979810733314512342831 1025969716099971768514247)
        ·
          refine ⟨1538954574149957652771371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025969716099971768514247 1538954574149957652771371)
          ·
            refine ⟨2308431861224936479157057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538954574149957652771371 2308431861224936479157057)
            ·
              refine ⟨1731323895918702359367793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2308431861224936479157057 1731323895918702359367793)
              ·
                refine ⟨1298492921939026769525845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731323895918702359367793 1298492921939026769525845)
                ·
                  refine ⟨15216713928972969955381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1298492921939026769525845 15216713928972969955381)
                  ·
                    rfl

theorem cell23_266710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_266710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266710 prefixEnd_266710 := by exact prefixLift 266710
  have htrace : WordTrace (prefixWord ++ tailWord_266710) baseStart_266710 baseEnd_266710 := by
    simpa [prefixWord, tailWord_266710, baseEnd_266710] using wordTrace_append hprefix tailTrace_266710
  have hstable : (prefixWord ++ tailWord_266710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266710).length < 2 ^ (prefixWord ++ tailWord_266710).sum := by decide
  have hdescent : baseEnd_266710 < baseStart_266710 := by decide
  rcases family_descends (prefixWord ++ tailWord_266710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266720 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 5, 1, 3]
def baseStart_266720 : Nat := 118140960795 + 266720 * 2 ^ 59
def prefixEnd_266720 : Nat := 4983230072969 + 3 ^ 40 * 266720 * 2
def baseEnd_266720 : Nat := 136955560167301690473383

theorem tailTrace_266720 : CollatzResearch.WordTrace tailWord_266720 prefixEnd_266720 136955560167301690473383 := by
  unfold tailWord_266720
  simp only [CollatzResearch.WordTrace]
  refine ⟨4864038796863233497258807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6485385062484311329678409 4864038796863233497258807)
  ·
    refine ⟨7296058195294850245888211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4864038796863233497258807 7296058195294850245888211)
    ·
      refine ⟨10944087292942275368832317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7296058195294850245888211 10944087292942275368832317)
      ·
        refine ⟨4104032734853353263312119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10944087292942275368832317 4104032734853353263312119)
        ·
          refine ⟨6156049102280029894968179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4104032734853353263312119 6156049102280029894968179)
          ·
            refine ⟨9234073653420044842452269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6156049102280029894968179 9234073653420044842452269)
            ·
              refine ⟨3462777620032516815919601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9234073653420044842452269 3462777620032516815919601)
              ·
                refine ⟨2597083215024387611939701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3462777620032516815919601 2597083215024387611939701)
                ·
                  refine ⟨243476551408536338619347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2597083215024387611939701 243476551408536338619347)
                  ·
                    refine ⟨365214827112804507929021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243476551408536338619347 365214827112804507929021)
                    ·
                      refine ⟨136955560167301690473383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 365214827112804507929021 136955560167301690473383)
                      ·
                        rfl

theorem cell23_266720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_266720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266720 prefixEnd_266720 := by exact prefixLift 266720
  have htrace : WordTrace (prefixWord ++ tailWord_266720) baseStart_266720 baseEnd_266720 := by
    simpa [prefixWord, tailWord_266720, baseEnd_266720] using wordTrace_append hprefix tailTrace_266720
  have hstable : (prefixWord ++ tailWord_266720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266720).length < 2 ^ (prefixWord ++ tailWord_266720).sum := by decide
  have hdescent : baseEnd_266720 < baseStart_266720 := by decide
  rcases family_descends (prefixWord ++ tailWord_266720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266737 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 3, 1, 3]
def baseStart_266737 : Nat := 118140960795 + 266737 * 2 ^ 59
def prefixEnd_266737 : Nat := 4983230072969 + 3 ^ 40 * 266737 * 2
def baseEnd_266737 : Nat := 136964289338428123960805

theorem tailTrace_266737 : CollatzResearch.WordTrace tailWord_266737 prefixEnd_266737 136964289338428123960805 := by
  unfold tailWord_266737
  simp only [CollatzResearch.WordTrace]
  refine ⟨9728697634664878897886465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6485798423109919265257643 9728697634664878897886465)
  ·
    refine ⟨7296523225998659173414849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9728697634664878897886465 7296523225998659173414849)
    ·
      refine ⟨5472392419498994380061137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7296523225998659173414849 5472392419498994380061137)
      ·
        refine ⟨4104294314624245785045853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5472392419498994380061137 4104294314624245785045853)
        ·
          refine ⟨1539110367984092169392195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4104294314624245785045853 1539110367984092169392195)
          ·
            refine ⟨2308665551976138254088293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1539110367984092169392195 2308665551976138254088293)
            ·
              refine ⟨432874790995525922641555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2308665551976138254088293 432874790995525922641555)
              ·
                refine ⟨649312186493288883962333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432874790995525922641555 649312186493288883962333)
                ·
                  refine ⟨243492069934983331485875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649312186493288883962333 243492069934983331485875)
                  ·
                    refine ⟨365238104902474997228813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243492069934983331485875 365238104902474997228813)
                    ·
                      refine ⟨136964289338428123960805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 365238104902474997228813 136964289338428123960805)
                      ·
                        rfl

theorem cell23_266737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_266737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266737 prefixEnd_266737 := by exact prefixLift 266737
  have htrace : WordTrace (prefixWord ++ tailWord_266737) baseStart_266737 baseEnd_266737 := by
    simpa [prefixWord, tailWord_266737, baseEnd_266737] using wordTrace_append hprefix tailTrace_266737
  have hstable : (prefixWord ++ tailWord_266737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266737).length < 2 ^ (prefixWord ++ tailWord_266737).sum := by decide
  have hdescent : baseEnd_266737 < baseStart_266737 := by decide
  rcases family_descends (prefixWord ++ tailWord_266737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266760 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 1, 8, 2]
def baseStart_266760 : Nat := 118140960795 + 266760 * 2 ^ 59
def prefixEnd_266760 : Nat := 4983230072969 + 3 ^ 40 * 266760 * 2
def baseEnd_266760 : Nat := 136976099393481533973199

theorem tailTrace_266760 : CollatzResearch.WordTrace tailWord_266760 prefixEnd_266760 136976099393481533973199 := by
  unfold tailWord_266760
  simp only [CollatzResearch.WordTrace]
  refine ⟨4864768256790776912986867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6486357675721035883982489 4864768256790776912986867)
  ·
    refine ⟨7297152385186165369480301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4864768256790776912986867 7297152385186165369480301)
    ·
      refine ⟨2736432144444812013555113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7297152385186165369480301 2736432144444812013555113)
      ·
        refine ⟨2052324108333609010166335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2736432144444812013555113 2052324108333609010166335)
        ·
          refine ⟨3078486162500413515249503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2052324108333609010166335 3078486162500413515249503)
          ·
            refine ⟨4617729243750620272874255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3078486162500413515249503 4617729243750620272874255)
            ·
              refine ⟨6926593865625930409311383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4617729243750620272874255 6926593865625930409311383)
              ·
                refine ⟨10389890798438895613967075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6926593865625930409311383 10389890798438895613967075)
                ·
                  refine ⟨15584836197658343420950613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10389890798438895613967075 15584836197658343420950613)
                  ·
                    refine ⟨182634799191308711964265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15584836197658343420950613 182634799191308711964265)
                    ·
                      refine ⟨136976099393481533973199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182634799191308711964265 136976099393481533973199)
                      ·
                        rfl

theorem cell23_266760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_266760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266760 prefixEnd_266760 := by exact prefixLift 266760
  have htrace : WordTrace (prefixWord ++ tailWord_266760) baseStart_266760 baseEnd_266760 := by
    simpa [prefixWord, tailWord_266760, baseEnd_266760] using wordTrace_append hprefix tailTrace_266760
  have hstable : (prefixWord ++ tailWord_266760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266760).length < 2 ^ (prefixWord ++ tailWord_266760).sum := by decide
  have hdescent : baseEnd_266760 < baseStart_266760 := by decide
  rcases family_descends (prefixWord ++ tailWord_266760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266780 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_266780 : Nat := 118140960795 + 266780 * 2 ^ 59
def prefixEnd_266780 : Nat := 4983230072969 + 3 ^ 40 * 266780 * 2
def baseEnd_266780 : Nat := 136986369006571455723107

theorem tailTrace_266780 : CollatzResearch.WordTrace tailWord_266780 prefixEnd_266780 136986369006571455723107 := by
  unfold tailWord_266780
  simp only [CollatzResearch.WordTrace]
  refine ⟨4865132986754548620850897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6486843982339398161134529 4865132986754548620850897)
  ·
    refine ⟨3648849740065911465638173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4865132986754548620850897 3648849740065911465638173)
    ·
      refine ⟨1368318652524716799614315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3648849740065911465638173 1368318652524716799614315)
      ·
        refine ⟨2052477978787075199421473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1368318652524716799614315 2052477978787075199421473)
        ·
          refine ⟨1539358484090306399566105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2052477978787075199421473 1539358484090306399566105)
          ·
            refine ⟨1154518863067729799674579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1539358484090306399566105 1154518863067729799674579)
            ·
              refine ⟨1731778294601594699511869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154518863067729799674579 1731778294601594699511869)
              ·
                refine ⟨649416860475598012316951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1731778294601594699511869 649416860475598012316951)
                ·
                  refine ⟨974125290713397018475427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649416860475598012316951 974125290713397018475427)
                  ·
                    refine ⟨1461187936070095527713141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 974125290713397018475427 1461187936070095527713141)
                    ·
                      refine ⟨136986369006571455723107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1461187936070095527713141 136986369006571455723107)
                      ·
                        rfl

theorem cell23_266780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_266780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266780 prefixEnd_266780 := by exact prefixLift 266780
  have htrace : WordTrace (prefixWord ++ tailWord_266780) baseStart_266780 baseEnd_266780 := by
    simpa [prefixWord, tailWord_266780, baseEnd_266780] using wordTrace_append hprefix tailTrace_266780
  have hstable : (prefixWord ++ tailWord_266780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266780).length < 2 ^ (prefixWord ++ tailWord_266780).sum := by decide
  have hdescent : baseEnd_266780 < baseStart_266780 := by decide
  rcases family_descends (prefixWord ++ tailWord_266780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266788 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 3, 1, 3]
def baseStart_266788 : Nat := 118140960795 + 266788 * 2 ^ 59
def prefixEnd_266788 : Nat := 4983230072969 + 3 ^ 40 * 266788 * 2
def baseEnd_266788 : Nat := 136990476851807424423071

theorem tailTrace_266788 : CollatzResearch.WordTrace tailWord_266788 prefixEnd_266788 136990476851807424423071 := by
  unfold tailWord_266788
  simp only [CollatzResearch.WordTrace]
  refine ⟨4865278878740057303996509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6487038504986743071995345 4865278878740057303996509)
  ·
    refine ⟨1824479579527521488998691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4865278878740057303996509 1824479579527521488998691)
    ·
      refine ⟨2736719369291282233498037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1824479579527521488998691 2736719369291282233498037)
      ·
        refine ⟨256567440871057709390441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2736719369291282233498037 256567440871057709390441)
        ·
          refine ⟨192425580653293282042831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256567440871057709390441 192425580653293282042831)
          ·
            refine ⟨288638370979939923064247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192425580653293282042831 288638370979939923064247)
            ·
              refine ⟨432957556469909884596371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288638370979939923064247 432957556469909884596371)
              ·
                refine ⟨649436334704864826894557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432957556469909884596371 649436334704864826894557)
                ·
                  refine ⟨243538625514324310085459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649436334704864826894557 243538625514324310085459)
                  ·
                    refine ⟨365307938271486465128189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243538625514324310085459 365307938271486465128189)
                    ·
                      refine ⟨136990476851807424423071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 365307938271486465128189 136990476851807424423071)
                      ·
                        rfl

theorem cell23_266788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_266788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266788 prefixEnd_266788 := by exact prefixLift 266788
  have htrace : WordTrace (prefixWord ++ tailWord_266788) baseStart_266788 baseEnd_266788 := by
    simpa [prefixWord, tailWord_266788, baseEnd_266788] using wordTrace_append hprefix tailTrace_266788
  have hstable : (prefixWord ++ tailWord_266788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266788).length < 2 ^ (prefixWord ++ tailWord_266788).sum := by decide
  have hdescent : baseEnd_266788 < baseStart_266788 := by decide
  rcases family_descends (prefixWord ++ tailWord_266788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266803 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 6]
def baseStart_266803 : Nat := 118140960795 + 266803 * 2 ^ 59
def prefixEnd_266803 : Nat := 4983230072969 + 3 ^ 40 * 266803 * 2
def baseEnd_266803 : Nat := 136998179061624865735501

theorem tailTrace_266803 : CollatzResearch.WordTrace tailWord_266803 prefixEnd_266803 136998179061624865735501 := by
  unfold tailWord_266803
  simp only [CollatzResearch.WordTrace]
  refine ⟨9731104852425772169789063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6487403234950514779859375 9731104852425772169789063)
  ·
    refine ⟨14596657278638658254683595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9731104852425772169789063 14596657278638658254683595)
    ·
      refine ⟨21894985917957987382025393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14596657278638658254683595 21894985917957987382025393)
      ·
        refine ⟨16421239438468490536519045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21894985917957987382025393 16421239438468490536519045)
        ·
          refine ⟨3078982394712841975597321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16421239438468490536519045 3078982394712841975597321)
          ·
            refine ⟨2309236796034631481697991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3078982394712841975597321 2309236796034631481697991)
            ·
              refine ⟨3463855194051947222546987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2309236796034631481697991 3463855194051947222546987)
              ·
                refine ⟨5195782791077920833820481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3463855194051947222546987 5195782791077920833820481)
                ·
                  refine ⟨3896837093308440625365361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5195782791077920833820481 3896837093308440625365361)
                  ·
                    refine ⟨2922627819981330469024021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3896837093308440625365361 2922627819981330469024021)
                    ·
                      refine ⟨136998179061624865735501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2922627819981330469024021 136998179061624865735501)
                      ·
                        rfl

theorem cell23_266803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_266803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266803 prefixEnd_266803 := by exact prefixLift 266803
  have htrace : WordTrace (prefixWord ++ tailWord_266803) baseStart_266803 baseEnd_266803 := by
    simpa [prefixWord, tailWord_266803, baseEnd_266803] using wordTrace_append hprefix tailTrace_266803
  have hstable : (prefixWord ++ tailWord_266803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266803).length < 2 ^ (prefixWord ++ tailWord_266803).sum := by decide
  have hdescent : baseEnd_266803 < baseStart_266803 := by decide
  rcases family_descends (prefixWord ++ tailWord_266803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266882 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_266882 : Nat := 118140960795 + 266882 * 2 ^ 59
def prefixEnd_266882 : Nat := 4983230072969 + 3 ^ 40 * 266882 * 2
def baseEnd_266882 : Nat := 137038744033330056647639

theorem tailTrace_266882 : CollatzResearch.WordTrace tailWord_266882 prefixEnd_266882 137038744033330056647639 := by
  unfold tailWord_266882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2433496554784892165478725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6489324146093045774609933 2433496554784892165478725)
  ·
    refine ⟨456280604022167281027261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2433496554784892165478725 456280604022167281027261)
    ·
      refine ⟨171105226508312730385223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 456280604022167281027261 171105226508312730385223)
      ·
        refine ⟨256657839762469095577835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171105226508312730385223 256657839762469095577835)
        ·
          refine ⟨384986759643703643366753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256657839762469095577835 384986759643703643366753)
          ·
            refine ⟨288740069732777732525065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384986759643703643366753 288740069732777732525065)
            ·
              refine ⟨216555052299583299393799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288740069732777732525065 216555052299583299393799)
              ·
                refine ⟨324832578449374949090699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216555052299583299393799 324832578449374949090699)
                ·
                  refine ⟨487248867674062423636049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324832578449374949090699 487248867674062423636049)
                  ·
                    refine ⟨365436650755546817727037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 487248867674062423636049 365436650755546817727037)
                    ·
                      refine ⟨137038744033330056647639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 365436650755546817727037 137038744033330056647639)
                      ·
                        rfl

theorem cell23_266882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_266882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266882 prefixEnd_266882 := by exact prefixLift 266882
  have htrace : WordTrace (prefixWord ++ tailWord_266882) baseStart_266882 baseEnd_266882 := by
    simpa [prefixWord, tailWord_266882, baseEnd_266882] using wordTrace_append hprefix tailTrace_266882
  have hstable : (prefixWord ++ tailWord_266882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266882).length < 2 ^ (prefixWord ++ tailWord_266882).sum := by decide
  have hdescent : baseEnd_266882 < baseStart_266882 := by decide
  rcases family_descends (prefixWord ++ tailWord_266882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266884 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_266884 : Nat := 118140960795 + 266884 * 2 ^ 59
def prefixEnd_266884 : Nat := 4983230072969 + 3 ^ 40 * 266884 * 2
def baseEnd_266884 : Nat := 137039770994639048822629

theorem tailTrace_266884 : CollatzResearch.WordTrace tailWord_266884 prefixEnd_266884 137039770994639048822629 := by
  unfold tailWord_266884
  simp only [CollatzResearch.WordTrace]
  refine ⟨4867029582566161501743853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6489372776754882002325137 4867029582566161501743853)
  ·
    refine ⟨1825136093462310563153945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4867029582566161501743853 1825136093462310563153945)
    ·
      refine ⟨1368852070096732922365459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1825136093462310563153945 1368852070096732922365459)
      ·
        refine ⟨2053278105145099383548189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1368852070096732922365459 2053278105145099383548189)
        ·
          refine ⟨769979289429412268830571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2053278105145099383548189 769979289429412268830571)
          ·
            refine ⟨1154968934144118403245857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769979289429412268830571 1154968934144118403245857)
            ·
              refine ⟨866226700608088802434393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1154968934144118403245857 866226700608088802434393)
              ·
                refine ⟨649670025456066601825795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866226700608088802434393 649670025456066601825795)
                ·
                  refine ⟨974505038184099902738693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 649670025456066601825795 974505038184099902738693)
                  ·
                    refine ⟨182719694659518731763505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 974505038184099902738693 182719694659518731763505)
                    ·
                      refine ⟨137039770994639048822629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182719694659518731763505 137039770994639048822629)
                      ·
                        rfl

theorem cell23_266884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_266884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266884 prefixEnd_266884 := by exact prefixLift 266884
  have htrace : WordTrace (prefixWord ++ tailWord_266884) baseStart_266884 baseEnd_266884 := by
    simpa [prefixWord, tailWord_266884, baseEnd_266884] using wordTrace_append hprefix tailTrace_266884
  have hstable : (prefixWord ++ tailWord_266884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266884).length < 2 ^ (prefixWord ++ tailWord_266884).sum := by decide
  have hdescent : baseEnd_266884 < baseStart_266884 := by decide
  rcases family_descends (prefixWord ++ tailWord_266884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266930 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_266930 : Nat := 118140960795 + 266930 * 2 ^ 59
def prefixEnd_266930 : Nat := 4983230072969 + 3 ^ 40 * 266930 * 2
def baseEnd_266930 : Nat := 137063391104745868847417

theorem tailTrace_266930 : CollatzResearch.WordTrace tailWord_266930 prefixEnd_266930 137063391104745868847417 := by
  unfold tailWord_266930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2433934230741418214915561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6490491281977115239774829 2433934230741418214915561)
  ·
    refine ⟨1825450673056063661186671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2433934230741418214915561 1825450673056063661186671)
    ·
      refine ⟨2738176009584095491780007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1825450673056063661186671 2738176009584095491780007)
      ·
        refine ⟨4107264014376143237670011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2738176009584095491780007 4107264014376143237670011)
        ·
          refine ⟨6160896021564214856505017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4107264014376143237670011 6160896021564214856505017)
          ·
            refine ⟨4620672016173161142378763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6160896021564214856505017 4620672016173161142378763)
            ·
              refine ⟨6931008024259741713568145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4620672016173161142378763 6931008024259741713568145)
              ·
                refine ⟨5198256018194806285176109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6931008024259741713568145 5198256018194806285176109)
                ·
                  refine ⟨1949346006823052356941041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5198256018194806285176109 1949346006823052356941041)
                  ·
                    refine ⟨1462009505117289267705781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1949346006823052356941041 1462009505117289267705781)
                    ·
                      refine ⟨137063391104745868847417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1462009505117289267705781 137063391104745868847417)
                      ·
                        rfl

theorem cell23_266930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_266930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266930 prefixEnd_266930 := by exact prefixLift 266930
  have htrace : WordTrace (prefixWord ++ tailWord_266930) baseStart_266930 baseEnd_266930 := by
    simpa [prefixWord, tailWord_266930, baseEnd_266930] using wordTrace_append hprefix tailTrace_266930
  have hstable : (prefixWord ++ tailWord_266930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266930).length < 2 ^ (prefixWord ++ tailWord_266930).sum := by decide
  have hdescent : baseEnd_266930 < baseStart_266930 := by decide
  rcases family_descends (prefixWord ++ tailWord_266930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266964 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_266964 : Nat := 118140960795 + 266964 * 2 ^ 59
def prefixEnd_266964 : Nat := 4983230072969 + 3 ^ 40 * 266964 * 2
def baseEnd_266964 : Nat := 137080849446998735822261

theorem tailTrace_266964 : CollatzResearch.WordTrace tailWord_266964 prefixEnd_266964 137080849446998735822261 := by
  unfold tailWord_266964
  simp only [CollatzResearch.WordTrace]
  refine ⟨4868488502421248333199973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6491318003228331110933297 4868488502421248333199973)
  ·
    refine ⟨912841594203984062474995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4868488502421248333199973 912841594203984062474995)
    ·
      refine ⟨1369262391305976093712493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 912841594203984062474995 1369262391305976093712493)
      ·
        refine ⟨513473396739741035142185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1369262391305976093712493 513473396739741035142185)
        ·
          refine ⟨385105047554805776356639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513473396739741035142185 385105047554805776356639)
          ·
            refine ⟨577657571332208664534959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385105047554805776356639 577657571332208664534959)
            ·
              refine ⟨866486356998312996802439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577657571332208664534959 866486356998312996802439)
              ·
                refine ⟨1299729535497469495203659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866486356998312996802439 1299729535497469495203659)
                ·
                  refine ⟨1949594303246204242805489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1299729535497469495203659 1949594303246204242805489)
                  ·
                    refine ⟨1462195727434653182104117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1949594303246204242805489 1462195727434653182104117)
                    ·
                      refine ⟨137080849446998735822261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1462195727434653182104117 137080849446998735822261)
                      ·
                        rfl

theorem cell23_266964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_266964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266964 prefixEnd_266964 := by exact prefixLift 266964
  have htrace : WordTrace (prefixWord ++ tailWord_266964) baseStart_266964 baseEnd_266964 := by
    simpa [prefixWord, tailWord_266964, baseEnd_266964] using wordTrace_append hprefix tailTrace_266964
  have hstable : (prefixWord ++ tailWord_266964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266964).length < 2 ^ (prefixWord ++ tailWord_266964).sum := by decide
  have hdescent : baseEnd_266964 < baseStart_266964 := by decide
  rcases family_descends (prefixWord ++ tailWord_266964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266994 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_266994 : Nat := 118140960795 + 266994 * 2 ^ 59
def prefixEnd_266994 : Nat := 4983230072969 + 3 ^ 40 * 266994 * 2
def baseEnd_266994 : Nat := 137096253866633618447123

theorem tailTrace_266994 : CollatzResearch.WordTrace tailWord_266994 prefixEnd_266994 137096253866633618447123 := by
  unfold tailWord_266994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2434517798683452947498009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6492047463155874526661357 2434517798683452947498009)
  ·
    refine ⟨1825888349012589710623507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2434517798683452947498009 1825888349012589710623507)
    ·
      refine ⟨2738832523518884565935261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1825888349012589710623507 2738832523518884565935261)
      ·
        refine ⟨1027062196319581712225723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2738832523518884565935261 1027062196319581712225723)
        ·
          refine ⟨1540593294479372568338585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027062196319581712225723 1540593294479372568338585)
          ·
            refine ⟨1155444970859529426253939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1540593294479372568338585 1155444970859529426253939)
            ·
              refine ⟨1733167456289294139380909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155444970859529426253939 1733167456289294139380909)
              ·
                refine ⟨649937796108485302267841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1733167456289294139380909 649937796108485302267841)
                ·
                  refine ⟨487453347081363976700881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 649937796108485302267841 487453347081363976700881)
                  ·
                    refine ⟨365590010311022982525661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 487453347081363976700881 365590010311022982525661)
                    ·
                      refine ⟨137096253866633618447123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 365590010311022982525661 137096253866633618447123)
                      ·
                        rfl

theorem cell23_266994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_266994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_266994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_266994 prefixEnd_266994 := by exact prefixLift 266994
  have htrace : WordTrace (prefixWord ++ tailWord_266994) baseStart_266994 baseEnd_266994 := by
    simpa [prefixWord, tailWord_266994, baseEnd_266994] using wordTrace_append hprefix tailTrace_266994
  have hstable : (prefixWord ++ tailWord_266994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266994).length < 2 ^ (prefixWord ++ tailWord_266994).sum := by decide
  have hdescent : baseEnd_266994 < baseStart_266994 := by decide
  rcases family_descends (prefixWord ++ tailWord_266994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
