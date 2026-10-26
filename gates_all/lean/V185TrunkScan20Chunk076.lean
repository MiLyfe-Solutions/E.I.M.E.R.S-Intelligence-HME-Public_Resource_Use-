import V185TrunkScan20Chunk075

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_462868 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 4]
def baseStart_462868 : Nat := 118140960795 + 462868 * 2 ^ 59
def prefixEnd_462868 : Nat := 4983230072969 + 3 ^ 40 * 462868 * 2
def baseEnd_462868 : Nat := 211265567631466898241169

theorem tailTrace_462868 : CollatzResearch.WordTrace tailWord_462868 prefixEnd_462868 211265567631466898241169 := by
  unfold tailWord_462868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8441091443557881202946629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11254788591410508270595505 8441091443557881202946629)
  ·
    refine ⟨1582704645667102725552493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8441091443557881202946629 1582704645667102725552493)
    ·
      refine ⟨593514242125163522082185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1582704645667102725552493 593514242125163522082185)
      ·
        refine ⟨445135681593872641561639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593514242125163522082185 445135681593872641561639)
        ·
          refine ⟨667703522390808962342459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445135681593872641561639 667703522390808962342459)
          ·
            refine ⟨1001555283586213443513689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667703522390808962342459 1001555283586213443513689)
            ·
              refine ⟨751166462689660082635267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001555283586213443513689 751166462689660082635267)
              ·
                refine ⟨1126749694034490123952901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751166462689660082635267 1126749694034490123952901)
                ·
                  refine ⟨211265567631466898241169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1126749694034490123952901 211265567631466898241169)
                  ·
                    rfl

theorem cell20_462868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_462868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462868 prefixEnd_462868 := by exact prefixLift 462868
  have htrace : WordTrace (prefixWord ++ tailWord_462868) baseStart_462868 baseEnd_462868 := by
    simpa [prefixWord, tailWord_462868, baseEnd_462868] using wordTrace_append hprefix tailTrace_462868
  have hstable : (prefixWord ++ tailWord_462868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462868).length < 2 ^ (prefixWord ++ tailWord_462868).sum := by decide
  have hdescent : baseEnd_462868 < baseStart_462868 := by decide
  rcases family_descends (prefixWord ++ tailWord_462868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462872 : List Nat := [2, 1, 2, 3, 2, 1, 1, 6, 2]
def baseStart_462872 : Nat := 118140960795 + 462872 * 2 ^ 59
def prefixEnd_462872 : Nat := 4983230072969 + 3 ^ 40 * 462872 * 2
def baseEnd_462872 : Nat := 211267393340460662107819

theorem tailTrace_462872 : CollatzResearch.WordTrace tailWord_462872 prefixEnd_462872 211267393340460662107819 := by
  unfold tailWord_462872
  simp only [CollatzResearch.WordTrace]
  refine ⟨8441164389550635544519435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11254885852734180726025913 8441164389550635544519435)
  ·
    refine ⟨12661746584325953316779153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8441164389550635544519435 12661746584325953316779153)
    ·
      refine ⟨9496309938244464987584365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12661746584325953316779153 9496309938244464987584365)
      ·
        refine ⟨3561116226841674370344137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9496309938244464987584365 3561116226841674370344137)
        ·
          refine ⟨2670837170131255777758103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3561116226841674370344137 2670837170131255777758103)
          ·
            refine ⟨4006255755196883666637155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670837170131255777758103 4006255755196883666637155)
            ·
              refine ⟨6009383632795325499955733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4006255755196883666637155 6009383632795325499955733)
              ·
                refine ⟨281689857787280882810425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6009383632795325499955733 281689857787280882810425)
                ·
                  refine ⟨211267393340460662107819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281689857787280882810425 211267393340460662107819)
                  ·
                    rfl

theorem cell20_462872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 2].length) (baseStart_462872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462872 prefixEnd_462872 := by exact prefixLift 462872
  have htrace : WordTrace (prefixWord ++ tailWord_462872) baseStart_462872 baseEnd_462872 := by
    simpa [prefixWord, tailWord_462872, baseEnd_462872] using wordTrace_append hprefix tailTrace_462872
  have hstable : (prefixWord ++ tailWord_462872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462872).length < 2 ^ (prefixWord ++ tailWord_462872).sum := by decide
  have hdescent : baseEnd_462872 < baseStart_462872 := by decide
  rcases family_descends (prefixWord ++ tailWord_462872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462934 : List Nat := [5, 2, 2, 1, 1, 1, 1, 7]
def baseStart_462934 : Nat := 118140960795 + 462934 * 2 ^ 59
def prefixEnd_462934 : Nat := 4983230072969 + 3 ^ 40 * 462934 * 2
def baseEnd_462934 : Nat := 70431897276621334013633

theorem tailTrace_462934 : CollatzResearch.WordTrace tailWord_462934 prefixEnd_462934 70431897276621334013633 := by
  unfold tailWord_462934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055286881554790979862241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11256393403251103785197237 1055286881554790979862241)
  ·
    refine ⟨791465161166093234896681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1055286881554790979862241 791465161166093234896681)
    ·
      refine ⟨593598870874569926172511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 791465161166093234896681 593598870874569926172511)
      ·
        refine ⟨890398306311854889258767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593598870874569926172511 890398306311854889258767)
        ·
          refine ⟨1335597459467782333888151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890398306311854889258767 1335597459467782333888151)
          ·
            refine ⟨2003396189201673500832227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335597459467782333888151 2003396189201673500832227)
            ·
              refine ⟨3005094283802510251248341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003396189201673500832227 3005094283802510251248341)
              ·
                refine ⟨70431897276621334013633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3005094283802510251248341 70431897276621334013633)
                ·
                  rfl

theorem cell20_462934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_462934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462934 prefixEnd_462934 := by exact prefixLift 462934
  have htrace : WordTrace (prefixWord ++ tailWord_462934) baseStart_462934 baseEnd_462934 := by
    simpa [prefixWord, tailWord_462934, baseEnd_462934] using wordTrace_append hprefix tailTrace_462934
  have hstable : (prefixWord ++ tailWord_462934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462934).length < 2 ^ (prefixWord ++ tailWord_462934).sum := by decide
  have hdescent : baseEnd_462934 < baseStart_462934 := by decide
  rcases family_descends (prefixWord ++ tailWord_462934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462938 : List Nat := [3, 1, 1, 2, 1, 1, 6, 5]
def baseStart_462938 : Nat := 118140960795 + 462938 * 2 ^ 59
def prefixEnd_462938 : Nat := 4983230072969 + 3 ^ 40 * 462938 * 2
def baseEnd_462938 : Nat := 70432505846285921969183

theorem tailTrace_462938 : CollatzResearch.WordTrace tailWord_462938 prefixEnd_462938 70432505846285921969183 := by
  unfold tailWord_462938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4221183999215541090235367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11256490664574776240627645 4221183999215541090235367)
  ·
    refine ⟨6331775998823311635353051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4221183999215541090235367 6331775998823311635353051)
    ·
      refine ⟨9497663998234967453029577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6331775998823311635353051 9497663998234967453029577)
      ·
        refine ⟨7123247998676225589772183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9497663998234967453029577 7123247998676225589772183)
        ·
          refine ⟨10684871998014338384658275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7123247998676225589772183 10684871998014338384658275)
          ·
            refine ⟨16027307997021507576987413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10684871998014338384658275 16027307997021507576987413)
            ·
              refine ⟨751280062360383167671285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16027307997021507576987413 751280062360383167671285)
              ·
                refine ⟨70432505846285921969183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 751280062360383167671285 70432505846285921969183)
                ·
                  rfl

theorem cell20_462938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_462938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462938 prefixEnd_462938 := by exact prefixLift 462938
  have htrace : WordTrace (prefixWord ++ tailWord_462938) baseStart_462938 baseEnd_462938 := by
    simpa [prefixWord, tailWord_462938, baseEnd_462938] using wordTrace_append hprefix tailTrace_462938
  have hstable : (prefixWord ++ tailWord_462938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462938).length < 2 ^ (prefixWord ++ tailWord_462938).sum := by decide
  have hdescent : baseEnd_462938 < baseStart_462938 := by decide
  rcases family_descends (prefixWord ++ tailWord_462938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462983 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_462983 : Nat := 118140960795 + 462983 * 2 ^ 59
def prefixEnd_462983 : Nat := 4983230072969 + 3 ^ 40 * 462983 * 2
def baseEnd_462983 : Nat := 211318056765037609407365

theorem tailTrace_462983 : CollatzResearch.WordTrace tailWord_462983 prefixEnd_462983 211318056765037609407365 := by
  unfold tailWord_462983
  simp only [CollatzResearch.WordTrace]
  refine ⟨16886377281699137046329603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11257584854466091364219735 16886377281699137046329603)
  ·
    refine ⟨25329565922548705569494405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16886377281699137046329603 25329565922548705569494405)
    ·
      refine ⟨4749293610477882294280201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25329565922548705569494405 4749293610477882294280201)
      ·
        refine ⟨3561970207858411720710151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4749293610477882294280201 3561970207858411720710151)
        ·
          refine ⟨5342955311787617581065227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561970207858411720710151 5342955311787617581065227)
          ·
            refine ⟨8014432967681426371597841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342955311787617581065227 8014432967681426371597841)
            ·
              refine ⟨6010824725761069778698381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8014432967681426371597841 6010824725761069778698381)
              ·
                refine ⟨2254059272160401167011893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6010824725761069778698381 2254059272160401167011893)
                ·
                  refine ⟨211318056765037609407365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2254059272160401167011893 211318056765037609407365)
                  ·
                    rfl

theorem cell20_462983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_462983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_462983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_462983 prefixEnd_462983 := by exact prefixLift 462983
  have htrace : WordTrace (prefixWord ++ tailWord_462983) baseStart_462983 baseEnd_462983 := by
    simpa [prefixWord, tailWord_462983, baseEnd_462983] using wordTrace_append hprefix tailTrace_462983
  have hstable : (prefixWord ++ tailWord_462983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462983).length < 2 ^ (prefixWord ++ tailWord_462983).sum := by decide
  have hdescent : baseEnd_462983 < baseStart_462983 := by decide
  rcases family_descends (prefixWord ++ tailWord_462983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463007 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 6]
def baseStart_463007 : Nat := 118140960795 + 463007 * 2 ^ 59
def prefixEnd_463007 : Nat := 4983230072969 + 3 ^ 40 * 463007 * 2
def baseEnd_463007 : Nat := 211329011019000192607267

theorem tailTrace_463007 : CollatzResearch.WordTrace tailWord_463007 prefixEnd_463007 211329011019000192607267 := by
  unfold tailWord_463007
  simp only [CollatzResearch.WordTrace]
  refine ⟨16887252633612189145203275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11258168422408126096802183 16887252633612189145203275)
  ·
    refine ⟨25330878950418283717804913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16887252633612189145203275 25330878950418283717804913)
    ·
      refine ⟨18998159212813712788353685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25330878950418283717804913 18998159212813712788353685)
      ·
        refine ⟨890538713100642786954079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18998159212813712788353685 890538713100642786954079)
        ·
          refine ⟨1335808069650964180431119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890538713100642786954079 1335808069650964180431119)
          ·
            refine ⟨2003712104476446270646679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335808069650964180431119 2003712104476446270646679)
            ·
              refine ⟨3005568156714669405970019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003712104476446270646679 3005568156714669405970019)
              ·
                refine ⟨4508352235072004108955029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005568156714669405970019 4508352235072004108955029)
                ·
                  refine ⟨211329011019000192607267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4508352235072004108955029 211329011019000192607267)
                  ·
                    rfl

theorem cell20_463007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_463007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463007 prefixEnd_463007 := by exact prefixLift 463007
  have htrace : WordTrace (prefixWord ++ tailWord_463007) baseStart_463007 baseEnd_463007 := by
    simpa [prefixWord, tailWord_463007, baseEnd_463007] using wordTrace_append hprefix tailTrace_463007
  have hstable : (prefixWord ++ tailWord_463007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463007).length < 2 ^ (prefixWord ++ tailWord_463007).sum := by decide
  have hdescent : baseEnd_463007 < baseStart_463007 := by decide
  rcases family_descends (prefixWord ++ tailWord_463007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463010 : List Nat := [3, 3, 1, 3, 1, 2, 3, 4]
def baseStart_463010 : Nat := 118140960795 + 463010 * 2 ^ 59
def prefixEnd_463010 : Nat := 4983230072969 + 3 ^ 40 * 463010 * 2
def baseEnd_463010 : Nat := 70443460100248505169085

theorem tailTrace_463010 : CollatzResearch.WordTrace tailWord_463010 prefixEnd_463010 70443460100248505169085 := by
  unfold tailWord_463010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4221840513150330164390621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11258241368400880438374989 4221840513150330164390621)
  ·
    refine ⟨1583190192431373811646483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4221840513150330164390621 1583190192431373811646483)
    ·
      refine ⟨2374785288647060717469725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583190192431373811646483 2374785288647060717469725)
      ·
        refine ⟨890544483242647769051147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2374785288647060717469725 890544483242647769051147)
        ·
          refine ⟨1335816724863971653576721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890544483242647769051147 1335816724863971653576721)
          ·
            refine ⟨1001862543647978740182541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335816724863971653576721 1001862543647978740182541)
            ·
              refine ⟨375698453867992027568453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1001862543647978740182541 375698453867992027568453)
              ·
                refine ⟨70443460100248505169085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375698453867992027568453 70443460100248505169085)
                ·
                  rfl

theorem cell20_463010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_463010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463010 prefixEnd_463010 := by exact prefixLift 463010
  have htrace : WordTrace (prefixWord ++ tailWord_463010) baseStart_463010 baseEnd_463010 := by
    simpa [prefixWord, tailWord_463010, baseEnd_463010] using wordTrace_append hprefix tailTrace_463010
  have hstable : (prefixWord ++ tailWord_463010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463010).length < 2 ^ (prefixWord ++ tailWord_463010).sum := by decide
  have hdescent : baseEnd_463010 < baseStart_463010 := by decide
  rcases family_descends (prefixWord ++ tailWord_463010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463035 : List Nat := [1, 1, 1, 1, 1, 2, 13]
def baseStart_463035 : Nat := 118140960795 + 463035 * 2 ^ 59
def prefixEnd_463035 : Nat := 4983230072969 + 3 ^ 40 * 463035 * 2
def baseEnd_463035 : Nat := 23482421220217393297091

theorem tailTrace_463035 : CollatzResearch.WordTrace tailWord_463035 prefixEnd_463035 23482421220217393297091 := by
  unfold tailWord_463035
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888273877510749927222559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11258849251673833284815039 16888273877510749927222559)
  ·
    refine ⟨25332410816266124890833839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16888273877510749927222559 25332410816266124890833839)
    ·
      refine ⟨37998616224399187336250759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25332410816266124890833839 37998616224399187336250759)
      ·
        refine ⟨56997924336598781004376139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37998616224399187336250759 56997924336598781004376139)
        ·
          refine ⟨85496886504898171506564209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56997924336598781004376139 85496886504898171506564209)
          ·
            refine ⟨64122664878673628629923157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85496886504898171506564209 64122664878673628629923157)
            ·
              refine ⟨23482421220217393297091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 64122664878673628629923157 23482421220217393297091)
              ·
                rfl

theorem cell20_463035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 13].length) (baseStart_463035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463035 prefixEnd_463035 := by exact prefixLift 463035
  have htrace : WordTrace (prefixWord ++ tailWord_463035) baseStart_463035 baseEnd_463035 := by
    simpa [prefixWord, tailWord_463035, baseEnd_463035] using wordTrace_append hprefix tailTrace_463035
  have hstable : (prefixWord ++ tailWord_463035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463035).length < 2 ^ (prefixWord ++ tailWord_463035).sum := by decide
  have hdescent : baseEnd_463035 < baseStart_463035 := by decide
  rcases family_descends (prefixWord ++ tailWord_463035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463041 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 4]
def baseStart_463041 : Nat := 118140960795 + 463041 * 2 ^ 59
def prefixEnd_463041 : Nat := 4983230072969 + 3 ^ 40 * 463041 * 2
def baseEnd_463041 : Nat := 211344529545447185473795

theorem tailTrace_463041 : CollatzResearch.WordTrace tailWord_463041 prefixEnd_463041 211344529545447185473795 := by
  unfold tailWord_463041
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888492715489012951940977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11258995143659341967960651 16888492715489012951940977)
  ·
    refine ⟨12666369536616759713955733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16888492715489012951940977 12666369536616759713955733)
    ·
      refine ⟨593736072028910611591675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12666369536616759713955733 593736072028910611591675)
      ·
        refine ⟨890604108043365917387513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593736072028910611591675 890604108043365917387513)
        ·
          refine ⟨667953081032524438040635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890604108043365917387513 667953081032524438040635)
          ·
            refine ⟨1001929621548786657060953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667953081032524438040635 1001929621548786657060953)
            ·
              refine ⟨751447216161589992795715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001929621548786657060953 751447216161589992795715)
              ·
                refine ⟨1127170824242384989193573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751447216161589992795715 1127170824242384989193573)
                ·
                  refine ⟨211344529545447185473795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1127170824242384989193573 211344529545447185473795)
                  ·
                    rfl

theorem cell20_463041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_463041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463041 prefixEnd_463041 := by exact prefixLift 463041
  have htrace : WordTrace (prefixWord ++ tailWord_463041) baseStart_463041 baseEnd_463041 := by
    simpa [prefixWord, tailWord_463041, baseEnd_463041] using wordTrace_append hprefix tailTrace_463041
  have hstable : (prefixWord ++ tailWord_463041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463041).length < 2 ^ (prefixWord ++ tailWord_463041).sum := by decide
  have hdescent : baseEnd_463041 < baseStart_463041 := by decide
  rcases family_descends (prefixWord ++ tailWord_463041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463069 : List Nat := [1, 4, 3, 2, 1, 2, 1, 6]
def baseStart_463069 : Nat := 118140960795 + 463069 * 2 ^ 59
def prefixEnd_463069 : Nat := 4983230072969 + 3 ^ 40 * 463069 * 2
def baseEnd_463069 : Nat := 70452436502801177513449

theorem tailTrace_463069 : CollatzResearch.WordTrace tailWord_463069 prefixEnd_463069 70452436502801177513449 := by
  unfold tailWord_463069
  simp only [CollatzResearch.WordTrace]
  refine ⟨16889513959387573733960261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11259675972925049155973507 16889513959387573733960261)
  ·
    refine ⟨3166783867385170075117549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16889513959387573733960261 3166783867385170075117549)
    ·
      refine ⟨1187543950269438778169081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3166783867385170075117549 1187543950269438778169081)
      ·
        refine ⟨890657962702079083626811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1187543950269438778169081 890657962702079083626811)
        ·
          refine ⟨1335986944053118625440217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890657962702079083626811 1335986944053118625440217)
          ·
            refine ⟨1001990208039838969080163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335986944053118625440217 1001990208039838969080163)
            ·
              refine ⟨1502985312059758453620245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001990208039838969080163 1502985312059758453620245)
              ·
                refine ⟨70452436502801177513449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1502985312059758453620245 70452436502801177513449)
                ·
                  rfl

theorem cell20_463069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_463069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463069 prefixEnd_463069 := by exact prefixLift 463069
  have htrace : WordTrace (prefixWord ++ tailWord_463069) baseStart_463069 baseEnd_463069 := by
    simpa [prefixWord, tailWord_463069, baseEnd_463069] using wordTrace_append hprefix tailTrace_463069
  have hstable : (prefixWord ++ tailWord_463069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463069).length < 2 ^ (prefixWord ++ tailWord_463069).sum := by decide
  have hdescent : baseEnd_463069 < baseStart_463069 := by decide
  rcases family_descends (prefixWord ++ tailWord_463069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463075 : List Nat := [1, 1, 1, 8, 2, 1, 1, 3, 2]
def baseStart_463075 : Nat := 118140960795 + 463075 * 2 ^ 59
def prefixEnd_463075 : Nat := 4983230072969 + 3 ^ 40 * 463075 * 2
def baseEnd_463075 : Nat := 211360048071894178340323

theorem tailTrace_463075 : CollatzResearch.WordTrace tailWord_463075 prefixEnd_463075 211360048071894178340323 := by
  unfold tailWord_463075
  simp only [CollatzResearch.WordTrace]
  refine ⟨16889732797365836758678679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11259821864910557839119119 16889732797365836758678679)
  ·
    refine ⟨25334599196048755138018019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16889732797365836758678679 25334599196048755138018019)
    ·
      refine ⟨38001898794073132707027029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25334599196048755138018019 38001898794073132707027029)
      ·
        refine ⟨445334751493044523910473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 38001898794073132707027029 445334751493044523910473)
        ·
          refine ⟨334001063619783392932855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445334751493044523910473 334001063619783392932855)
          ·
            refine ⟨501001595429675089399283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334001063619783392932855 501001595429675089399283)
            ·
              refine ⟨751502393144512634098925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501001595429675089399283 751502393144512634098925)
              ·
                refine ⟨281813397429192237787097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 751502393144512634098925 281813397429192237787097)
                ·
                  refine ⟨211360048071894178340323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281813397429192237787097 211360048071894178340323)
                  ·
                    rfl

theorem cell20_463075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 2].length) (baseStart_463075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463075 prefixEnd_463075 := by exact prefixLift 463075
  have htrace : WordTrace (prefixWord ++ tailWord_463075) baseStart_463075 baseEnd_463075 := by
    simpa [prefixWord, tailWord_463075, baseEnd_463075] using wordTrace_append hprefix tailTrace_463075
  have hstable : (prefixWord ++ tailWord_463075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463075).length < 2 ^ (prefixWord ++ tailWord_463075).sum := by decide
  have hdescent : baseEnd_463075 < baseStart_463075 := by decide
  rcases family_descends (prefixWord ++ tailWord_463075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463079 : List Nat := [1, 1, 5, 3, 1, 1, 3, 3, 2]
def baseStart_463079 : Nat := 118140960795 + 463079 * 2 ^ 59
def prefixEnd_463079 : Nat := 4983230072969 + 3 ^ 40 * 463079 * 2
def baseEnd_463079 : Nat := 211361873780887942206973

theorem tailTrace_463079 : CollatzResearch.WordTrace tailWord_463079 prefixEnd_463079 211361873780887942206973 := by
  unfold tailWord_463079
  simp only [CollatzResearch.WordTrace]
  refine ⟨16889878689351345441824291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11259919126234230294549527 16889878689351345441824291)
  ·
    refine ⟨25334818034027018162736437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16889878689351345441824291 25334818034027018162736437)
    ·
      refine ⟨2375139190690032952756541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25334818034027018162736437 2375139190690032952756541)
      ·
        refine ⟨890677196508762357283703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2375139190690032952756541 890677196508762357283703)
        ·
          refine ⟨1336015794763143535925555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890677196508762357283703 1336015794763143535925555)
          ·
            refine ⟨2004023692144715303888333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336015794763143535925555 2004023692144715303888333)
            ·
              refine ⟨751508884554268238958125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2004023692144715303888333 751508884554268238958125)
              ·
                refine ⟨281815831707850589609297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 751508884554268238958125 281815831707850589609297)
                ·
                  refine ⟨211361873780887942206973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281815831707850589609297 211361873780887942206973)
                  ·
                    rfl

theorem cell20_463079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 2].length) (baseStart_463079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463079 prefixEnd_463079 := by exact prefixLift 463079
  have htrace : WordTrace (prefixWord ++ tailWord_463079) baseStart_463079 baseEnd_463079 := by
    simpa [prefixWord, tailWord_463079, baseEnd_463079] using wordTrace_append hprefix tailTrace_463079
  have hstable : (prefixWord ++ tailWord_463079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463079).length < 2 ^ (prefixWord ++ tailWord_463079).sum := by decide
  have hdescent : baseEnd_463079 < baseStart_463079 := by decide
  rcases family_descends (prefixWord ++ tailWord_463079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463090 : List Nat := [3, 2, 1, 3, 2, 1, 8]
def baseStart_463090 : Nat := 118140960795 + 463090 * 2 ^ 59
def prefixEnd_463090 : Nat := 4983230072969 + 3 ^ 40 * 463090 * 2
def baseEnd_463090 : Nat := 23485210497846754760029

theorem tailTrace_463090 : CollatzResearch.WordTrace tailWord_463090 prefixEnd_463090 23485210497846754760029 := by
  unfold tailWord_463090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4222569973077873580118681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11260186594874329546983149 4222569973077873580118681)
  ·
    refine ⟨3166927479808405185089011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4222569973077873580118681 3166927479808405185089011)
    ·
      refine ⟨4750391219712607777633517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3166927479808405185089011 4750391219712607777633517)
      ·
        refine ⟨1781396707392227916612569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4750391219712607777633517 1781396707392227916612569)
        ·
          refine ⟨1336047530544170937459427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1781396707392227916612569 1336047530544170937459427)
          ·
            refine ⟨2004071295816256406189141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336047530544170937459427 2004071295816256406189141)
            ·
              refine ⟨23485210497846754760029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2004071295816256406189141 23485210497846754760029)
              ·
                rfl

theorem cell20_463090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 8].length) (baseStart_463090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463090 prefixEnd_463090 := by exact prefixLift 463090
  have htrace : WordTrace (prefixWord ++ tailWord_463090) baseStart_463090 baseEnd_463090 := by
    simpa [prefixWord, tailWord_463090, baseEnd_463090] using wordTrace_append hprefix tailTrace_463090
  have hstable : (prefixWord ++ tailWord_463090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463090).length < 2 ^ (prefixWord ++ tailWord_463090).sum := by decide
  have hdescent : baseEnd_463090 < baseStart_463090 := by decide
  rcases family_descends (prefixWord ++ tailWord_463090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463100 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 4]
def baseStart_463100 : Nat := 118140960795 + 463100 * 2 ^ 59
def prefixEnd_463100 : Nat := 4983230072969 + 3 ^ 40 * 463100 * 2
def baseEnd_463100 : Nat := 211371458753105202506887

theorem tailTrace_463100 : CollatzResearch.WordTrace tailWord_463100 prefixEnd_463100 211371458753105202506887 := by
  unfold tailWord_463100
  simp only [CollatzResearch.WordTrace]
  refine ⟨8445322311137633014169377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11260429748183510685559169 8445322311137633014169377)
  ·
    refine ⟨6333991733353224760627033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8445322311137633014169377 6333991733353224760627033)
    ·
      refine ⟨4750493800014918570470275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6333991733353224760627033 4750493800014918570470275)
      ·
        refine ⟨7125740700022377855705413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4750493800014918570470275 7125740700022377855705413)
        ·
          refine ⟨1336076381254195847944765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7125740700022377855705413 1336076381254195847944765)
          ·
            refine ⟨501028642970323442979287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1336076381254195847944765 501028642970323442979287)
            ·
              refine ⟨751542964455485164468931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501028642970323442979287 751542964455485164468931)
              ·
                refine ⟨1127314446683227746703397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751542964455485164468931 1127314446683227746703397)
                ·
                  refine ⟨211371458753105202506887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1127314446683227746703397 211371458753105202506887)
                  ·
                    rfl

theorem cell20_463100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_463100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463100 prefixEnd_463100 := by exact prefixLift 463100
  have htrace : WordTrace (prefixWord ++ tailWord_463100) baseStart_463100 baseEnd_463100 := by
    simpa [prefixWord, tailWord_463100, baseEnd_463100] using wordTrace_append hprefix tailTrace_463100
  have hstable : (prefixWord ++ tailWord_463100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463100).length < 2 ^ (prefixWord ++ tailWord_463100).sum := by decide
  have hdescent : baseEnd_463100 < baseStart_463100 := by decide
  rcases family_descends (prefixWord ++ tailWord_463100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463207 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 3]
def baseStart_463207 : Nat := 118140960795 + 463207 * 2 ^ 59
def prefixEnd_463207 : Nat := 4983230072969 + 3 ^ 40 * 463207 * 2
def baseEnd_463207 : Nat := 211420296468688385939783

theorem tailTrace_463207 : CollatzResearch.WordTrace tailWord_463207 prefixEnd_463207 211420296468688385939783 := by
  unfold tailWord_463207
  simp only [CollatzResearch.WordTrace]
  refine ⟨16894547232887623302483875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11263031488591748868322583 16894547232887623302483875)
  ·
    refine ⟨25341820849331434953725813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16894547232887623302483875 25341820849331434953725813)
    ·
      refine ⟨2375795704624822026911795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25341820849331434953725813 2375795704624822026911795)
      ·
        refine ⟨3563693556937233040367693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375795704624822026911795 3563693556937233040367693)
        ·
          refine ⟨1336385083851462390137885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3563693556937233040367693 1336385083851462390137885)
          ·
            refine ⟨501144406444298396301707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1336385083851462390137885 501144406444298396301707)
            ·
              refine ⟨751716609666447594452561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501144406444298396301707 751716609666447594452561)
              ·
                refine ⟨563787457249835695839421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751716609666447594452561 563787457249835695839421)
                ·
                  refine ⟨211420296468688385939783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563787457249835695839421 211420296468688385939783)
                  ·
                    rfl

theorem cell20_463207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 3].length) (baseStart_463207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463207 prefixEnd_463207 := by exact prefixLift 463207
  have htrace : WordTrace (prefixWord ++ tailWord_463207) baseStart_463207 baseEnd_463207 := by
    simpa [prefixWord, tailWord_463207, baseEnd_463207] using wordTrace_append hprefix tailTrace_463207
  have hstable : (prefixWord ++ tailWord_463207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463207).length < 2 ^ (prefixWord ++ tailWord_463207).sum := by decide
  have hdescent : baseEnd_463207 < baseStart_463207 := by decide
  rcases family_descends (prefixWord ++ tailWord_463207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463225 : List Nat := [1, 2, 1, 3, 2, 1, 1, 9]
def baseStart_463225 : Nat := 118140960795 + 463225 * 2 ^ 59
def prefixEnd_463225 : Nat := 4983230072969 + 3 ^ 40 * 463225 * 2
def baseEnd_463225 : Nat := 70476170719720107779903

theorem tailTrace_463225 : CollatzResearch.WordTrace tailWord_463225 prefixEnd_463225 70476170719720107779903 := by
  unfold tailWord_463225
  simp only [CollatzResearch.WordTrace]
  refine ⟨16895203746822412376639129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11263469164548274917759419 16895203746822412376639129)
  ·
    refine ⟨12671402810116809282479347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16895203746822412376639129 12671402810116809282479347)
    ·
      refine ⟨19007104215175213923719021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12671402810116809282479347 19007104215175213923719021)
      ·
        refine ⟨7127664080690705221394633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19007104215175213923719021 7127664080690705221394633)
        ·
          refine ⟨5345748060518028916045975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7127664080690705221394633 5345748060518028916045975)
          ·
            refine ⟨8018622090777043374068963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345748060518028916045975 8018622090777043374068963)
            ·
              refine ⟨12027933136165565061103445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8018622090777043374068963 12027933136165565061103445)
              ·
                refine ⟨70476170719720107779903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12027933136165565061103445 70476170719720107779903)
                ·
                  rfl

theorem cell20_463225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_463225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463225 prefixEnd_463225 := by exact prefixLift 463225
  have htrace : WordTrace (prefixWord ++ tailWord_463225) baseStart_463225 baseEnd_463225 := by
    simpa [prefixWord, tailWord_463225, baseEnd_463225] using wordTrace_append hprefix tailTrace_463225
  have hstable : (prefixWord ++ tailWord_463225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463225).length < 2 ^ (prefixWord ++ tailWord_463225).sum := by decide
  have hdescent : baseEnd_463225 < baseStart_463225 := by decide
  rcases family_descends (prefixWord ++ tailWord_463225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463234 : List Nat := [3, 4, 2, 1, 3, 1, 2, 4]
def baseStart_463234 : Nat := 118140960795 + 463234 * 2 ^ 59
def prefixEnd_463234 : Nat := 4983230072969 + 3 ^ 40 * 463234 * 2
def baseEnd_463234 : Nat := 70477540001465430679891

theorem tailTrace_463234 : CollatzResearch.WordTrace tailWord_463234 prefixEnd_463234 70477540001465430679891 := by
  unfold tailWord_463234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223883000947451728429189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11263688002526537942477837 4223883000947451728429189)
  ·
    refine ⟨791978062677647199080473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4223883000947451728429189 791978062677647199080473)
    ·
      refine ⟨593983547008235399310355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 791978062677647199080473 593983547008235399310355)
      ·
        refine ⟨890975320512353098965533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593983547008235399310355 890975320512353098965533)
        ·
          refine ⟨334115745192132412112075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 890975320512353098965533 334115745192132412112075)
          ·
            refine ⟨501173617788198618168113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334115745192132412112075 501173617788198618168113)
            ·
              refine ⟨375880213341148963626085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501173617788198618168113 375880213341148963626085)
              ·
                refine ⟨70477540001465430679891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375880213341148963626085 70477540001465430679891)
                ·
                  rfl

theorem cell20_463234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_463234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463234 prefixEnd_463234 := by exact prefixLift 463234
  have htrace : WordTrace (prefixWord ++ tailWord_463234) baseStart_463234 baseEnd_463234 := by
    simpa [prefixWord, tailWord_463234, baseEnd_463234] using wordTrace_append hprefix tailTrace_463234
  have hstable : (prefixWord ++ tailWord_463234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463234).length < 2 ^ (prefixWord ++ tailWord_463234).sum := by decide
  have hdescent : baseEnd_463234 < baseStart_463234 := by decide
  rcases family_descends (prefixWord ++ tailWord_463234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463266 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_463266 : Nat := 118140960795 + 463266 * 2 ^ 59
def prefixEnd_463266 : Nat := 4983230072969 + 3 ^ 40 * 463266 * 2
def baseEnd_463266 : Nat := 211447225676346402972875

theorem tailTrace_463266 : CollatzResearch.WordTrace tailWord_463266 prefixEnd_463266 211447225676346402972875 := by
  unfold tailWord_463266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4224174784918469094720413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11264466093115917585921101 4224174784918469094720413)
  ·
    refine ⟨1584065544344425910520155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4224174784918469094720413 1584065544344425910520155)
    ·
      refine ⟨2376098316516638865780233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1584065544344425910520155 2376098316516638865780233)
      ·
        refine ⟨1782073737387479149335175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2376098316516638865780233 1782073737387479149335175)
        ·
          refine ⟨2673110606081218724002763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782073737387479149335175 2673110606081218724002763)
          ·
            refine ⟨4009665909121828086004145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673110606081218724002763 4009665909121828086004145)
            ·
              refine ⟨3007249431841371064503109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4009665909121828086004145 3007249431841371064503109)
              ·
                refine ⟨563859268470257074594333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3007249431841371064503109 563859268470257074594333)
                ·
                  refine ⟨211447225676346402972875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563859268470257074594333 211447225676346402972875)
                  ·
                    rfl

theorem cell20_463266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_463266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463266 prefixEnd_463266 := by exact prefixLift 463266
  have htrace : WordTrace (prefixWord ++ tailWord_463266) baseStart_463266 baseEnd_463266 := by
    simpa [prefixWord, tailWord_463266, baseEnd_463266] using wordTrace_append hprefix tailTrace_463266
  have hstable : (prefixWord ++ tailWord_463266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463266).length < 2 ^ (prefixWord ++ tailWord_463266).sum := by decide
  have hdescent : baseEnd_463266 < baseStart_463266 := by decide
  rcases family_descends (prefixWord ++ tailWord_463266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463273 : List Nat := [1, 2, 1, 1, 1, 1, 3, 8, 2]
def baseStart_463273 : Nat := 118140960795 + 463273 * 2 ^ 59
def prefixEnd_463273 : Nat := 4983230072969 + 3 ^ 40 * 463273 * 2
def baseEnd_463273 : Nat := 211450420667085489739513

theorem tailTrace_463273 : CollatzResearch.WordTrace tailWord_463273 prefixEnd_463273 211450420667085489739513 := by
  unfold tailWord_463273
  simp only [CollatzResearch.WordTrace]
  refine ⟨16896954450648516574386473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11264636300432344382924315 16896954450648516574386473)
  ·
    refine ⟨12672715837986387430789855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16896954450648516574386473 12672715837986387430789855)
    ·
      refine ⟨19009073756979581146184783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12672715837986387430789855 19009073756979581146184783)
      ·
        refine ⟨28513610635469371719277175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19009073756979581146184783 28513610635469371719277175)
        ·
          refine ⟨42770415953204057578915763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28513610635469371719277175 42770415953204057578915763)
          ·
            refine ⟨64155623929806086368373645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42770415953204057578915763 64155623929806086368373645)
            ·
              refine ⟨24058358973677282388140117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64155623929806086368373645 24058358973677282388140117)
              ·
                refine ⟨281933894222780652986017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 24058358973677282388140117 281933894222780652986017)
                ·
                  refine ⟨211450420667085489739513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281933894222780652986017 211450420667085489739513)
                  ·
                    rfl

theorem cell20_463273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 2].length) (baseStart_463273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463273 prefixEnd_463273 := by exact prefixLift 463273
  have htrace : WordTrace (prefixWord ++ tailWord_463273) baseStart_463273 baseEnd_463273 := by
    simpa [prefixWord, tailWord_463273, baseEnd_463273] using wordTrace_append hprefix tailTrace_463273
  have hstable : (prefixWord ++ tailWord_463273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463273).length < 2 ^ (prefixWord ++ tailWord_463273).sum := by decide
  have hdescent : baseEnd_463273 < baseStart_463273 := by decide
  rcases family_descends (prefixWord ++ tailWord_463273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463311 : List Nat := [1, 1, 2, 1, 1, 4, 1, 7, 2]
def baseStart_463311 : Nat := 118140960795 + 463311 * 2 ^ 59
def prefixEnd_463311 : Nat := 4983230072969 + 3 ^ 40 * 463311 * 2
def baseEnd_463311 : Nat := 211467764902526246472691

theorem tailTrace_463311 : CollatzResearch.WordTrace tailWord_463311 prefixEnd_463311 211467764902526246472691 := by
  unfold tailWord_463311
  simp only [CollatzResearch.WordTrace]
  refine ⟨16898340424510849064269787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11265560283007232709513191 16898340424510849064269787)
  ·
    refine ⟨25347510636766273596404681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16898340424510849064269787 25347510636766273596404681)
    ·
      refine ⟨19010632977574705197303511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25347510636766273596404681 19010632977574705197303511)
      ·
        refine ⟨28515949466362057795955267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19010632977574705197303511 28515949466362057795955267)
        ·
          refine ⟨42773924199543086693932901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28515949466362057795955267 42773924199543086693932901)
          ·
            refine ⟨8020110787414328755112419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42773924199543086693932901 8020110787414328755112419)
            ·
              refine ⟨12030166181121493132668629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8020110787414328755112419 12030166181121493132668629)
              ·
                refine ⟨281957019870034995296921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12030166181121493132668629 281957019870034995296921)
                ·
                  refine ⟨211467764902526246472691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281957019870034995296921 211467764902526246472691)
                  ·
                    rfl

theorem cell20_463311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 2].length) (baseStart_463311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463311 prefixEnd_463311 := by exact prefixLift 463311
  have htrace : WordTrace (prefixWord ++ tailWord_463311) baseStart_463311 baseEnd_463311 := by
    simpa [prefixWord, tailWord_463311, baseEnd_463311] using wordTrace_append hprefix tailTrace_463311
  have hstable : (prefixWord ++ tailWord_463311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463311).length < 2 ^ (prefixWord ++ tailWord_463311).sum := by decide
  have hdescent : baseEnd_463311 < baseStart_463311 := by decide
  rcases family_descends (prefixWord ++ tailWord_463311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463342 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_463342 : Nat := 118140960795 + 463342 * 2 ^ 59
def prefixEnd_463342 : Nat := 4983230072969 + 3 ^ 40 * 463342 * 2
def baseEnd_463342 : Nat := 211481914147227916439231

theorem tailTrace_463342 : CollatzResearch.WordTrace tailWord_463342 prefixEnd_463342 211481914147227916439231 := by
  unfold tailWord_463342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112433885924817669831035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11266314058265694239098853 2112433885924817669831035)
  ·
    refine ⟨3168650828887226504746553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2112433885924817669831035 3168650828887226504746553)
    ·
      refine ⟨2376488121665419878559915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3168650828887226504746553 2376488121665419878559915)
      ·
        refine ⟨3564732182498129817839873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2376488121665419878559915 3564732182498129817839873)
        ·
          refine ⟨2673549136873597363379905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3564732182498129817839873 2673549136873597363379905)
          ·
            refine ⟨2005161852655198022534929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2673549136873597363379905 2005161852655198022534929)
            ·
              refine ⟨1503871389491398516901197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005161852655198022534929 1503871389491398516901197)
              ·
                refine ⟨563951771059274443837949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1503871389491398516901197 563951771059274443837949)
                ·
                  refine ⟨211481914147227916439231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563951771059274443837949 211481914147227916439231)
                  ·
                    rfl

theorem cell20_463342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_463342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463342 prefixEnd_463342 := by exact prefixLift 463342
  have htrace : WordTrace (prefixWord ++ tailWord_463342) baseStart_463342 baseEnd_463342 := by
    simpa [prefixWord, tailWord_463342, baseEnd_463342] using wordTrace_append hprefix tailTrace_463342
  have hstable : (prefixWord ++ tailWord_463342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463342).length < 2 ^ (prefixWord ++ tailWord_463342).sum := by decide
  have hdescent : baseEnd_463342 < baseStart_463342 := by decide
  rcases family_descends (prefixWord ++ tailWord_463342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463362 : List Nat := [3, 4, 1, 2, 2, 1, 2, 3, 2]
def baseStart_463362 : Nat := 118140960795 + 463362 * 2 ^ 59
def prefixEnd_463362 : Nat := 4983230072969 + 3 ^ 40 * 463362 * 2
def baseEnd_463362 : Nat := 211491042692196735772483

theorem tailTrace_463362 : CollatzResearch.WordTrace tailWord_463362 prefixEnd_463362 211491042692196735772483 := by
  unfold tailWord_463362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4225050136831521193594085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11266800364884056516250893 4225050136831521193594085)
  ·
    refine ⟨792196900655910223798891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4225050136831521193594085 792196900655910223798891)
    ·
      refine ⟨1188295350983865335698337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 792196900655910223798891 1188295350983865335698337)
      ·
        refine ⟨891221513237899001773753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1188295350983865335698337 891221513237899001773753)
        ·
          refine ⟨668416134928424251330315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 891221513237899001773753 668416134928424251330315)
          ·
            refine ⟨1002624202392636376995473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668416134928424251330315 1002624202392636376995473)
            ·
              refine ⟨751968151794477282746605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002624202392636376995473 751968151794477282746605)
              ·
                refine ⟨281988056922928981029977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 751968151794477282746605 281988056922928981029977)
                ·
                  refine ⟨211491042692196735772483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281988056922928981029977 211491042692196735772483)
                  ·
                    rfl

theorem cell20_463362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_463362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463362 prefixEnd_463362 := by exact prefixLift 463362
  have htrace : WordTrace (prefixWord ++ tailWord_463362) baseStart_463362 baseEnd_463362 := by
    simpa [prefixWord, tailWord_463362, baseEnd_463362] using wordTrace_append hprefix tailTrace_463362
  have hstable : (prefixWord ++ tailWord_463362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463362).length < 2 ^ (prefixWord ++ tailWord_463362).sum := by decide
  have hdescent : baseEnd_463362 < baseStart_463362 := by decide
  rcases family_descends (prefixWord ++ tailWord_463362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463370 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_463370 : Nat := 118140960795 + 463370 * 2 ^ 59
def prefixEnd_463370 : Nat := 4983230072969 + 3 ^ 40 * 463370 * 2
def baseEnd_463370 : Nat := 211494694110184263505783

theorem tailTrace_463370 : CollatzResearch.WordTrace tailWord_463370 prefixEnd_463370 211494694110184263505783 := by
  unfold tailWord_463370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4225123082824275535166891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11266994887531401427111709 4225123082824275535166891)
  ·
    refine ⟨6337684624236413302750337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4225123082824275535166891 6337684624236413302750337)
    ·
      refine ⟨4753263468177309977062753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6337684624236413302750337 4753263468177309977062753)
      ·
        refine ⟨3564947601132982482797065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4753263468177309977062753 3564947601132982482797065)
        ·
          refine ⟨2673710700849736862097799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3564947601132982482797065 2673710700849736862097799)
          ·
            refine ⟨4010566051274605293146699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673710700849736862097799 4010566051274605293146699)
            ·
              refine ⟨6015849076911907939720049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010566051274605293146699 6015849076911907939720049)
              ·
                refine ⟨4511886807683930954790037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6015849076911907939720049 4511886807683930954790037)
                ·
                  refine ⟨211494694110184263505783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4511886807683930954790037 211494694110184263505783)
                  ·
                    rfl

theorem cell20_463370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_463370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463370 prefixEnd_463370 := by exact prefixLift 463370
  have htrace : WordTrace (prefixWord ++ tailWord_463370) baseStart_463370 baseEnd_463370 := by
    simpa [prefixWord, tailWord_463370, baseEnd_463370] using wordTrace_append hprefix tailTrace_463370
  have hstable : (prefixWord ++ tailWord_463370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463370).length < 2 ^ (prefixWord ++ tailWord_463370).sum := by decide
  have hdescent : baseEnd_463370 < baseStart_463370 := by decide
  rcases family_descends (prefixWord ++ tailWord_463370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463408 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_463408 : Nat := 118140960795 + 463408 * 2 ^ 59
def prefixEnd_463408 : Nat := 4983230072969 + 3 ^ 40 * 463408 * 2
def baseEnd_463408 : Nat := 211512038345625020238961

theorem tailTrace_463408 : CollatzResearch.WordTrace tailWord_463408 prefixEnd_463408 211512038345625020238961 := by
  unfold tailWord_463408
  simp only [CollatzResearch.WordTrace]
  refine ⟨8450939152579717315275439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11267918870106289753700585 8450939152579717315275439)
  ·
    refine ⟨12676408728869575972913159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8450939152579717315275439 12676408728869575972913159)
    ·
      refine ⟨19014613093304363959369739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12676408728869575972913159 19014613093304363959369739)
      ·
        refine ⟨28521919639956545939054609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19014613093304363959369739 28521919639956545939054609)
        ·
          refine ⟨21391439729967409454290957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28521919639956545939054609 21391439729967409454290957)
          ·
            refine ⟨8021789898737778545359109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21391439729967409454290957 8021789898737778545359109)
            ·
              refine ⟨1504085606013333477254833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8021789898737778545359109 1504085606013333477254833)
              ·
                refine ⟨1128064204510000107941125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504085606013333477254833 1128064204510000107941125)
                ·
                  refine ⟨211512038345625020238961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1128064204510000107941125 211512038345625020238961)
                  ·
                    rfl

theorem cell20_463408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_463408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463408 prefixEnd_463408 := by exact prefixLift 463408
  have htrace : WordTrace (prefixWord ++ tailWord_463408) baseStart_463408 baseEnd_463408 := by
    simpa [prefixWord, tailWord_463408, baseEnd_463408] using wordTrace_append hprefix tailTrace_463408
  have hstable : (prefixWord ++ tailWord_463408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463408).length < 2 ^ (prefixWord ++ tailWord_463408).sum := by decide
  have hdescent : baseEnd_463408 < baseStart_463408 := by decide
  rcases family_descends (prefixWord ++ tailWord_463408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463415 : List Nat := [1, 1, 3, 1, 2, 3, 3, 6]
def baseStart_463415 : Nat := 118140960795 + 463415 * 2 ^ 59
def prefixEnd_463415 : Nat := 4983230072969 + 3 ^ 40 * 463415 * 2
def baseEnd_463415 : Nat := 70505077778788035668533

theorem tailTrace_463415 : CollatzResearch.WordTrace tailWord_463415 prefixEnd_463415 70505077778788035668533 := by
  unfold tailWord_463415
  simp only [CollatzResearch.WordTrace]
  refine ⟨16902133616134074826055699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11268089077422716550703799 16902133616134074826055699)
  ·
    refine ⟨25353200424201112239083549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16902133616134074826055699 25353200424201112239083549)
    ·
      refine ⟨9507450159075417089656331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25353200424201112239083549 9507450159075417089656331)
      ·
        refine ⟨14261175238613125634484497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9507450159075417089656331 14261175238613125634484497)
        ·
          refine ⟨10695881428959844225863373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14261175238613125634484497 10695881428959844225863373)
          ·
            refine ⟨4010955535859941584698765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10695881428959844225863373 4010955535859941584698765)
            ·
              refine ⟨1504108325947478094262037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4010955535859941584698765 1504108325947478094262037)
              ·
                refine ⟨70505077778788035668533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1504108325947478094262037 70505077778788035668533)
                ·
                  rfl

theorem cell20_463415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_463415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463415 prefixEnd_463415 := by exact prefixLift 463415
  have htrace : WordTrace (prefixWord ++ tailWord_463415) baseStart_463415 baseEnd_463415 := by
    simpa [prefixWord, tailWord_463415, baseEnd_463415] using wordTrace_append hprefix tailTrace_463415
  have hstable : (prefixWord ++ tailWord_463415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463415).length < 2 ^ (prefixWord ++ tailWord_463415).sum := by decide
  have hdescent : baseEnd_463415 < baseStart_463415 := by decide
  rcases family_descends (prefixWord ++ tailWord_463415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463421 : List Nat := [1, 4, 1, 3, 2, 3, 1, 3, 2]
def baseStart_463421 : Nat := 118140960795 + 463421 * 2 ^ 59
def prefixEnd_463421 : Nat := 4983230072969 + 3 ^ 40 * 463421 * 2
def baseEnd_463421 : Nat := 211517971899854752805575

theorem tailTrace_463421 : CollatzResearch.WordTrace tailWord_463421 prefixEnd_463421 211517971899854752805575 := by
  unfold tailWord_463421
  simp only [CollatzResearch.WordTrace]
  refine ⟨16902352454112337850774117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11268234969408225233849411 16902352454112337850774117)
  ·
    refine ⟨3169191085146063347020147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16902352454112337850774117 3169191085146063347020147)
    ·
      refine ⟨4753786627719095020530221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3169191085146063347020147 4753786627719095020530221)
      ·
        refine ⟨1782669985394660632698833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4753786627719095020530221 1782669985394660632698833)
        ·
          refine ⟨1337002489045995474524125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1782669985394660632698833 1337002489045995474524125)
          ·
            refine ⟨501375933392248302946547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1337002489045995474524125 501375933392248302946547)
            ·
              refine ⟨752063900088372454419821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501375933392248302946547 752063900088372454419821)
              ·
                refine ⟨282023962533139670407433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 752063900088372454419821 282023962533139670407433)
                ·
                  refine ⟨211517971899854752805575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282023962533139670407433 211517971899854752805575)
                  ·
                    rfl

theorem cell20_463421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_463421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463421 prefixEnd_463421 := by exact prefixLift 463421
  have htrace : WordTrace (prefixWord ++ tailWord_463421) baseStart_463421 baseEnd_463421 := by
    simpa [prefixWord, tailWord_463421, baseEnd_463421] using wordTrace_append hprefix tailTrace_463421
  have hstable : (prefixWord ++ tailWord_463421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463421).length < 2 ^ (prefixWord ++ tailWord_463421).sum := by decide
  have hdescent : baseEnd_463421 < baseStart_463421 := by decide
  rcases family_descends (prefixWord ++ tailWord_463421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463452 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 3]
def baseStart_463452 : Nat := 118140960795 + 463452 * 2 ^ 59
def prefixEnd_463452 : Nat := 4983230072969 + 3 ^ 40 * 463452 * 2
def baseEnd_463452 : Nat := 211532121144556422772115

theorem tailTrace_463452 : CollatzResearch.WordTrace tailWord_463452 prefixEnd_463452 211532121144556422772115 := by
  unfold tailWord_463452
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451741558500015072576305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11268988744666686763435073 8451741558500015072576305)
  ·
    refine ⟨6338806168875011304432229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8451741558500015072576305 6338806168875011304432229)
    ·
      refine ⟨1188526156664064619581043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6338806168875011304432229 1188526156664064619581043)
      ·
        refine ⟨1782789234996096929371565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188526156664064619581043 1782789234996096929371565)
        ·
          refine ⟨668545963123536348514337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1782789234996096929371565 668545963123536348514337)
          ·
            refine ⟨501409472342652261385753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668545963123536348514337 501409472342652261385753)
            ·
              refine ⟨376057104256989196039315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501409472342652261385753 376057104256989196039315)
              ·
                refine ⟨564085656385483794058973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376057104256989196039315 564085656385483794058973)
                ·
                  refine ⟨211532121144556422772115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564085656385483794058973 211532121144556422772115)
                  ·
                    rfl

theorem cell20_463452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_463452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463452 prefixEnd_463452 := by exact prefixLift 463452
  have htrace : WordTrace (prefixWord ++ tailWord_463452) baseStart_463452 baseEnd_463452 := by
    simpa [prefixWord, tailWord_463452, baseEnd_463452] using wordTrace_append hprefix tailTrace_463452
  have hstable : (prefixWord ++ tailWord_463452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463452).length < 2 ^ (prefixWord ++ tailWord_463452).sum := by decide
  have hdescent : baseEnd_463452 < baseStart_463452 := by decide
  rcases family_descends (prefixWord ++ tailWord_463452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463456 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 3]
def baseStart_463456 : Nat := 118140960795 + 463456 * 2 ^ 59
def prefixEnd_463456 : Nat := 4983230072969 + 3 ^ 40 * 463456 * 2
def baseEnd_463456 : Nat := 211533946853550186638765

theorem tailTrace_463456 : CollatzResearch.WordTrace tailWord_463456 prefixEnd_463456 211533946853550186638765 := by
  unfold tailWord_463456
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451814504492769414149111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11269086005990359218865481 8451814504492769414149111)
  ·
    refine ⟨12677721756739154121223667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8451814504492769414149111 12677721756739154121223667)
    ·
      refine ⟨19016582635108731181835501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12677721756739154121223667 19016582635108731181835501)
      ·
        refine ⟨7131218488165774193188313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19016582635108731181835501 7131218488165774193188313)
        ·
          refine ⟨5348413866124330644891235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7131218488165774193188313 5348413866124330644891235)
          ·
            refine ⟨8022620799186495967336853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5348413866124330644891235 8022620799186495967336853)
            ·
              refine ⟨376060349961866998468915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8022620799186495967336853 376060349961866998468915)
              ·
                refine ⟨564090524942800497703373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376060349961866998468915 564090524942800497703373)
                ·
                  refine ⟨211533946853550186638765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564090524942800497703373 211533946853550186638765)
                  ·
                    rfl

theorem cell20_463456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_463456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463456 prefixEnd_463456 := by exact prefixLift 463456
  have htrace : WordTrace (prefixWord ++ tailWord_463456) baseStart_463456 baseEnd_463456 := by
    simpa [prefixWord, tailWord_463456, baseEnd_463456] using wordTrace_append hprefix tailTrace_463456
  have hstable : (prefixWord ++ tailWord_463456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463456).length < 2 ^ (prefixWord ++ tailWord_463456).sum := by decide
  have hdescent : baseEnd_463456 < baseStart_463456 := by decide
  rcases family_descends (prefixWord ++ tailWord_463456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463470 : List Nat := [4, 1, 2, 2, 2, 1, 2, 6]
def baseStart_463470 : Nat := 118140960795 + 463470 * 2 ^ 59
def prefixEnd_463470 : Nat := 4983230072969 + 3 ^ 40 * 463470 * 2
def baseEnd_463470 : Nat := 70513445611676120057347

theorem tailTrace_463470 : CollatzResearch.WordTrace tailWord_463470 prefixEnd_463470 70513445611676120057347 := by
  unfold tailWord_463470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2113017453866852402413483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11269426420623212812871909 2113017453866852402413483)
  ·
    refine ⟨3169526180800278603620225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2113017453866852402413483 3169526180800278603620225)
    ·
      refine ⟨2377144635600208952715169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3169526180800278603620225 2377144635600208952715169)
      ·
        refine ⟨1782858476700156714536377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2377144635600208952715169 1782858476700156714536377)
        ·
          refine ⟨1337143857525117535902283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1782858476700156714536377 1337143857525117535902283)
          ·
            refine ⟨2005715786287676303853425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337143857525117535902283 2005715786287676303853425)
            ·
              refine ⟨1504286839715757227890069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005715786287676303853425 1504286839715757227890069)
              ·
                refine ⟨70513445611676120057347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1504286839715757227890069 70513445611676120057347)
                ·
                  rfl

theorem cell20_463470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_463470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463470 prefixEnd_463470 := by exact prefixLift 463470
  have htrace : WordTrace (prefixWord ++ tailWord_463470) baseStart_463470 baseEnd_463470 := by
    simpa [prefixWord, tailWord_463470, baseEnd_463470] using wordTrace_append hprefix tailTrace_463470
  have hstable : (prefixWord ++ tailWord_463470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463470).length < 2 ^ (prefixWord ++ tailWord_463470).sum := by decide
  have hdescent : baseEnd_463470 < baseStart_463470 := by decide
  rcases family_descends (prefixWord ++ tailWord_463470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463536 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_463536 : Nat := 118140960795 + 463536 * 2 ^ 59
def prefixEnd_463536 : Nat := 4983230072969 + 3 ^ 40 * 463536 * 2
def baseEnd_463536 : Nat := 211570461033425463971771

theorem tailTrace_463536 : CollatzResearch.WordTrace tailWord_463536 prefixEnd_463536 211570461033425463971771 := by
  unfold tailWord_463536
  simp only [CollatzResearch.WordTrace]
  refine ⟨8453273424347856245605231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11271031232463808327473641 8453273424347856245605231)
  ·
    refine ⟨12679910136521784368407847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8453273424347856245605231 12679910136521784368407847)
    ·
      refine ⟨19019865204782676552611771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12679910136521784368407847 19019865204782676552611771)
      ·
        refine ⟨28529797807174014828917657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19019865204782676552611771 28529797807174014828917657)
        ·
          refine ⟨21397348355380511121688243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28529797807174014828917657 21397348355380511121688243)
          ·
            refine ⟨32096022533070766682532365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21397348355380511121688243 32096022533070766682532365)
            ·
              refine ⟨12036008449901537505949637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32096022533070766682532365 12036008449901537505949637)
              ·
                refine ⟨2256751584356538282365557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12036008449901537505949637 2256751584356538282365557)
                ·
                  refine ⟨211570461033425463971771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2256751584356538282365557 211570461033425463971771)
                  ·
                    rfl

theorem cell20_463536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_463536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463536 prefixEnd_463536 := by exact prefixLift 463536
  have htrace : WordTrace (prefixWord ++ tailWord_463536) baseStart_463536 baseEnd_463536 := by
    simpa [prefixWord, tailWord_463536, baseEnd_463536] using wordTrace_append hprefix tailTrace_463536
  have hstable : (prefixWord ++ tailWord_463536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463536).length < 2 ^ (prefixWord ++ tailWord_463536).sum := by decide
  have hdescent : baseEnd_463536 < baseStart_463536 := by decide
  rcases family_descends (prefixWord ++ tailWord_463536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463539 : List Nat := [1, 1, 1, 2, 3, 4, 1, 5, 2]
def baseStart_463539 : Nat := 118140960795 + 463539 * 2 ^ 59
def prefixEnd_463539 : Nat := 4983230072969 + 3 ^ 40 * 463539 * 2
def baseEnd_463539 : Nat := 211571830315170786871759

theorem tailTrace_463539 : CollatzResearch.WordTrace tailWord_463539 prefixEnd_463539 211571830315170786871759 := by
  unfold tailWord_463539
  simp only [CollatzResearch.WordTrace]
  refine ⟨16906656267684844003569671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11271104178456562669046447 16906656267684844003569671)
  ·
    refine ⟨25359984401527266005354507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16906656267684844003569671 25359984401527266005354507)
    ·
      refine ⟨38039976602290899008031761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25359984401527266005354507 38039976602290899008031761)
      ·
        refine ⟨28529982451718174256023821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38039976602290899008031761 28529982451718174256023821)
        ·
          refine ⟨10698743419394315346008933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28529982451718174256023821 10698743419394315346008933)
          ·
            refine ⟨2006014391136434127376675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10698743419394315346008933 2006014391136434127376675)
            ·
              refine ⟨3009021586704651191065013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006014391136434127376675 3009021586704651191065013)
              ·
                refine ⟨282095773753561049162345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3009021586704651191065013 282095773753561049162345)
                ·
                  refine ⟨211571830315170786871759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282095773753561049162345 211571830315170786871759)
                  ·
                    rfl

theorem cell20_463539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 2].length) (baseStart_463539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463539 prefixEnd_463539 := by exact prefixLift 463539
  have htrace : WordTrace (prefixWord ++ tailWord_463539) baseStart_463539 baseEnd_463539 := by
    simpa [prefixWord, tailWord_463539, baseEnd_463539] using wordTrace_append hprefix tailTrace_463539
  have hstable : (prefixWord ++ tailWord_463539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463539).length < 2 ^ (prefixWord ++ tailWord_463539).sum := by decide
  have hdescent : baseEnd_463539 < baseStart_463539 := by decide
  rcases family_descends (prefixWord ++ tailWord_463539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463556 : List Nat := [2, 3, 3, 1, 1, 2, 2, 4, 2]
def baseStart_463556 : Nat := 118140960795 + 463556 * 2 ^ 59
def prefixEnd_463556 : Nat := 4983230072969 + 3 ^ 40 * 463556 * 2
def baseEnd_463556 : Nat := 211579589578394283305023

theorem tailTrace_463556 : CollatzResearch.WordTrace tailWord_463556 prefixEnd_463556 211579589578394283305023 := by
  unfold tailWord_463556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8453638154311627953469261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11271517539082170604625681 8453638154311627953469261)
  ·
    refine ⟨3170114307866860482550973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8453638154311627953469261 3170114307866860482550973)
    ·
      refine ⟨1188792865450072680956615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3170114307866860482550973 1188792865450072680956615)
      ·
        refine ⟨1783189298175109021434923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188792865450072680956615 1783189298175109021434923)
        ·
          refine ⟨2674783947262663532152385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783189298175109021434923 2674783947262663532152385)
          ·
            refine ⟨2006087960446997649114289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2674783947262663532152385 2006087960446997649114289)
            ·
              refine ⟨1504565970335248236835717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006087960446997649114289 1504565970335248236835717)
              ·
                refine ⟨282106119437859044406697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1504565970335248236835717 282106119437859044406697)
                ·
                  refine ⟨211579589578394283305023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282106119437859044406697 211579589578394283305023)
                  ·
                    rfl

theorem cell20_463556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_463556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463556 prefixEnd_463556 := by exact prefixLift 463556
  have htrace : WordTrace (prefixWord ++ tailWord_463556) baseStart_463556 baseEnd_463556 := by
    simpa [prefixWord, tailWord_463556, baseEnd_463556] using wordTrace_append hprefix tailTrace_463556
  have hstable : (prefixWord ++ tailWord_463556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463556).length < 2 ^ (prefixWord ++ tailWord_463556).sum := by decide
  have hdescent : baseEnd_463556 < baseStart_463556 := by decide
  rcases family_descends (prefixWord ++ tailWord_463556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463560 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_463560 : Nat := 118140960795 + 463560 * 2 ^ 59
def prefixEnd_463560 : Nat := 4983230072969 + 3 ^ 40 * 463560 * 2
def baseEnd_463560 : Nat := 211581415287388047171673

theorem tailTrace_463560 : CollatzResearch.WordTrace tailWord_463560 prefixEnd_463560 211581415287388047171673 := by
  unfold tailWord_463560
  simp only [CollatzResearch.WordTrace]
  refine ⟨8453711100304382295042067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11271614800405843060056089 8453711100304382295042067)
  ·
    refine ⟨12680566650456573442563101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8453711100304382295042067 12680566650456573442563101)
    ·
      refine ⟨4755212493921215040961163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12680566650456573442563101 4755212493921215040961163)
      ·
        refine ⟨7132818740881822561441745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4755212493921215040961163 7132818740881822561441745)
        ·
          refine ⟨5349614055661366921081309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7132818740881822561441745 5349614055661366921081309)
          ·
            refine ⟨2006105270873012595405491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5349614055661366921081309 2006105270873012595405491)
            ·
              refine ⟨3009157906309518893108237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006105270873012595405491 3009157906309518893108237)
              ·
                refine ⟨1128434214866069584915589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3009157906309518893108237 1128434214866069584915589)
                ·
                  refine ⟨211581415287388047171673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1128434214866069584915589 211581415287388047171673)
                  ·
                    rfl

theorem cell20_463560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_463560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463560 prefixEnd_463560 := by exact prefixLift 463560
  have htrace : WordTrace (prefixWord ++ tailWord_463560) baseStart_463560 baseEnd_463560 := by
    simpa [prefixWord, tailWord_463560, baseEnd_463560] using wordTrace_append hprefix tailTrace_463560
  have hstable : (prefixWord ++ tailWord_463560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463560).length < 2 ^ (prefixWord ++ tailWord_463560).sum := by decide
  have hdescent : baseEnd_463560 < baseStart_463560 := by decide
  rcases family_descends (prefixWord ++ tailWord_463560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463580 : List Nat := [2, 2, 5, 1, 1, 3, 2, 4]
def baseStart_463580 : Nat := 118140960795 + 463580 * 2 ^ 59
def prefixEnd_463580 : Nat := 4983230072969 + 3 ^ 40 * 463580 * 2
def baseEnd_463580 : Nat := 70530181277452288834975

theorem tailTrace_463580 : CollatzResearch.WordTrace tailWord_463580 prefixEnd_463580 70530181277452288834975 := by
  unfold tailWord_463580
  simp only [CollatzResearch.WordTrace]
  refine ⟨8454075830268154002906097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11272101107024205337208129 8454075830268154002906097)
  ·
    refine ⟨6340556872701115502179573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8454075830268154002906097 6340556872701115502179573)
    ·
      refine ⟨594427206815729578329335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6340556872701115502179573 594427206815729578329335)
      ·
        refine ⟨891640810223594367494003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594427206815729578329335 891640810223594367494003)
        ·
          refine ⟨1337461215335391551241005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891640810223594367494003 1337461215335391551241005)
          ·
            refine ⟨501547955750771831715377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1337461215335391551241005 501547955750771831715377)
            ·
              refine ⟨376160966813078873786533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501547955750771831715377 376160966813078873786533)
              ·
                refine ⟨70530181277452288834975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376160966813078873786533 70530181277452288834975)
                ·
                  rfl

theorem cell20_463580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_463580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463580 prefixEnd_463580 := by exact prefixLift 463580
  have htrace : WordTrace (prefixWord ++ tailWord_463580) baseStart_463580 baseEnd_463580 := by
    simpa [prefixWord, tailWord_463580, baseEnd_463580] using wordTrace_append hprefix tailTrace_463580
  have hstable : (prefixWord ++ tailWord_463580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463580).length < 2 ^ (prefixWord ++ tailWord_463580).sum := by decide
  have hdescent : baseEnd_463580 < baseStart_463580 := by decide
  rcases family_descends (prefixWord ++ tailWord_463580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463653 : List Nat := [1, 3, 1, 2, 3, 1, 2, 5, 2]
def baseStart_463653 : Nat := 118140960795 + 463653 * 2 ^ 59
def prefixEnd_463653 : Nat := 4983230072969 + 3 ^ 40 * 463653 * 2
def baseEnd_463653 : Nat := 211623863021493057071293

theorem tailTrace_463653 : CollatzResearch.WordTrace tailWord_463653 prefixEnd_463653 211623863021493057071293 := by
  unfold tailWord_463653
  simp only [CollatzResearch.WordTrace]
  refine ⟨16910814189271841473219613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11273876126181227648813075 16910814189271841473219613)
  ·
    refine ⟨6341555320976940552457355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16910814189271841473219613 6341555320976940552457355)
    ·
      refine ⟨9512332981465410828686033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6341555320976940552457355 9512332981465410828686033)
      ·
        refine ⟨7134249736099058121514525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9512332981465410828686033 7134249736099058121514525)
        ·
          refine ⟨2675343651037146795567947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7134249736099058121514525 2675343651037146795567947)
          ·
            refine ⟨4013015476555720193351921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675343651037146795567947 4013015476555720193351921)
            ·
              refine ⟨3009761607416790145013941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4013015476555720193351921 3009761607416790145013941)
              ·
                refine ⟨282165150695324076095057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3009761607416790145013941 282165150695324076095057)
                ·
                  refine ⟨211623863021493057071293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282165150695324076095057 211623863021493057071293)
                  ·
                    rfl

theorem cell20_463653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_463653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463653 prefixEnd_463653 := by exact prefixLift 463653
  have htrace : WordTrace (prefixWord ++ tailWord_463653) baseStart_463653 baseEnd_463653 := by
    simpa [prefixWord, tailWord_463653, baseEnd_463653] using wordTrace_append hprefix tailTrace_463653
  have hstable : (prefixWord ++ tailWord_463653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463653).length < 2 ^ (prefixWord ++ tailWord_463653).sum := by decide
  have hdescent : baseEnd_463653 < baseStart_463653 := by decide
  rcases family_descends (prefixWord ++ tailWord_463653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463657 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_463657 : Nat := 118140960795 + 463657 * 2 ^ 59
def prefixEnd_463657 : Nat := 4983230072969 + 3 ^ 40 * 463657 * 2
def baseEnd_463657 : Nat := 211625688730486820937943

theorem tailTrace_463657 : CollatzResearch.WordTrace tailWord_463657 prefixEnd_463657 211625688730486820937943 := by
  unfold tailWord_463657
  simp only [CollatzResearch.WordTrace]
  refine ⟨16910960081257350156365225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11273973387504900104243483 16910960081257350156365225)
  ·
    refine ⟨12683220060943012617273919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16910960081257350156365225 12683220060943012617273919)
    ·
      refine ⟨19024830091414518925910879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12683220060943012617273919 19024830091414518925910879)
      ·
        refine ⟨28537245137121778388866319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19024830091414518925910879 28537245137121778388866319)
        ·
          refine ⟨42805867705682667583299479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28537245137121778388866319 42805867705682667583299479)
          ·
            refine ⟨64208801558524001374949219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42805867705682667583299479 64208801558524001374949219)
            ·
              refine ⟨96313202337786002062423829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64208801558524001374949219 96313202337786002062423829)
              ·
                refine ⟨4514681359583718846676117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96313202337786002062423829 4514681359583718846676117)
                ·
                  refine ⟨211625688730486820937943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4514681359583718846676117 211625688730486820937943)
                  ·
                    rfl

theorem cell20_463657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_463657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463657 prefixEnd_463657 := by exact prefixLift 463657
  have htrace : WordTrace (prefixWord ++ tailWord_463657) baseStart_463657 baseEnd_463657 := by
    simpa [prefixWord, tailWord_463657, baseEnd_463657] using wordTrace_append hprefix tailTrace_463657
  have hstable : (prefixWord ++ tailWord_463657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463657).length < 2 ^ (prefixWord ++ tailWord_463657).sum := by decide
  have hdescent : baseEnd_463657 < baseStart_463657 := by decide
  rcases family_descends (prefixWord ++ tailWord_463657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463667 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 3]
def baseStart_463667 : Nat := 118140960795 + 463667 * 2 ^ 59
def prefixEnd_463667 : Nat := 4983230072969 + 3 ^ 40 * 463667 * 2
def baseEnd_463667 : Nat := 211630253002971230604569

theorem tailTrace_463667 : CollatzResearch.WordTrace tailWord_463667 prefixEnd_463667 211630253002971230604569 := by
  unfold tailWord_463667
  simp only [CollatzResearch.WordTrace]
  refine ⟨16911324811221121864229255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11274216540814081242819503 16911324811221121864229255)
  ·
    refine ⟨25366987216831682796343883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16911324811221121864229255 25366987216831682796343883)
    ·
      refine ⟨38050480825247524194515825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25366987216831682796343883 38050480825247524194515825)
      ·
        refine ⟨28537860618935643145886869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38050480825247524194515825 28537860618935643145886869)
        ·
          refine ⟨1337712216512608272463447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28537860618935643145886869 1337712216512608272463447)
          ·
            refine ⟨2006568324768912408695171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337712216512608272463447 2006568324768912408695171)
            ·
              refine ⟨3009852487153368613042757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006568324768912408695171 3009852487153368613042757)
              ·
                refine ⟨564347341341256614945517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3009852487153368613042757 564347341341256614945517)
                ·
                  refine ⟨211630253002971230604569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564347341341256614945517 211630253002971230604569)
                  ·
                    rfl

theorem cell20_463667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 3].length) (baseStart_463667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463667 prefixEnd_463667 := by exact prefixLift 463667
  have htrace : WordTrace (prefixWord ++ tailWord_463667) baseStart_463667 baseEnd_463667 := by
    simpa [prefixWord, tailWord_463667, baseEnd_463667] using wordTrace_append hprefix tailTrace_463667
  have hstable : (prefixWord ++ tailWord_463667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463667).length < 2 ^ (prefixWord ++ tailWord_463667).sum := by decide
  have hdescent : baseEnd_463667 < baseStart_463667 := by decide
  rcases family_descends (prefixWord ++ tailWord_463667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463677 : List Nat := [1, 4, 1, 4, 2, 2, 1, 5]
def baseStart_463677 : Nat := 118140960795 + 463677 * 2 ^ 59
def prefixEnd_463677 : Nat := 4983230072969 + 3 ^ 40 * 463677 * 2
def baseEnd_463677 : Nat := 70544939091818546757065

theorem tailTrace_463677 : CollatzResearch.WordTrace tailWord_463677 prefixEnd_463677 70544939091818546757065 := by
  unfold tailWord_463677
  simp only [CollatzResearch.WordTrace]
  refine ⟨16911689541184893572093285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11274459694123262381395523 16911689541184893572093285)
  ·
    refine ⟨3170941788972167544767491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16911689541184893572093285 3170941788972167544767491)
    ·
      refine ⟨4756412683458251317151237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3170941788972167544767491 4756412683458251317151237)
      ·
        refine ⟨891827378148422121965857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4756412683458251317151237 891827378148422121965857)
        ·
          refine ⟨668870533611316591474393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 891827378148422121965857 668870533611316591474393)
          ·
            refine ⟨501652900208487443605795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668870533611316591474393 501652900208487443605795)
            ·
              refine ⟨752479350312731165408693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501652900208487443605795 752479350312731165408693)
              ·
                refine ⟨70544939091818546757065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 752479350312731165408693 70544939091818546757065)
                ·
                  rfl

theorem cell20_463677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 5].length) (baseStart_463677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463677 prefixEnd_463677 := by exact prefixLift 463677
  have htrace : WordTrace (prefixWord ++ tailWord_463677) baseStart_463677 baseEnd_463677 := by
    simpa [prefixWord, tailWord_463677, baseEnd_463677] using wordTrace_append hprefix tailTrace_463677
  have hstable : (prefixWord ++ tailWord_463677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463677).length < 2 ^ (prefixWord ++ tailWord_463677).sum := by decide
  have hdescent : baseEnd_463677 < baseStart_463677 := by decide
  rcases family_descends (prefixWord ++ tailWord_463677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463698 : List Nat := [3, 2, 2, 1, 1, 2, 5, 4]
def baseStart_463698 : Nat := 118140960795 + 463698 * 2 ^ 59
def prefixEnd_463698 : Nat := 4983230072969 + 3 ^ 40 * 463698 * 2
def baseEnd_463698 : Nat := 70548134082557633523703

theorem tailTrace_463698 : CollatzResearch.WordTrace tailWord_463698 prefixEnd_463698 70548134082557633523703 := by
  unfold tailWord_463698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4228113868527203539651937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11274970316072542772405165 4228113868527203539651937)
  ·
    refine ⟨3171085401395402654738953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4228113868527203539651937 3171085401395402654738953)
    ·
      refine ⟨2378314051046551991054215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3171085401395402654738953 2378314051046551991054215)
      ·
        refine ⟨3567471076569827986581323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378314051046551991054215 3567471076569827986581323)
        ·
          refine ⟨5351206614854741979871985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567471076569827986581323 5351206614854741979871985)
          ·
            refine ⟨4013404961141056484903989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5351206614854741979871985 4013404961141056484903989)
            ·
              refine ⟨376256715106974045459749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4013404961141056484903989 376256715106974045459749)
              ·
                refine ⟨70548134082557633523703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376256715106974045459749 70548134082557633523703)
                ·
                  rfl

theorem cell20_463698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_463698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463698 prefixEnd_463698 := by exact prefixLift 463698
  have htrace : WordTrace (prefixWord ++ tailWord_463698) baseStart_463698 baseEnd_463698 := by
    simpa [prefixWord, tailWord_463698, baseEnd_463698] using wordTrace_append hprefix tailTrace_463698
  have hstable : (prefixWord ++ tailWord_463698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463698).length < 2 ^ (prefixWord ++ tailWord_463698).sum := by decide
  have hdescent : baseEnd_463698 < baseStart_463698 := by decide
  rcases family_descends (prefixWord ++ tailWord_463698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463708 : List Nat := [2, 2, 4, 2, 1, 1, 1, 5, 2]
def baseStart_463708 : Nat := 118140960795 + 463708 * 2 ^ 59
def prefixEnd_463708 : Nat := 4983230072969 + 3 ^ 40 * 463708 * 2
def baseEnd_463708 : Nat := 211648966520157310237735

theorem tailTrace_463708 : CollatzResearch.WordTrace tailWord_463708 prefixEnd_463708 211648966520157310237735 := by
  unfold tailWord_463708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8456410102036292933235889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11275213469381723910981185 8456410102036292933235889)
  ·
    refine ⟨6342307576527219699926917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8456410102036292933235889 6342307576527219699926917)
    ·
      refine ⟨1189182670598853693736297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6342307576527219699926917 1189182670598853693736297)
      ·
        refine ⟨891887002949140270302223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1189182670598853693736297 891887002949140270302223)
        ·
          refine ⟨1337830504423710405453335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891887002949140270302223 1337830504423710405453335)
          ·
            refine ⟨2006745756635565608180003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337830504423710405453335 2006745756635565608180003)
            ·
              refine ⟨3010118634953348412270005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006745756635565608180003 3010118634953348412270005)
              ·
                refine ⟨282198622026876413650313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3010118634953348412270005 282198622026876413650313)
                ·
                  refine ⟨211648966520157310237735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282198622026876413650313 211648966520157310237735)
                  ·
                    rfl

theorem cell20_463708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_463708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463708 prefixEnd_463708 := by exact prefixLift 463708
  have htrace : WordTrace (prefixWord ++ tailWord_463708) baseStart_463708 baseEnd_463708 := by
    simpa [prefixWord, tailWord_463708, baseEnd_463708] using wordTrace_append hprefix tailTrace_463708
  have hstable : (prefixWord ++ tailWord_463708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463708).length < 2 ^ (prefixWord ++ tailWord_463708).sum := by decide
  have hdescent : baseEnd_463708 < baseStart_463708 := by decide
  rcases family_descends (prefixWord ++ tailWord_463708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463719 : List Nat := [1, 1, 5, 1, 2, 3, 7]
def baseStart_463719 : Nat := 118140960795 + 463719 * 2 ^ 59
def prefixEnd_463719 : Nat := 4983230072969 + 3 ^ 40 * 463719 * 2
def baseEnd_463719 : Nat := 23517109691098906763447

theorem tailTrace_463719 : CollatzResearch.WordTrace tailWord_463719 prefixEnd_463719 23517109691098906763447 := by
  unfold tailWord_463719
  simp only [CollatzResearch.WordTrace]
  refine ⟨16913221407032734745122211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11275480938021823163414807 16913221407032734745122211)
  ·
    refine ⟨25369832110549102117683317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16913221407032734745122211 25369832110549102117683317)
    ·
      refine ⟨2378421760363978323532811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25369832110549102117683317 2378421760363978323532811)
      ·
        refine ⟨3567632640545967485299217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378421760363978323532811 3567632640545967485299217)
        ·
          refine ⟨2675724480409475613974413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3567632640545967485299217 2675724480409475613974413)
          ·
            refine ⟨1003396680153553355240405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2675724480409475613974413 1003396680153553355240405)
            ·
              refine ⟨23517109691098906763447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1003396680153553355240405 23517109691098906763447)
              ·
                rfl

theorem cell20_463719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 7].length) (baseStart_463719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463719 prefixEnd_463719 := by exact prefixLift 463719
  have htrace : WordTrace (prefixWord ++ tailWord_463719) baseStart_463719 baseEnd_463719 := by
    simpa [prefixWord, tailWord_463719, baseEnd_463719] using wordTrace_append hprefix tailTrace_463719
  have hstable : (prefixWord ++ tailWord_463719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463719).length < 2 ^ (prefixWord ++ tailWord_463719).sum := by decide
  have hdescent : baseEnd_463719 < baseStart_463719 := by decide
  rcases family_descends (prefixWord ++ tailWord_463719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463729 : List Nat := [1, 2, 2, 2, 1, 4, 2, 4, 2]
def baseStart_463729 : Nat := 118140960795 + 463729 * 2 ^ 59
def prefixEnd_463729 : Nat := 4983230072969 + 3 ^ 40 * 463729 * 2
def baseEnd_463729 : Nat := 211658551492374570537649

theorem tailTrace_463729 : CollatzResearch.WordTrace tailWord_463729 prefixEnd_463729 211658551492374570537649 := by
  unfold tailWord_463729
  simp only [CollatzResearch.WordTrace]
  refine ⟨16913586136996506452986241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11275724091331004301990827 16913586136996506452986241)
  ·
    refine ⟨12685189602747379839739681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16913586136996506452986241 12685189602747379839739681)
    ·
      refine ⟨9513892202060534879804761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12685189602747379839739681 9513892202060534879804761)
      ·
        refine ⟨7135419151545401159853571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9513892202060534879804761 7135419151545401159853571)
        ·
          refine ⟨10703128727318101739780357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135419151545401159853571 10703128727318101739780357)
          ·
            refine ⟨2006836636372144076208817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10703128727318101739780357 2006836636372144076208817)
            ·
              refine ⟨1505127477279108057156613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006836636372144076208817 1505127477279108057156613)
              ·
                refine ⟨282211401989832760716865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1505127477279108057156613 282211401989832760716865)
                ·
                  refine ⟨211658551492374570537649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282211401989832760716865 211658551492374570537649)
                  ·
                    rfl

theorem cell20_463729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 2].length) (baseStart_463729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463729 prefixEnd_463729 := by exact prefixLift 463729
  have htrace : WordTrace (prefixWord ++ tailWord_463729) baseStart_463729 baseEnd_463729 := by
    simpa [prefixWord, tailWord_463729, baseEnd_463729] using wordTrace_append hprefix tailTrace_463729
  have hstable : (prefixWord ++ tailWord_463729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463729).length < 2 ^ (prefixWord ++ tailWord_463729).sum := by decide
  have hdescent : baseEnd_463729 < baseStart_463729 := by decide
  rcases family_descends (prefixWord ++ tailWord_463729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463839 : List Nat := [1, 1, 2, 3, 5, 2, 2, 2, 2]
def baseStart_463839 : Nat := 118140960795 + 463839 * 2 ^ 59
def prefixEnd_463839 : Nat := 4983230072969 + 3 ^ 40 * 463839 * 2
def baseEnd_463839 : Nat := 211708758489703076870533

theorem tailTrace_463839 : CollatzResearch.WordTrace tailWord_463839 prefixEnd_463839 211708758489703076870533 := by
  unfold tailWord_463839
  simp only [CollatzResearch.WordTrace]
  refine ⟨16917598166597995239490571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11278398777731996826327047 16917598166597995239490571)
  ·
    refine ⟨25376397249896992859235857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16917598166597995239490571 25376397249896992859235857)
    ·
      refine ⟨19032297937422744644426893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25376397249896992859235857 19032297937422744644426893)
      ·
        refine ⟨7137111726533529241660085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19032297937422744644426893 7137111726533529241660085)
        ·
          refine ⟨669104224362518366405633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7137111726533529241660085 669104224362518366405633)
          ·
            refine ⟨501828168271888774804225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669104224362518366405633 501828168271888774804225)
            ·
              refine ⟨376371126203916581103169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501828168271888774804225 376371126203916581103169)
              ·
                refine ⟨282278344652937435827377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376371126203916581103169 282278344652937435827377)
                ·
                  refine ⟨211708758489703076870533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282278344652937435827377 211708758489703076870533)
                  ·
                    rfl

theorem cell20_463839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 2].length) (baseStart_463839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463839 prefixEnd_463839 := by exact prefixLift 463839
  have htrace : WordTrace (prefixWord ++ tailWord_463839) baseStart_463839 baseEnd_463839 := by
    simpa [prefixWord, tailWord_463839, baseEnd_463839] using wordTrace_append hprefix tailTrace_463839
  have hstable : (prefixWord ++ tailWord_463839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463839).length < 2 ^ (prefixWord ++ tailWord_463839).sum := by decide
  have hdescent : baseEnd_463839 < baseStart_463839 := by decide
  rcases family_descends (prefixWord ++ tailWord_463839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463843 : List Nat := [1, 1, 1, 6, 1, 1, 3, 4, 2]
def baseStart_463843 : Nat := 118140960795 + 463843 * 2 ^ 59
def prefixEnd_463843 : Nat := 4983230072969 + 3 ^ 40 * 463843 * 2
def baseEnd_463843 : Nat := 211710584198696840737183

theorem tailTrace_463843 : CollatzResearch.WordTrace tailWord_463843 prefixEnd_463843 211710584198696840737183 := by
  unfold tailWord_463843
  simp only [CollatzResearch.WordTrace]
  refine ⟨16917744058583503922636183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11278496039055669281757455 16917744058583503922636183)
  ·
    refine ⟨25376616087875255883954275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16917744058583503922636183 25376616087875255883954275)
    ·
      refine ⟨38064924131812883825931413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25376616087875255883954275 38064924131812883825931413)
      ·
        refine ⟨1784293318678728929340535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38064924131812883825931413 1784293318678728929340535)
        ·
          refine ⟨2676439978018093394010803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784293318678728929340535 2676439978018093394010803)
          ·
            refine ⟨4014659967027140091016205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676439978018093394010803 4014659967027140091016205)
            ·
              refine ⟨1505497487635177534131077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4014659967027140091016205 1505497487635177534131077)
              ·
                refine ⟨282280778931595787649577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1505497487635177534131077 282280778931595787649577)
                ·
                  refine ⟨211710584198696840737183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282280778931595787649577 211710584198696840737183)
                  ·
                    rfl

theorem cell20_463843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 2].length) (baseStart_463843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463843 prefixEnd_463843 := by exact prefixLift 463843
  have htrace : WordTrace (prefixWord ++ tailWord_463843) baseStart_463843 baseEnd_463843 := by
    simpa [prefixWord, tailWord_463843, baseEnd_463843] using wordTrace_append hprefix tailTrace_463843
  have hstable : (prefixWord ++ tailWord_463843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463843).length < 2 ^ (prefixWord ++ tailWord_463843).sum := by decide
  have hdescent : baseEnd_463843 < baseStart_463843 := by decide
  rcases family_descends (prefixWord ++ tailWord_463843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463850 : List Nat := [3, 1, 3, 1, 2, 4, 1, 5]
def baseStart_463850 : Nat := 118140960795 + 463850 * 2 ^ 59
def prefixEnd_463850 : Nat := 4983230072969 + 3 ^ 40 * 463850 * 2
def baseEnd_463850 : Nat := 70571259729811975834607

theorem tailTrace_463850 : CollatzResearch.WordTrace tailWord_463850 prefixEnd_463850 70571259729811975834607 := by
  unfold tailWord_463850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229499842389536029535251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11278666246372096078760669 4229499842389536029535251)
  ·
    refine ⟨6344249763584304044302877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4229499842389536029535251 6344249763584304044302877)
    ·
      refine ⟨2379093661344114016613579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6344249763584304044302877 2379093661344114016613579)
      ·
        refine ⟨3568640492016171024920369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2379093661344114016613579 3568640492016171024920369)
        ·
          refine ⟨2676480369012128268690277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3568640492016171024920369 2676480369012128268690277)
          ·
            refine ⟨501840069189774050379427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2676480369012128268690277 501840069189774050379427)
            ·
              refine ⟨752760103784661075569141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501840069189774050379427 752760103784661075569141)
              ·
                refine ⟨70571259729811975834607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 752760103784661075569141 70571259729811975834607)
                ·
                  rfl

theorem cell20_463850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_463850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463850 prefixEnd_463850 := by exact prefixLift 463850
  have htrace : WordTrace (prefixWord ++ tailWord_463850) baseStart_463850 baseEnd_463850 := by
    simpa [prefixWord, tailWord_463850, baseEnd_463850] using wordTrace_append hprefix tailTrace_463850
  have hstable : (prefixWord ++ tailWord_463850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463850).length < 2 ^ (prefixWord ++ tailWord_463850).sum := by decide
  have hdescent : baseEnd_463850 < baseStart_463850 := by decide
  rcases family_descends (prefixWord ++ tailWord_463850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463857 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 3]
def baseStart_463857 : Nat := 118140960795 + 463857 * 2 ^ 59
def prefixEnd_463857 : Nat := 4983230072969 + 3 ^ 40 * 463857 * 2
def baseEnd_463857 : Nat := 211716974180175014270459

theorem tailTrace_463857 : CollatzResearch.WordTrace tailWord_463857 prefixEnd_463857 211716974180175014270459 := by
  unfold tailWord_463857
  simp only [CollatzResearch.WordTrace]
  refine ⟨16918254680532784313645825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11278836453688522875763883 16918254680532784313645825)
  ·
    refine ⟨12688691010399588235234369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16918254680532784313645825 12688691010399588235234369)
    ·
      refine ⟨9516518257799691176425777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12688691010399588235234369 9516518257799691176425777)
      ·
        refine ⟨7137388693349768382319333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9516518257799691176425777 7137388693349768382319333)
        ·
          refine ⟨1338260380003081571684875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7137388693349768382319333 1338260380003081571684875)
          ·
            refine ⟨2007390570004622357527313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338260380003081571684875 2007390570004622357527313)
            ·
              refine ⟨1505542927503466768145485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007390570004622357527313 1505542927503466768145485)
              ·
                refine ⟨564578597813800038054557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1505542927503466768145485 564578597813800038054557)
                ·
                  refine ⟨211716974180175014270459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564578597813800038054557 211716974180175014270459)
                  ·
                    rfl

theorem cell20_463857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_463857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463857 prefixEnd_463857 := by exact prefixLift 463857
  have htrace : WordTrace (prefixWord ++ tailWord_463857) baseStart_463857 baseEnd_463857 := by
    simpa [prefixWord, tailWord_463857, baseEnd_463857] using wordTrace_append hprefix tailTrace_463857
  have hstable : (prefixWord ++ tailWord_463857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463857).length < 2 ^ (prefixWord ++ tailWord_463857).sum := by decide
  have hdescent : baseEnd_463857 < baseStart_463857 := by decide
  rcases family_descends (prefixWord ++ tailWord_463857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463895 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 5]
def baseStart_463895 : Nat := 118140960795 + 463895 * 2 ^ 59
def prefixEnd_463895 : Nat := 4983230072969 + 3 ^ 40 * 463895 * 2
def baseEnd_463895 : Nat := 211734318415615771003637

theorem tailTrace_463895 : CollatzResearch.WordTrace tailWord_463895 prefixEnd_463895 211734318415615771003637 := by
  unfold tailWord_463895
  simp only [CollatzResearch.WordTrace]
  refine ⟨16919640654395116803529139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11279760436263411202352759 16919640654395116803529139)
  ·
    refine ⟨25379460981592675205293709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16919640654395116803529139 25379460981592675205293709)
    ·
      refine ⟨9517297868097253201985141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25379460981592675205293709 9517297868097253201985141)
      ·
        refine ⟨892246675134117487686107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9517297868097253201985141 892246675134117487686107)
        ·
          refine ⟨1338370012701176231529161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892246675134117487686107 1338370012701176231529161)
          ·
            refine ⟨1003777509525882173646871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338370012701176231529161 1003777509525882173646871)
            ·
              refine ⟨1505666264288823260470307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003777509525882173646871 1505666264288823260470307)
              ·
                refine ⟨2258499396433234890705461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505666264288823260470307 2258499396433234890705461)
                ·
                  refine ⟨211734318415615771003637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2258499396433234890705461 211734318415615771003637)
                  ·
                    rfl

theorem cell20_463895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_463895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463895 prefixEnd_463895 := by exact prefixLift 463895
  have htrace : WordTrace (prefixWord ++ tailWord_463895) baseStart_463895 baseEnd_463895 := by
    simpa [prefixWord, tailWord_463895, baseEnd_463895] using wordTrace_append hprefix tailTrace_463895
  have hstable : (prefixWord ++ tailWord_463895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463895).length < 2 ^ (prefixWord ++ tailWord_463895).sum := by decide
  have hdescent : baseEnd_463895 < baseStart_463895 := by decide
  rcases family_descends (prefixWord ++ tailWord_463895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463926 : List Nat := [5, 1, 2, 1, 1, 3, 1, 6]
def baseStart_463926 : Nat := 118140960795 + 463926 * 2 ^ 59
def prefixEnd_463926 : Nat := 4983230072969 + 3 ^ 40 * 463926 * 2
def baseEnd_463926 : Nat := 70582822553439146990059

theorem tailTrace_463926 : CollatzResearch.WordTrace tailWord_463926 prefixEnd_463926 70582822553439146990059 := by
  unfold tailWord_463926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057548207330175568619227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11280514211521872731938421 1057548207330175568619227)
  ·
    refine ⟨1586322310995263352928841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1057548207330175568619227 1586322310995263352928841)
    ·
      refine ⟨1189741733246447514696631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1586322310995263352928841 1189741733246447514696631)
      ·
        refine ⟨1784612599869671272044947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1189741733246447514696631 1784612599869671272044947)
        ·
          refine ⟨2676918899804506908067421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784612599869671272044947 2676918899804506908067421)
          ·
            refine ⟨1003844587426690090525283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2676918899804506908067421 1003844587426690090525283)
            ·
              refine ⟨1505766881140035135787925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003844587426690090525283 1505766881140035135787925)
              ·
                refine ⟨70582822553439146990059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1505766881140035135787925 70582822553439146990059)
                ·
                  rfl

theorem cell20_463926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_463926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463926 prefixEnd_463926 := by exact prefixLift 463926
  have htrace : WordTrace (prefixWord ++ tailWord_463926) baseStart_463926 baseEnd_463926 := by
    simpa [prefixWord, tailWord_463926, baseEnd_463926] using wordTrace_append hprefix tailTrace_463926
  have hstable : (prefixWord ++ tailWord_463926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463926).length < 2 ^ (prefixWord ++ tailWord_463926).sum := by decide
  have hdescent : baseEnd_463926 < baseStart_463926 := by decide
  rcases family_descends (prefixWord ++ tailWord_463926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463961 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 4]
def baseStart_463961 : Nat := 118140960795 + 463961 * 2 ^ 59
def prefixEnd_463961 : Nat := 4983230072969 + 3 ^ 40 * 463961 * 2
def baseEnd_463961 : Nat := 211764442614012874803367

theorem tailTrace_463961 : CollatzResearch.WordTrace tailWord_463961 prefixEnd_463961 211764442614012874803367 := by
  unfold tailWord_463961
  simp only [CollatzResearch.WordTrace]
  refine ⟨16922047872156010075431737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11281365248104006716954491 16922047872156010075431737)
  ·
    refine ⟨12691535904117007556573803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16922047872156010075431737 12691535904117007556573803)
    ·
      refine ⟨19037303856175511334860705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12691535904117007556573803 19037303856175511334860705)
      ·
        refine ⟨14277977892131633501145529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19037303856175511334860705 14277977892131633501145529)
        ·
          refine ⟨10708483419098725125859147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14277977892131633501145529 10708483419098725125859147)
          ·
            refine ⟨16062725128648087688788721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10708483419098725125859147 16062725128648087688788721)
            ·
              refine ⟨12047043846486065766591541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16062725128648087688788721 12047043846486065766591541)
              ·
                refine ⟨1129410360608068665617957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12047043846486065766591541 1129410360608068665617957)
                ·
                  refine ⟨211764442614012874803367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1129410360608068665617957 211764442614012874803367)
                  ·
                    rfl

theorem cell20_463961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_463961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463961 prefixEnd_463961 := by exact prefixLift 463961
  have htrace : WordTrace (prefixWord ++ tailWord_463961) baseStart_463961 baseEnd_463961 := by
    simpa [prefixWord, tailWord_463961, baseEnd_463961] using wordTrace_append hprefix tailTrace_463961
  have hstable : (prefixWord ++ tailWord_463961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463961).length < 2 ^ (prefixWord ++ tailWord_463961).sum := by decide
  have hdescent : baseEnd_463961 < baseStart_463961 := by decide
  rcases family_descends (prefixWord ++ tailWord_463961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463998 : List Nat := [4, 2, 4, 1, 2, 7]
def baseStart_463998 : Nat := 118140960795 + 463998 * 2 ^ 59
def prefixEnd_463998 : Nat := 4983230072969 + 3 ^ 40 * 463998 * 2
def baseEnd_463998 : Nat := 7843752978600192243329

theorem tailTrace_463998 : CollatzResearch.WordTrace tailWord_463998 prefixEnd_463998 7843752978600192243329 := by
  unfold tailWord_463998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115424671627745674316081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11282264915347976929685765 2115424671627745674316081)
  ·
    refine ⟨1586568503720809255737061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2115424671627745674316081 1586568503720809255737061)
    ·
      refine ⟨297481594447651735450699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1586568503720809255737061 297481594447651735450699)
      ·
        refine ⟨446222391671477603176049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297481594447651735450699 446222391671477603176049)
        ·
          refine ⟨334666793753608202382037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446222391671477603176049 334666793753608202382037)
          ·
            refine ⟨7843752978600192243329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 334666793753608202382037 7843752978600192243329)
            ·
              rfl

theorem cell20_463998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 7].length) (baseStart_463998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_463998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_463998 prefixEnd_463998 := by exact prefixLift 463998
  have htrace : WordTrace (prefixWord ++ tailWord_463998) baseStart_463998 baseEnd_463998 := by
    simpa [prefixWord, tailWord_463998, baseEnd_463998] using wordTrace_append hprefix tailTrace_463998
  have hstable : (prefixWord ++ tailWord_463998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463998).length < 2 ^ (prefixWord ++ tailWord_463998).sum := by decide
  have hdescent : baseEnd_463998 < baseStart_463998 := by decide
  rcases family_descends (prefixWord ++ tailWord_463998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464008 : List Nat := [2, 1, 3, 4, 3, 1, 2, 2, 2]
def baseStart_464008 : Nat := 118140960795 + 464008 * 2 ^ 59
def prefixEnd_464008 : Nat := 4983230072969 + 3 ^ 40 * 464008 * 2
def baseEnd_464008 : Nat := 211785894694689600236509

theorem tailTrace_464008 : CollatzResearch.WordTrace tailWord_464008 prefixEnd_464008 211785894694689600236509 := by
  unfold tailWord_464008
  simp only [CollatzResearch.WordTrace]
  refine ⟨8461881051492868551196339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11282508068657158068261785 8461881051492868551196339)
  ·
    refine ⟨12692821577239302826794509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8461881051492868551196339 12692821577239302826794509)
    ·
      refine ⟨4759808091464738560047941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12692821577239302826794509 4759808091464738560047941)
      ·
        refine ⟨892464017149638480008989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4759808091464738560047941 892464017149638480008989)
        ·
          refine ⟨334674006431114430003371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 892464017149638480008989 334674006431114430003371)
          ·
            refine ⟨502011009646671645005057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334674006431114430003371 502011009646671645005057)
            ·
              refine ⟨376508257235003733753793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502011009646671645005057 376508257235003733753793)
              ·
                refine ⟨282381192926252800315345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 376508257235003733753793 282381192926252800315345)
                ·
                  refine ⟨211785894694689600236509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282381192926252800315345 211785894694689600236509)
                  ·
                    rfl

theorem cell20_464008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 2].length) (baseStart_464008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464008 prefixEnd_464008 := by exact prefixLift 464008
  have htrace : WordTrace (prefixWord ++ tailWord_464008) baseStart_464008 baseEnd_464008 := by
    simpa [prefixWord, tailWord_464008, baseEnd_464008] using wordTrace_append hprefix tailTrace_464008
  have hstable : (prefixWord ++ tailWord_464008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464008).length < 2 ^ (prefixWord ++ tailWord_464008).sum := by decide
  have hdescent : baseEnd_464008 < baseStart_464008 := by decide
  rcases family_descends (prefixWord ++ tailWord_464008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464009 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 3]
def baseStart_464009 : Nat := 118140960795 + 464009 * 2 ^ 59
def prefixEnd_464009 : Nat := 4983230072969 + 3 ^ 40 * 464009 * 2
def baseEnd_464009 : Nat := 211786351121938041203171

theorem tailTrace_464009 : CollatzResearch.WordTrace tailWord_464009 prefixEnd_464009 211786351121938041203171 := by
  unfold tailWord_464009
  simp only [CollatzResearch.WordTrace]
  refine ⟨16923798575982114273179081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11282532383988076182119387 16923798575982114273179081)
  ·
    refine ⟨12692848931986585704884311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16923798575982114273179081 12692848931986585704884311)
    ·
      refine ⟨19039273397979878557326467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12692848931986585704884311 19039273397979878557326467)
      ·
        refine ⟨28558910096969817835989701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19039273397979878557326467 28558910096969817835989701)
        ·
          refine ⟨5354795643181840844248069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28558910096969817835989701 5354795643181840844248069)
          ·
            refine ⟨1004024183096595158296513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5354795643181840844248069 1004024183096595158296513)
            ·
              refine ⟨753018137322446368722385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004024183096595158296513 753018137322446368722385)
              ·
                refine ⟨564763602991834776541789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753018137322446368722385 564763602991834776541789)
                ·
                  refine ⟨211786351121938041203171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564763602991834776541789 211786351121938041203171)
                  ·
                    rfl

theorem cell20_464009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_464009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464009 prefixEnd_464009 := by exact prefixLift 464009
  have htrace : WordTrace (prefixWord ++ tailWord_464009) baseStart_464009 baseEnd_464009 := by
    simpa [prefixWord, tailWord_464009, baseEnd_464009] using wordTrace_append hprefix tailTrace_464009
  have hstable : (prefixWord ++ tailWord_464009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464009).length < 2 ^ (prefixWord ++ tailWord_464009).sum := by decide
  have hdescent : baseEnd_464009 < baseStart_464009 := by decide
  rcases family_descends (prefixWord ++ tailWord_464009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464023 : List Nat := [1, 1, 3, 3, 3, 1, 3, 5]
def baseStart_464023 : Nat := 118140960795 + 464023 * 2 ^ 59
def prefixEnd_464023 : Nat := 4983230072969 + 3 ^ 40 * 464023 * 2
def baseEnd_464023 : Nat := 70597580367805404912149

theorem tailTrace_464023 : CollatzResearch.WordTrace tailWord_464023 prefixEnd_464023 70597580367805404912149 := by
  unfold tailWord_464023
  simp only [CollatzResearch.WordTrace]
  refine ⟨16924309197931394664188723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11282872798620929776125815 16924309197931394664188723)
  ·
    refine ⟨25386463796897091996283085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16924309197931394664188723 25386463796897091996283085)
    ·
      refine ⟨9519923923836409498606157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25386463796897091996283085 9519923923836409498606157)
      ·
        refine ⟨3569971471438653561977309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9519923923836409498606157 3569971471438653561977309)
        ·
          refine ⟨1338739301789495085741491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3569971471438653561977309 1338739301789495085741491)
          ·
            refine ⟨2008108952684242628612237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338739301789495085741491 2008108952684242628612237)
            ·
              refine ⟨753040857256590985729589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2008108952684242628612237 753040857256590985729589)
              ·
                refine ⟨70597580367805404912149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 753040857256590985729589 70597580367805404912149)
                ·
                  rfl

theorem cell20_464023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_464023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464023 prefixEnd_464023 := by exact prefixLift 464023
  have htrace : WordTrace (prefixWord ++ tailWord_464023) baseStart_464023 baseEnd_464023 := by
    simpa [prefixWord, tailWord_464023, baseEnd_464023] using wordTrace_append hprefix tailTrace_464023
  have hstable : (prefixWord ++ tailWord_464023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464023).length < 2 ^ (prefixWord ++ tailWord_464023).sum := by decide
  have hdescent : baseEnd_464023 < baseStart_464023 := by decide
  rcases family_descends (prefixWord ++ tailWord_464023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464037 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 6]
def baseStart_464037 : Nat := 118140960795 + 464037 * 2 ^ 59
def prefixEnd_464037 : Nat := 4983230072969 + 3 ^ 40 * 464037 * 2
def baseEnd_464037 : Nat := 211799131084894388269723

theorem tailTrace_464037 : CollatzResearch.WordTrace tailWord_464037 prefixEnd_464037 211799131084894388269723 := by
  unfold tailWord_464037
  simp only [CollatzResearch.WordTrace]
  refine ⟨16924819819880675055198365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11283213213253783370132243 16924819819880675055198365)
  ·
    refine ⟨6346807432455253145699387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16924819819880675055198365 6346807432455253145699387)
    ·
      refine ⟨9520211148682879718549081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6346807432455253145699387 9520211148682879718549081)
      ·
        refine ⟨7140158361512159788911811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9520211148682879718549081 7140158361512159788911811)
        ·
          refine ⟨10710237542268239683367717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7140158361512159788911811 10710237542268239683367717)
          ·
            refine ⟨2008169539175294940631447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10710237542268239683367717 2008169539175294940631447)
            ·
              refine ⟨3012254308762942410947171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008169539175294940631447 3012254308762942410947171)
              ·
                refine ⟨4518381463144413616420757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012254308762942410947171 4518381463144413616420757)
                ·
                  refine ⟨211799131084894388269723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4518381463144413616420757 211799131084894388269723)
                  ·
                    rfl

theorem cell20_464037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_464037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464037 prefixEnd_464037 := by exact prefixLift 464037
  have htrace : WordTrace (prefixWord ++ tailWord_464037) baseStart_464037 baseEnd_464037 := by
    simpa [prefixWord, tailWord_464037, baseEnd_464037] using wordTrace_append hprefix tailTrace_464037
  have hstable : (prefixWord ++ tailWord_464037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464037).length < 2 ^ (prefixWord ++ tailWord_464037).sum := by decide
  have hdescent : baseEnd_464037 < baseStart_464037 := by decide
  rcases family_descends (prefixWord ++ tailWord_464037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464064 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 3]
def baseStart_464064 : Nat := 118140960795 + 464064 * 2 ^ 59
def prefixEnd_464064 : Nat := 4983230072969 + 3 ^ 40 * 464064 * 2
def baseEnd_464064 : Nat := 211811454620602294369613

theorem tailTrace_464064 : CollatzResearch.WordTrace tailWord_464064 prefixEnd_464064 211811454620602294369613 := by
  unfold tailWord_464064
  simp only [CollatzResearch.WordTrace]
  refine ⟨8462902295391429333215623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11283869727188572444287497 8462902295391429333215623)
  ·
    refine ⟨12694353443087143999823435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8462902295391429333215623 12694353443087143999823435)
    ·
      refine ⟨19041530164630715999735153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12694353443087143999823435 19041530164630715999735153)
      ·
        refine ⟨14281147623473036999801365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19041530164630715999735153 14281147623473036999801365)
        ·
          refine ⟨669428794850298609365689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14281147623473036999801365 669428794850298609365689)
          ·
            refine ⟨502071596137723957024267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669428794850298609365689 502071596137723957024267)
            ·
              refine ⟨753107394206585935536401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502071596137723957024267 753107394206585935536401)
              ·
                refine ⟨564830545654939451652301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753107394206585935536401 564830545654939451652301)
                ·
                  refine ⟨211811454620602294369613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564830545654939451652301 211811454620602294369613)
                  ·
                    rfl

theorem cell20_464064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_464064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464064 prefixEnd_464064 := by exact prefixLift 464064
  have htrace : WordTrace (prefixWord ++ tailWord_464064) baseStart_464064 baseEnd_464064 := by
    simpa [prefixWord, tailWord_464064, baseEnd_464064] using wordTrace_append hprefix tailTrace_464064
  have hstable : (prefixWord ++ tailWord_464064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464064).length < 2 ^ (prefixWord ++ tailWord_464064).sum := by decide
  have hdescent : baseEnd_464064 < baseStart_464064 := by decide
  rcases family_descends (prefixWord ++ tailWord_464064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464106 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_464106 : Nat := 118140960795 + 464106 * 2 ^ 59
def prefixEnd_464106 : Nat := 4983230072969 + 3 ^ 40 * 464106 * 2
def baseEnd_464106 : Nat := 211830624565036814969441

theorem tailTrace_464106 : CollatzResearch.WordTrace tailWord_464106 prefixEnd_464106 211830624565036814969441 := by
  unfold tailWord_464106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4231834114157674959865043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11284890971087133226306781 4231834114157674959865043)
  ·
    refine ⟨6347751171236512439797565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4231834114157674959865043 6347751171236512439797565)
    ·
      refine ⟨2380406689213692164924087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6347751171236512439797565 2380406689213692164924087)
      ·
        refine ⟨3570610033820538247386131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380406689213692164924087 3570610033820538247386131)
        ·
          refine ⟨5355915050730807371079197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3570610033820538247386131 5355915050730807371079197)
          ·
            refine ⟨2008468144024052764154699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5355915050730807371079197 2008468144024052764154699)
            ·
              refine ⟨3012702216036079146232049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008468144024052764154699 3012702216036079146232049)
              ·
                refine ⟨2259526662027059359674037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012702216036079146232049 2259526662027059359674037)
                ·
                  refine ⟨211830624565036814969441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2259526662027059359674037 211830624565036814969441)
                  ·
                    rfl

theorem cell20_464106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_464106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464106 prefixEnd_464106 := by exact prefixLift 464106
  have htrace : WordTrace (prefixWord ++ tailWord_464106) baseStart_464106 baseEnd_464106 := by
    simpa [prefixWord, tailWord_464106, baseEnd_464106] using wordTrace_append hprefix tailTrace_464106
  have hstable : (prefixWord ++ tailWord_464106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464106).length < 2 ^ (prefixWord ++ tailWord_464106).sum := by decide
  have hdescent : baseEnd_464106 < baseStart_464106 := by decide
  rcases family_descends (prefixWord ++ tailWord_464106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464140 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 3]
def baseStart_464140 : Nat := 118140960795 + 464140 * 2 ^ 59
def prefixEnd_464140 : Nat := 4983230072969 + 3 ^ 40 * 464140 * 2
def baseEnd_464140 : Nat := 211846143091483807835969

theorem tailTrace_464140 : CollatzResearch.WordTrace tailWord_464140 prefixEnd_464140 211846143091483807835969 := by
  unfold tailWord_464140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8464288269253761823098937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11285717692338349097465249 8464288269253761823098937)
  ·
    refine ⟨6348216201940321367324203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8464288269253761823098937 6348216201940321367324203)
    ·
      refine ⟨9522324302910482050986305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6348216201940321367324203 9522324302910482050986305)
      ·
        refine ⟨7141743227182861538239729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9522324302910482050986305 7141743227182861538239729)
        ·
          refine ⟨5356307420387146153679797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7141743227182861538239729 5356307420387146153679797)
          ·
            refine ⟨502153820661294951907481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5356307420387146153679797 502153820661294951907481)
            ·
              refine ⟨376615365495971213930611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502153820661294951907481 376615365495971213930611)
              ·
                refine ⟨564923048243956820895917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376615365495971213930611 564923048243956820895917)
                ·
                  refine ⟨211846143091483807835969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564923048243956820895917 211846143091483807835969)
                  ·
                    rfl

theorem cell20_464140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_464140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464140 prefixEnd_464140 := by exact prefixLift 464140
  have htrace : WordTrace (prefixWord ++ tailWord_464140) baseStart_464140 baseEnd_464140 := by
    simpa [prefixWord, tailWord_464140, baseEnd_464140] using wordTrace_append hprefix tailTrace_464140
  have hstable : (prefixWord ++ tailWord_464140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464140).length < 2 ^ (prefixWord ++ tailWord_464140).sum := by decide
  have hdescent : baseEnd_464140 < baseStart_464140 := by decide
  rcases family_descends (prefixWord ++ tailWord_464140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464151 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 6]
def baseStart_464151 : Nat := 118140960795 + 464151 * 2 ^ 59
def prefixEnd_464151 : Nat := 4983230072969 + 3 ^ 40 * 464151 * 2
def baseEnd_464151 : Nat := 211851163791216658469257

theorem tailTrace_464151 : CollatzResearch.WordTrace tailWord_464151 prefixEnd_464151 211851163791216658469257 := by
  unfold tailWord_464151
  simp only [CollatzResearch.WordTrace]
  refine ⟨16928977741467672524848307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11285985160978448349898871 16928977741467672524848307)
  ·
    refine ⟨25393466612201508787272461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16928977741467672524848307 25393466612201508787272461)
    ·
      refine ⟨9522549979575565795227173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25393466612201508787272461 9522549979575565795227173)
      ·
        refine ⟨1785478121170418586605095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9522549979575565795227173 1785478121170418586605095)
        ·
          refine ⟨2678217181755627879907643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785478121170418586605095 2678217181755627879907643)
          ·
            refine ⟨4017325772633441819861465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678217181755627879907643 4017325772633441819861465)
            ·
              refine ⟨3012994329475081364896099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4017325772633441819861465 3012994329475081364896099)
              ·
                refine ⟨4519491494212622047344149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012994329475081364896099 4519491494212622047344149)
                ·
                  refine ⟨211851163791216658469257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4519491494212622047344149 211851163791216658469257)
                  ·
                    rfl

theorem cell20_464151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_464151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464151 prefixEnd_464151 := by exact prefixLift 464151
  have htrace : WordTrace (prefixWord ++ tailWord_464151) baseStart_464151 baseEnd_464151 := by
    simpa [prefixWord, tailWord_464151, baseEnd_464151] using wordTrace_append hprefix tailTrace_464151
  have hstable : (prefixWord ++ tailWord_464151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464151).length < 2 ^ (prefixWord ++ tailWord_464151).sum := by decide
  have hdescent : baseEnd_464151 < baseStart_464151 := by decide
  rcases family_descends (prefixWord ++ tailWord_464151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464237 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 3]
def baseStart_464237 : Nat := 118140960795 + 464237 * 2 ^ 59
def prefixEnd_464237 : Nat := 4983230072969 + 3 ^ 40 * 464237 * 2
def baseEnd_464237 : Nat := 211890416534582581602239

theorem tailTrace_464237 : CollatzResearch.WordTrace tailWord_464237 prefixEnd_464237 211890416534582581602239 := by
  unfold tailWord_464237
  simp only [CollatzResearch.WordTrace]
  refine ⟨16932114419156109212478965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11288076279437406141652643 16932114419156109212478965)
  ·
    refine ⟨1587385726795885238669903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16932114419156109212478965 1587385726795885238669903)
    ·
      refine ⟨2381078590193827858004855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1587385726795885238669903 2381078590193827858004855)
      ·
        refine ⟨3571617885290741787007283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381078590193827858004855 3571617885290741787007283)
        ·
          refine ⟨5357426827936112680510925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571617885290741787007283 5357426827936112680510925)
          ·
            refine ⟨2009035060476042255191597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5357426827936112680510925 2009035060476042255191597)
            ·
              refine ⟨753388147678515845696849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2009035060476042255191597 753388147678515845696849)
              ·
                refine ⟨565041110758886884272637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753388147678515845696849 565041110758886884272637)
                ·
                  refine ⟨211890416534582581602239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565041110758886884272637 211890416534582581602239)
                  ·
                    rfl

theorem cell20_464237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_464237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464237 prefixEnd_464237 := by exact prefixLift 464237
  have htrace : WordTrace (prefixWord ++ tailWord_464237) baseStart_464237 baseEnd_464237 := by
    simpa [prefixWord, tailWord_464237, baseEnd_464237] using wordTrace_append hprefix tailTrace_464237
  have hstable : (prefixWord ++ tailWord_464237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464237).length < 2 ^ (prefixWord ++ tailWord_464237).sum := by decide
  have hdescent : baseEnd_464237 < baseStart_464237 := by decide
  rcases family_descends (prefixWord ++ tailWord_464237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464274 : List Nat := [3, 2, 3, 3, 2, 1, 1, 3, 2]
def baseStart_464274 : Nat := 118140960795 + 464274 * 2 ^ 59
def prefixEnd_464274 : Nat := 4983230072969 + 3 ^ 40 * 464274 * 2
def baseEnd_464274 : Nat := 211907304342774897368755

theorem tailTrace_464274 : CollatzResearch.WordTrace tailWord_464274 prefixEnd_464274 211907304342774897368755 := by
  unfold tailWord_464274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4233365980005516132893969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11288975946681376354383917 4233365980005516132893969)
  ·
    refine ⟨3175024485004137099670477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4233365980005516132893969 3175024485004137099670477)
    ·
      refine ⟨1190634181876551412376429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3175024485004137099670477 1190634181876551412376429)
      ·
        refine ⟨446487818203706779641161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1190634181876551412376429 446487818203706779641161)
        ·
          refine ⟨334865863652780084730871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446487818203706779641161 334865863652780084730871)
          ·
            refine ⟨502298795479170127096307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334865863652780084730871 502298795479170127096307)
            ·
              refine ⟨753448193218755190644461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502298795479170127096307 753448193218755190644461)
              ·
                refine ⟨282543072457033196491673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 753448193218755190644461 282543072457033196491673)
                ·
                  refine ⟨211907304342774897368755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282543072457033196491673 211907304342774897368755)
                  ·
                    rfl

theorem cell20_464274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_464274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464274 prefixEnd_464274 := by exact prefixLift 464274
  have htrace : WordTrace (prefixWord ++ tailWord_464274) baseStart_464274 baseEnd_464274 := by
    simpa [prefixWord, tailWord_464274, baseEnd_464274] using wordTrace_append hprefix tailTrace_464274
  have hstable : (prefixWord ++ tailWord_464274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464274).length < 2 ^ (prefixWord ++ tailWord_464274).sum := by decide
  have hdescent : baseEnd_464274 < baseStart_464274 := by decide
  rcases family_descends (prefixWord ++ tailWord_464274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464313 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 3]
def baseStart_464313 : Nat := 118140960795 + 464313 * 2 ^ 59
def prefixEnd_464313 : Nat := 4983230072969 + 3 ^ 40 * 464313 * 2
def baseEnd_464313 : Nat := 211925105005464095068595

theorem tailTrace_464313 : CollatzResearch.WordTrace tailWord_464313 prefixEnd_464313 211925105005464095068595 := by
  unfold tailWord_464313
  simp only [CollatzResearch.WordTrace]
  refine ⟨16934886366880774192245593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11289924244587182794830395 16934886366880774192245593)
  ·
    refine ⟨12701164775160580644184195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16934886366880774192245593 12701164775160580644184195)
    ·
      refine ⟨19051747162740870966276293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12701164775160580644184195 19051747162740870966276293)
      ·
        refine ⟨3572202593013913306176805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19051747162740870966276293 3572202593013913306176805)
        ·
          refine ⟨669787986190108744908151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3572202593013913306176805 669787986190108744908151)
          ·
            refine ⟨1004681979285163117362227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669787986190108744908151 1004681979285163117362227)
            ·
              refine ⟨1507022968927744676043341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004681979285163117362227 1507022968927744676043341)
              ·
                refine ⟨565133613347904253516253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1507022968927744676043341 565133613347904253516253)
                ·
                  refine ⟨211925105005464095068595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565133613347904253516253 211925105005464095068595)
                  ·
                    rfl

theorem cell20_464313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_464313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464313 prefixEnd_464313 := by exact prefixLift 464313
  have htrace : WordTrace (prefixWord ++ tailWord_464313) baseStart_464313 baseEnd_464313 := by
    simpa [prefixWord, tailWord_464313, baseEnd_464313] using wordTrace_append hprefix tailTrace_464313
  have hstable : (prefixWord ++ tailWord_464313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464313).length < 2 ^ (prefixWord ++ tailWord_464313).sum := by decide
  have hdescent : baseEnd_464313 < baseStart_464313 := by decide
  rcases family_descends (prefixWord ++ tailWord_464313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464393 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_464393 : Nat := 118140960795 + 464393 * 2 ^ 59
def prefixEnd_464393 : Nat := 4983230072969 + 3 ^ 40 * 464393 * 2
def baseEnd_464393 : Nat := 211961619185339372401601

theorem tailTrace_464393 : CollatzResearch.WordTrace tailWord_464393 prefixEnd_464393 211961619185339372401601 := by
  unfold tailWord_464393
  simp only [CollatzResearch.WordTrace]
  refine ⟨16937804206590947855157833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11291869471060631903438555 16937804206590947855157833)
  ·
    refine ⟨12703353154943210891368375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16937804206590947855157833 12703353154943210891368375)
    ·
      refine ⟨19055029732414816337052563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12703353154943210891368375 19055029732414816337052563)
      ·
        refine ⟨28582544598622224505578845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19055029732414816337052563 28582544598622224505578845)
        ·
          refine ⟨10718454224483334189592067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28582544598622224505578845 10718454224483334189592067)
          ·
            refine ⟨16077681336725001284388101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10718454224483334189592067 16077681336725001284388101)
            ·
              refine ⟨3014565250635937740822769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16077681336725001284388101 3014565250635937740822769)
              ·
                refine ⟨2260923937976953305617077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3014565250635937740822769 2260923937976953305617077)
                ·
                  refine ⟨211961619185339372401601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2260923937976953305617077 211961619185339372401601)
                  ·
                    rfl

theorem cell20_464393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_464393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464393 prefixEnd_464393 := by exact prefixLift 464393
  have htrace : WordTrace (prefixWord ++ tailWord_464393) baseStart_464393 baseEnd_464393 := by
    simpa [prefixWord, tailWord_464393, baseEnd_464393] using wordTrace_append hprefix tailTrace_464393
  have hstable : (prefixWord ++ tailWord_464393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464393).length < 2 ^ (prefixWord ++ tailWord_464393).sum := by decide
  have hdescent : baseEnd_464393 < baseStart_464393 := by decide
  rcases family_descends (prefixWord ++ tailWord_464393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464417 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 4]
def baseStart_464417 : Nat := 118140960795 + 464417 * 2 ^ 59
def prefixEnd_464417 : Nat := 4983230072969 + 3 ^ 40 * 464417 * 2
def baseEnd_464417 : Nat := 211972573439301955601503

theorem tailTrace_464417 : CollatzResearch.WordTrace tailWord_464417 prefixEnd_464417 211972573439301955601503 := by
  unfold tailWord_464417
  simp only [CollatzResearch.WordTrace]
  refine ⟨16938679558503999954031505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11292453039002666636021003 16938679558503999954031505)
  ·
    refine ⟨12704009668877999965523629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16938679558503999954031505 12704009668877999965523629)
    ·
      refine ⟨4764003625829249987071361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12704009668877999965523629 4764003625829249987071361)
      ·
        refine ⟨3573002719371937490303521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4764003625829249987071361 3573002719371937490303521)
        ·
          refine ⟨2679752039528953117727641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3573002719371937490303521 2679752039528953117727641)
          ·
            refine ⟨2009814029646714838295731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679752039528953117727641 2009814029646714838295731)
            ·
              refine ⟨3014721044470072257443597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009814029646714838295731 3014721044470072257443597)
              ·
                refine ⟨1130520391676277096541349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3014721044470072257443597 1130520391676277096541349)
                ·
                  refine ⟨211972573439301955601503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1130520391676277096541349 211972573439301955601503)
                  ·
                    rfl

theorem cell20_464417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_464417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464417 prefixEnd_464417 := by exact prefixLift 464417
  have htrace : WordTrace (prefixWord ++ tailWord_464417) baseStart_464417 baseEnd_464417 := by
    simpa [prefixWord, tailWord_464417, baseEnd_464417] using wordTrace_append hprefix tailTrace_464417
  have hstable : (prefixWord ++ tailWord_464417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464417).length < 2 ^ (prefixWord ++ tailWord_464417).sum := by decide
  have hdescent : baseEnd_464417 < baseStart_464417 := by decide
  rcases family_descends (prefixWord ++ tailWord_464417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464441 : List Nat := [1, 2, 1, 5, 1, 2, 4, 4]
def baseStart_464441 : Nat := 118140960795 + 464441 * 2 ^ 59
def prefixEnd_464441 : Nat := 4983230072969 + 3 ^ 40 * 464441 * 2
def baseEnd_464441 : Nat := 70661175897754846267135

theorem tailTrace_464441 : CollatzResearch.WordTrace tailWord_464441 prefixEnd_464441 70661175897754846267135 := by
  unfold tailWord_464441
  simp only [CollatzResearch.WordTrace]
  refine ⟨16939554910417052052905177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11293036606944701368603451 16939554910417052052905177)
  ·
    refine ⟨12704666182812789039678883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16939554910417052052905177 12704666182812789039678883)
    ·
      refine ⟨19056999274219183559518325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12704666182812789039678883 19056999274219183559518325)
      ·
        refine ⟨1786593681958048458704843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19056999274219183559518325 1786593681958048458704843)
        ·
          refine ⟨2679890522937072688057265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786593681958048458704843 2679890522937072688057265)
          ·
            refine ⟨2009917892202804516042949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679890522937072688057265 2009917892202804516042949)
            ·
              refine ⟨376859604788025846758053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2009917892202804516042949 376859604788025846758053)
              ·
                refine ⟨70661175897754846267135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376859604788025846758053 70661175897754846267135)
                ·
                  rfl

theorem cell20_464441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 4].length) (baseStart_464441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464441 prefixEnd_464441 := by exact prefixLift 464441
  have htrace : WordTrace (prefixWord ++ tailWord_464441) baseStart_464441 baseEnd_464441 := by
    simpa [prefixWord, tailWord_464441, baseEnd_464441] using wordTrace_append hprefix tailTrace_464441
  have hstable : (prefixWord ++ tailWord_464441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464441).length < 2 ^ (prefixWord ++ tailWord_464441).sum := by decide
  have hdescent : baseEnd_464441 < baseStart_464441 := by decide
  rcases family_descends (prefixWord ++ tailWord_464441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464520 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 3]
def baseStart_464520 : Nat := 118140960795 + 464520 * 2 ^ 59
def prefixEnd_464520 : Nat := 4983230072969 + 3 ^ 40 * 464520 * 2
def baseEnd_464520 : Nat := 212019585445891375167749

theorem tailTrace_464520 : CollatzResearch.WordTrace tailWord_464520 prefixEnd_464520 212019585445891375167749 := by
  unfold tailWord_464520
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471218138565424272515507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11294957518087232363354009 8471218138565424272515507)
  ·
    refine ⟨12706827207848136408773261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8471218138565424272515507 12706827207848136408773261)
    ·
      refine ⟨4765060202943051153289973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12706827207848136408773261 4765060202943051153289973)
      ·
        refine ⟨446724394025911045620935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4765060202943051153289973 446724394025911045620935)
        ·
          refine ⟨670086591038866568431403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446724394025911045620935 670086591038866568431403)
          ·
            refine ⟨1005129886558299852647105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670086591038866568431403 1005129886558299852647105)
            ·
              refine ⟨753847414918724889485329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005129886558299852647105 753847414918724889485329)
              ·
                refine ⟨565385561189043667113997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753847414918724889485329 565385561189043667113997)
                ·
                  refine ⟨212019585445891375167749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565385561189043667113997 212019585445891375167749)
                  ·
                    rfl

theorem cell20_464520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_464520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464520 prefixEnd_464520 := by exact prefixLift 464520
  have htrace : WordTrace (prefixWord ++ tailWord_464520) baseStart_464520 baseEnd_464520 := by
    simpa [prefixWord, tailWord_464520, baseEnd_464520] using wordTrace_append hprefix tailTrace_464520
  have hstable : (prefixWord ++ tailWord_464520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464520).length < 2 ^ (prefixWord ++ tailWord_464520).sum := by decide
  have hdescent : baseEnd_464520 < baseStart_464520 := by decide
  rcases family_descends (prefixWord ++ tailWord_464520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464524 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 3]
def baseStart_464524 : Nat := 118140960795 + 464524 * 2 ^ 59
def prefixEnd_464524 : Nat := 4983230072969 + 3 ^ 40 * 464524 * 2
def baseEnd_464524 : Nat := 212021411154885139034399

theorem tailTrace_464524 : CollatzResearch.WordTrace tailWord_464524 prefixEnd_464524 212021411154885139034399 := by
  unfold tailWord_464524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8471291084558178614088313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11295054779410904818784417 8471291084558178614088313)
  ·
    refine ⟨6353468313418633960566235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8471291084558178614088313 6353468313418633960566235)
    ·
      refine ⟨9530202470127950940849353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6353468313418633960566235 9530202470127950940849353)
      ·
        refine ⟨7147651852595963205637015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9530202470127950940849353 7147651852595963205637015)
        ·
          refine ⟨10721477778893944808455523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7147651852595963205637015 10721477778893944808455523)
          ·
            refine ⟨16082216668340917212683285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721477778893944808455523 16082216668340917212683285)
            ·
              refine ⟨753853906328480494344529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16082216668340917212683285 753853906328480494344529)
              ·
                refine ⟨565390429746360370758397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753853906328480494344529 565390429746360370758397)
                ·
                  refine ⟨212021411154885139034399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565390429746360370758397 212021411154885139034399)
                  ·
                    rfl

theorem cell20_464524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_464524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464524 prefixEnd_464524 := by exact prefixLift 464524
  have htrace : WordTrace (prefixWord ++ tailWord_464524) baseStart_464524 baseEnd_464524 := by
    simpa [prefixWord, tailWord_464524, baseEnd_464524] using wordTrace_append hprefix tailTrace_464524
  have hstable : (prefixWord ++ tailWord_464524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464524).length < 2 ^ (prefixWord ++ tailWord_464524).sum := by decide
  have hdescent : baseEnd_464524 < baseStart_464524 := by decide
  rcases family_descends (prefixWord ++ tailWord_464524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464582 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_464582 : Nat := 118140960795 + 464582 * 2 ^ 59
def prefixEnd_464582 : Nat := 4983230072969 + 3 ^ 40 * 464582 * 2
def baseEnd_464582 : Nat := 212047883935294715100829

theorem tailTrace_464582 : CollatzResearch.WordTrace tailWord_464582 prefixEnd_464582 212047883935294715100829 := by
  unfold tailWord_464582
  simp only [CollatzResearch.WordTrace]
  refine ⟨529521800090819785430875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11296465068604155422525333 529521800090819785430875)
  ·
    refine ⟨794282700136229678146313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 529521800090819785430875 794282700136229678146313)
    ·
      refine ⟨595712025102172258609735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 794282700136229678146313 595712025102172258609735)
      ·
        refine ⟨893568037653258387914603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595712025102172258609735 893568037653258387914603)
        ·
          refine ⟨1340352056479887581871905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893568037653258387914603 1340352056479887581871905)
          ·
            refine ⟨1005264042359915686403929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340352056479887581871905 1005264042359915686403929)
            ·
              refine ⟨753948031769936764802947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005264042359915686403929 753948031769936764802947)
              ·
                refine ⟨1130922047654905147204421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753948031769936764802947 1130922047654905147204421)
                ·
                  refine ⟨212047883935294715100829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1130922047654905147204421 212047883935294715100829)
                  ·
                    rfl

theorem cell20_464582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_464582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464582 prefixEnd_464582 := by exact prefixLift 464582
  have htrace : WordTrace (prefixWord ++ tailWord_464582) baseStart_464582 baseEnd_464582 := by
    simpa [prefixWord, tailWord_464582, baseEnd_464582] using wordTrace_append hprefix tailTrace_464582
  have hstable : (prefixWord ++ tailWord_464582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464582).length < 2 ^ (prefixWord ++ tailWord_464582).sum := by decide
  have hdescent : baseEnd_464582 < baseStart_464582 := by decide
  rcases family_descends (prefixWord ++ tailWord_464582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464583 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 5]
def baseStart_464583 : Nat := 118140960795 + 464583 * 2 ^ 59
def prefixEnd_464583 : Nat := 4983230072969 + 3 ^ 40 * 464583 * 2
def baseEnd_464583 : Nat := 212048340362543156067491

theorem tailTrace_464583 : CollatzResearch.WordTrace tailWord_464583 prefixEnd_464583 212048340362543156067491 := by
  unfold tailWord_464583
  simp only [CollatzResearch.WordTrace]
  refine ⟨16944734075902610304574403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11296489383935073536382935 16944734075902610304574403)
  ·
    refine ⟨25417101113853915456861605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16944734075902610304574403 25417101113853915456861605)
    ·
      refine ⟨4765706458847609148161551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25417101113853915456861605 4765706458847609148161551)
      ·
        refine ⟨7148559688271413722242327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4765706458847609148161551 7148559688271413722242327)
        ·
          refine ⟨10722839532407120583363491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7148559688271413722242327 10722839532407120583363491)
          ·
            refine ⟨16084259298610680875045237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10722839532407120583363491 16084259298610680875045237)
            ·
              refine ⟨1507899309244751332035491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16084259298610680875045237 1507899309244751332035491)
              ·
                refine ⟨2261848963867126998053237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507899309244751332035491 2261848963867126998053237)
                ·
                  refine ⟨212048340362543156067491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2261848963867126998053237 212048340362543156067491)
                  ·
                    rfl

theorem cell20_464583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_464583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464583 prefixEnd_464583 := by exact prefixLift 464583
  have htrace : WordTrace (prefixWord ++ tailWord_464583) baseStart_464583 baseEnd_464583 := by
    simpa [prefixWord, tailWord_464583, baseEnd_464583] using wordTrace_append hprefix tailTrace_464583
  have hstable : (prefixWord ++ tailWord_464583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464583).length < 2 ^ (prefixWord ++ tailWord_464583).sum := by decide
  have hdescent : baseEnd_464583 < baseStart_464583 := by decide
  rcases family_descends (prefixWord ++ tailWord_464583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464586 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_464586 : Nat := 118140960795 + 464586 * 2 ^ 59
def prefixEnd_464586 : Nat := 4983230072969 + 3 ^ 40 * 464586 * 2
def baseEnd_464586 : Nat := 212049709644288478967479

theorem tailTrace_464586 : CollatzResearch.WordTrace tailWord_464586 prefixEnd_464586 212049709644288478967479 := by
  unfold tailWord_464586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236210873722935454233403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11296562329927827877955741 4236210873722935454233403)
  ·
    refine ⟨6354316310584403181350105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4236210873722935454233403 6354316310584403181350105)
    ·
      refine ⟨4765737232938302386012579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6354316310584403181350105 4765737232938302386012579)
      ·
        refine ⟨7148605849407453579018869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4765737232938302386012579 7148605849407453579018869)
        ·
          refine ⟨670181798381948773033019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7148605849407453579018869 670181798381948773033019)
          ·
            refine ⟨1005272697572923159549529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670181798381948773033019 1005272697572923159549529)
            ·
              refine ⟨753954523179692369662147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005272697572923159549529 753954523179692369662147)
              ·
                refine ⟨1130931784769538554493221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753954523179692369662147 1130931784769538554493221)
                ·
                  refine ⟨212049709644288478967479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1130931784769538554493221 212049709644288478967479)
                  ·
                    rfl

theorem cell20_464586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_464586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464586 prefixEnd_464586 := by exact prefixLift 464586
  have htrace : WordTrace (prefixWord ++ tailWord_464586) baseStart_464586 baseEnd_464586 := by
    simpa [prefixWord, tailWord_464586, baseEnd_464586] using wordTrace_append hprefix tailTrace_464586
  have hstable : (prefixWord ++ tailWord_464586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464586).length < 2 ^ (prefixWord ++ tailWord_464586).sum := by decide
  have hdescent : baseEnd_464586 < baseStart_464586 := by decide
  rcases family_descends (prefixWord ++ tailWord_464586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464596 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 3]
def baseStart_464596 : Nat := 118140960795 + 464596 * 2 ^ 59
def prefixEnd_464596 : Nat := 4983230072969 + 3 ^ 40 * 464596 * 2
def baseEnd_464596 : Nat := 212054273916772888634105

theorem tailTrace_464596 : CollatzResearch.WordTrace tailWord_464596 prefixEnd_464596 212054273916772888634105 := by
  unfold tailWord_464596
  simp only [CollatzResearch.WordTrace]
  refine ⟨8472604112427756762398821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11296805483237009016531761 8472604112427756762398821)
  ·
    refine ⟨1588613271080204392949779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8472604112427756762398821 1588613271080204392949779)
    ·
      refine ⟨2382919906620306589424669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1588613271080204392949779 2382919906620306589424669)
      ·
        refine ⟨893594964982614971034251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2382919906620306589424669 893594964982614971034251)
        ·
          refine ⟨1340392447473922456551377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893594964982614971034251 1340392447473922456551377)
          ·
            refine ⟨1005294335605441842413533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340392447473922456551377 1005294335605441842413533)
            ·
              refine ⟨376985375852040690905075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1005294335605441842413533 376985375852040690905075)
              ·
                refine ⟨565478063778061036357613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376985375852040690905075 565478063778061036357613)
                ·
                  refine ⟨212054273916772888634105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565478063778061036357613 212054273916772888634105)
                  ·
                    rfl

theorem cell20_464596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_464596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464596 prefixEnd_464596 := by exact prefixLift 464596
  have htrace : WordTrace (prefixWord ++ tailWord_464596) baseStart_464596 baseEnd_464596 := by
    simpa [prefixWord, tailWord_464596, baseEnd_464596] using wordTrace_append hprefix tailTrace_464596
  have hstable : (prefixWord ++ tailWord_464596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464596).length < 2 ^ (prefixWord ++ tailWord_464596).sum := by decide
  have hdescent : baseEnd_464596 < baseStart_464596 := by decide
  rcases family_descends (prefixWord ++ tailWord_464596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464693 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 3]
def baseStart_464693 : Nat := 118140960795 + 464693 * 2 ^ 59
def prefixEnd_464693 : Nat := 4983230072969 + 3 ^ 40 * 464693 * 2
def baseEnd_464693 : Nat := 212098547359871662400375

theorem tailTrace_464693 : CollatzResearch.WordTrace tailWord_464693 prefixEnd_464693 212098547359871662400375 := by
  unfold tailWord_464693
  simp only [CollatzResearch.WordTrace]
  refine ⟨16948746105504099091078733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11299164070336066060719155 16948746105504099091078733)
  ·
    refine ⟨6355779789564037159154525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16948746105504099091078733 6355779789564037159154525)
    ·
      refine ⟨2383417421086513934682947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6355779789564037159154525 2383417421086513934682947)
      ·
        refine ⟨3575126131629770902024421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383417421086513934682947 3575126131629770902024421)
        ·
          refine ⟨670336149680582044129579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3575126131629770902024421 670336149680582044129579)
          ·
            refine ⟨1005504224520873066194369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670336149680582044129579 1005504224520873066194369)
            ·
              refine ⟨754128168390654799645777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005504224520873066194369 754128168390654799645777)
              ·
                refine ⟨565596126292991099734333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754128168390654799645777 565596126292991099734333)
                ·
                  refine ⟨212098547359871662400375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565596126292991099734333 212098547359871662400375)
                  ·
                    rfl

theorem cell20_464693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_464693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464693 prefixEnd_464693 := by exact prefixLift 464693
  have htrace : WordTrace (prefixWord ++ tailWord_464693) baseStart_464693 baseEnd_464693 := by
    simpa [prefixWord, tailWord_464693, baseEnd_464693] using wordTrace_append hprefix tailTrace_464693
  have hstable : (prefixWord ++ tailWord_464693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464693).length < 2 ^ (prefixWord ++ tailWord_464693).sum := by decide
  have hdescent : baseEnd_464693 < baseStart_464693 := by decide
  rcases family_descends (prefixWord ++ tailWord_464693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464710 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_464710 : Nat := 118140960795 + 464710 * 2 ^ 59
def prefixEnd_464710 : Nat := 4983230072969 + 3 ^ 40 * 464710 * 2
def baseEnd_464710 : Nat := 212106306623095158833639

theorem tailTrace_464710 : CollatzResearch.WordTrace tailWord_464710 prefixEnd_464710 212106306623095158833639 := by
  unfold tailWord_464710
  simp only [CollatzResearch.WordTrace]
  refine ⟨529667692076328468576487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11299577430961673996298389 529667692076328468576487)
  ·
    refine ⟨794501538114492702864731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 529667692076328468576487 794501538114492702864731)
    ·
      refine ⟨1191752307171739054297097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794501538114492702864731 1191752307171739054297097)
      ·
        refine ⟨893814230378804290722823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1191752307171739054297097 893814230378804290722823)
        ·
          refine ⟨1340721345568206436084235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893814230378804290722823 1340721345568206436084235)
          ·
            refine ⟨2011082018352309654126353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340721345568206436084235 2011082018352309654126353)
            ·
              refine ⟨1508311513764232240594765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011082018352309654126353 1508311513764232240594765)
              ·
                refine ⟨565616817661587090223037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1508311513764232240594765 565616817661587090223037)
                ·
                  refine ⟨212106306623095158833639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565616817661587090223037 212106306623095158833639)
                  ·
                    rfl

theorem cell20_464710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_464710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464710 prefixEnd_464710 := by exact prefixLift 464710
  have htrace : WordTrace (prefixWord ++ tailWord_464710) baseStart_464710 baseEnd_464710 := by
    simpa [prefixWord, tailWord_464710, baseEnd_464710] using wordTrace_append hprefix tailTrace_464710
  have hstable : (prefixWord ++ tailWord_464710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464710).length < 2 ^ (prefixWord ++ tailWord_464710).sum := by decide
  have hdescent : baseEnd_464710 < baseStart_464710 := by decide
  rcases family_descends (prefixWord ++ tailWord_464710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464721 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 4]
def baseStart_464721 : Nat := 118140960795 + 464721 * 2 ^ 59
def prefixEnd_464721 : Nat := 4983230072969 + 3 ^ 40 * 464721 * 2
def baseEnd_464721 : Nat := 212111327322828009466927

theorem tailTrace_464721 : CollatzResearch.WordTrace tailWord_464721 prefixEnd_464721 212111327322828009466927 := by
  unfold tailWord_464721
  simp only [CollatzResearch.WordTrace]
  refine ⟨16949767349402659873098017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11299844899601773248732011 16949767349402659873098017)
  ·
    refine ⟨12712325512051994904823513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16949767349402659873098017 12712325512051994904823513)
    ·
      refine ⟨9534244134038996178617635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12712325512051994904823513 9534244134038996178617635)
      ·
        refine ⟨14301366201058494267926453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9534244134038996178617635 14301366201058494267926453)
        ·
          refine ⟨1340753081349233837618105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14301366201058494267926453 1340753081349233837618105)
          ·
            refine ⟨1005564811011925378213579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340753081349233837618105 1005564811011925378213579)
            ·
              refine ⟨1508347216517888067320369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005564811011925378213579 1508347216517888067320369)
              ·
                refine ⟨1131260412388416050490277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1508347216517888067320369 1131260412388416050490277)
                ·
                  refine ⟨212111327322828009466927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131260412388416050490277 212111327322828009466927)
                  ·
                    rfl

theorem cell20_464721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_464721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464721 prefixEnd_464721 := by exact prefixLift 464721
  have htrace : WordTrace (prefixWord ++ tailWord_464721) baseStart_464721 baseEnd_464721 := by
    simpa [prefixWord, tailWord_464721, baseEnd_464721] using wordTrace_append hprefix tailTrace_464721
  have hstable : (prefixWord ++ tailWord_464721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464721).length < 2 ^ (prefixWord ++ tailWord_464721).sum := by decide
  have hdescent : baseEnd_464721 < baseStart_464721 := by decide
  rcases family_descends (prefixWord ++ tailWord_464721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464804 : List Nat := [2, 3, 1, 2, 1, 5, 6]
def baseStart_464804 : Nat := 118140960795 + 464804 * 2 ^ 59
def prefixEnd_464804 : Nat := 4983230072969 + 3 ^ 40 * 464804 * 2
def baseEnd_464804 : Nat := 23572134531605401077769

theorem tailTrace_464804 : CollatzResearch.WordTrace tailWord_464804 prefixEnd_464804 23572134531605401077769 := by
  unfold tailWord_464804
  simp only [CollatzResearch.WordTrace]
  refine ⟨8476397304050982524184733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11301863072067976698912977 8476397304050982524184733)
  ·
    refine ⟨3178648989019118446569275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8476397304050982524184733 3178648989019118446569275)
    ·
      refine ⟨4767973483528677669853913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3178648989019118446569275 4767973483528677669853913)
      ·
        refine ⟨3575980112646508252390435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4767973483528677669853913 3575980112646508252390435)
        ·
          refine ⟨5363970168969762378585653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575980112646508252390435 5363970168969762378585653)
          ·
            refine ⟨502872203340915222992405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5363970168969762378585653 502872203340915222992405)
            ·
              refine ⟨23572134531605401077769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 502872203340915222992405 23572134531605401077769)
              ·
                rfl

theorem cell20_464804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 6].length) (baseStart_464804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464804 prefixEnd_464804 := by exact prefixLift 464804
  have htrace : WordTrace (prefixWord ++ tailWord_464804) baseStart_464804 baseEnd_464804 := by
    simpa [prefixWord, tailWord_464804, baseEnd_464804] using wordTrace_append hprefix tailTrace_464804
  have hstable : (prefixWord ++ tailWord_464804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464804).length < 2 ^ (prefixWord ++ tailWord_464804).sum := by decide
  have hdescent : baseEnd_464804 < baseStart_464804 := by decide
  rcases family_descends (prefixWord ++ tailWord_464804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464820 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 3]
def baseStart_464820 : Nat := 118140960795 + 464820 * 2 ^ 59
def prefixEnd_464820 : Nat := 4983230072969 + 3 ^ 40 * 464820 * 2
def baseEnd_464820 : Nat := 212156513620423665166523

theorem tailTrace_464820 : CollatzResearch.WordTrace tailWord_464820 prefixEnd_464820 212156513620423665166523 := by
  unfold tailWord_464820
  simp only [CollatzResearch.WordTrace]
  refine ⟨8476689088021999890475957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11302252117362666520634609 8476689088021999890475957)
  ·
    refine ⟨794689602002062489732121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8476689088021999890475957 794689602002062489732121)
    ·
      refine ⟨596017201501546867299091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 794689602002062489732121 596017201501546867299091)
      ·
        refine ⟨894025802252320300948637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596017201501546867299091 894025802252320300948637)
        ·
          refine ⟨335259675844620112855739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 894025802252320300948637 335259675844620112855739)
          ·
            refine ⟨502889513766930169283609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335259675844620112855739 502889513766930169283609)
            ·
              refine ⟨377167135325197626962707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502889513766930169283609 377167135325197626962707)
              ·
                refine ⟨565750702987796440444061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377167135325197626962707 565750702987796440444061)
                ·
                  refine ⟨212156513620423665166523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565750702987796440444061 212156513620423665166523)
                  ·
                    rfl

theorem cell20_464820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_464820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464820 prefixEnd_464820 := by exact prefixLift 464820
  have htrace : WordTrace (prefixWord ++ tailWord_464820) baseStart_464820 baseEnd_464820 := by
    simpa [prefixWord, tailWord_464820, baseEnd_464820] using wordTrace_append hprefix tailTrace_464820
  have hstable : (prefixWord ++ tailWord_464820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464820).length < 2 ^ (prefixWord ++ tailWord_464820).sum := by decide
  have hdescent : baseEnd_464820 < baseStart_464820 := by decide
  rcases family_descends (prefixWord ++ tailWord_464820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464852 : List Nat := [2, 4, 1, 2, 1, 1, 2, 5, 2]
def baseStart_464852 : Nat := 118140960795 + 464852 * 2 ^ 59
def prefixEnd_464852 : Nat := 4983230072969 + 3 ^ 40 * 464852 * 2
def baseEnd_464852 : Nat := 212171119292373776099725

theorem tailTrace_464852 : CollatzResearch.WordTrace tailWord_464852 prefixEnd_464852 212171119292373776099725 := by
  unfold tailWord_464852
  simp only [CollatzResearch.WordTrace]
  refine ⟨8477272655964034623058405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11303030207952046164077873 8477272655964034623058405)
  ·
    refine ⟨1589488622993256491823451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8477272655964034623058405 1589488622993256491823451)
    ·
      refine ⟨2384232934489884737735177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589488622993256491823451 2384232934489884737735177)
      ·
        refine ⟨1788174700867413553301383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2384232934489884737735177 1788174700867413553301383)
        ·
          refine ⟨2682262051301120329952075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788174700867413553301383 2682262051301120329952075)
          ·
            refine ⟨4023393076951680494928113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682262051301120329952075 4023393076951680494928113)
            ·
              refine ⟨3017544807713760371196085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4023393076951680494928113 3017544807713760371196085)
              ·
                refine ⟨282894825723165034799633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3017544807713760371196085 282894825723165034799633)
                ·
                  refine ⟨212171119292373776099725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282894825723165034799633 212171119292373776099725)
                  ·
                    rfl

theorem cell20_464852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_464852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464852 prefixEnd_464852 := by exact prefixLift 464852
  have htrace : WordTrace (prefixWord ++ tailWord_464852) baseStart_464852 baseEnd_464852 := by
    simpa [prefixWord, tailWord_464852, baseEnd_464852] using wordTrace_append hprefix tailTrace_464852
  have hstable : (prefixWord ++ tailWord_464852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464852).length < 2 ^ (prefixWord ++ tailWord_464852).sum := by decide
  have hdescent : baseEnd_464852 < baseStart_464852 := by decide
  rcases family_descends (prefixWord ++ tailWord_464852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464863 : List Nat := [1, 1, 2, 3, 4, 9]
def baseStart_464863 : Nat := 118140960795 + 464863 * 2 ^ 59
def prefixEnd_464863 : Nat := 4983230072969 + 3 ^ 40 * 464863 * 2
def baseEnd_464863 : Nat := 7858375555263208397519

theorem tailTrace_464863 : CollatzResearch.WordTrace tailWord_464863 prefixEnd_464863 7858375555263208397519 := by
  unfold tailWord_464863
  simp only [CollatzResearch.WordTrace]
  refine ⟨16954946514888218124767243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11303297676592145416511495 16954946514888218124767243)
  ·
    refine ⟨25432419772332327187150865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16954946514888218124767243 25432419772332327187150865)
    ·
      refine ⟨19074314829249245390363149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25432419772332327187150865 19074314829249245390363149)
      ·
        refine ⟨7152868060968467021386181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19074314829249245390363149 7152868060968467021386181)
        ·
          refine ⟨1341162761431587566509909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7152868060968467021386181 1341162761431587566509909)
          ·
            refine ⟨7858375555263208397519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1341162761431587566509909 7858375555263208397519)
            ·
              rfl

theorem cell20_464863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 9].length) (baseStart_464863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464863 prefixEnd_464863 := by exact prefixLift 464863
  have htrace : WordTrace (prefixWord ++ tailWord_464863) baseStart_464863 baseEnd_464863 := by
    simpa [prefixWord, tailWord_464863, baseEnd_464863] using wordTrace_append hprefix tailTrace_464863
  have hstable : (prefixWord ++ tailWord_464863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464863).length < 2 ^ (prefixWord ++ tailWord_464863).sum := by decide
  have hdescent : baseEnd_464863 < baseStart_464863 := by decide
  rcases family_descends (prefixWord ++ tailWord_464863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464952 : List Nat := [2, 1, 2, 1, 7, 1, 2, 4]
def baseStart_464952 : Nat := 118140960795 + 464952 * 2 ^ 59
def prefixEnd_464952 : Nat := 4983230072969 + 3 ^ 40 * 464952 * 2
def baseEnd_464952 : Nat := 70738920672405957588661

theorem tailTrace_464952 : CollatzResearch.WordTrace tailWord_464952 prefixEnd_464952 70738920672405957588661 := by
  unfold tailWord_464952
  simp only [CollatzResearch.WordTrace]
  refine ⟨8479096305782893162378555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11305461741043857549838073 8479096305782893162378555)
  ·
    refine ⟨12718644458674339743567833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8479096305782893162378555 12718644458674339743567833)
    ·
      refine ⟨9538983344005754807675875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12718644458674339743567833 9538983344005754807675875)
      ·
        refine ⟨14308475016008632211513813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9538983344005754807675875 14308475016008632211513813)
        ·
          refine ⟨335354883187702317457355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14308475016008632211513813 335354883187702317457355)
          ·
            refine ⟨503032324781553476186033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335354883187702317457355 503032324781553476186033)
            ·
              refine ⟨377274243586165107139525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503032324781553476186033 377274243586165107139525)
              ·
                refine ⟨70738920672405957588661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377274243586165107139525 70738920672405957588661)
                ·
                  rfl

theorem cell20_464952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_464952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464952 prefixEnd_464952 := by exact prefixLift 464952
  have htrace : WordTrace (prefixWord ++ tailWord_464952) baseStart_464952 baseEnd_464952 := by
    simpa [prefixWord, tailWord_464952, baseEnd_464952] using wordTrace_append hprefix tailTrace_464952
  have hstable : (prefixWord ++ tailWord_464952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464952).length < 2 ^ (prefixWord ++ tailWord_464952).sum := by decide
  have hdescent : baseEnd_464952 < baseStart_464952 := by decide
  rcases family_descends (prefixWord ++ tailWord_464952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464997 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 3]
def baseStart_464997 : Nat := 118140960795 + 464997 * 2 ^ 59
def prefixEnd_464997 : Nat := 4983230072969 + 3 ^ 40 * 464997 * 2
def baseEnd_464997 : Nat := 212237301243397716265799

theorem tailTrace_464997 : CollatzResearch.WordTrace tailWord_464997 prefixEnd_464997 212237301243397716265799 := by
  unfold tailWord_464997
  simp only [CollatzResearch.WordTrace]
  refine ⟨16959833896402759010145245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11306555930935172673430163 16959833896402759010145245)
  ·
    refine ⟨6359937711151034628804467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16959833896402759010145245 6359937711151034628804467)
    ·
      refine ⟨9539906566726551943206701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6359937711151034628804467 9539906566726551943206701)
      ·
        refine ⟨3577464962522456978702513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9539906566726551943206701 3577464962522456978702513)
        ·
          refine ⟨2683098721891842734026885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3577464962522456978702513 2683098721891842734026885)
          ·
            refine ⟨503081010354720512630041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2683098721891842734026885 503081010354720512630041)
            ·
              refine ⟨377310757766040384472531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503081010354720512630041 377310757766040384472531)
              ·
                refine ⟨565966136649060576708797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377310757766040384472531 565966136649060576708797)
                ·
                  refine ⟨212237301243397716265799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565966136649060576708797 212237301243397716265799)
                  ·
                    rfl

theorem cell20_464997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_464997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_464997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_464997 prefixEnd_464997 := by exact prefixLift 464997
  have htrace : WordTrace (prefixWord ++ tailWord_464997) baseStart_464997 baseEnd_464997 := by
    simpa [prefixWord, tailWord_464997, baseEnd_464997] using wordTrace_append hprefix tailTrace_464997
  have hstable : (prefixWord ++ tailWord_464997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464997).length < 2 ^ (prefixWord ++ tailWord_464997).sum := by decide
  have hdescent : baseEnd_464997 < baseStart_464997 := by decide
  rcases family_descends (prefixWord ++ tailWord_464997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465001 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 3]
def baseStart_465001 : Nat := 118140960795 + 465001 * 2 ^ 59
def prefixEnd_465001 : Nat := 4983230072969 + 3 ^ 40 * 465001 * 2
def baseEnd_465001 : Nat := 212239126952391480132449

theorem tailTrace_465001 : CollatzResearch.WordTrace tailWord_465001 prefixEnd_465001 212239126952391480132449 := by
  unfold tailWord_465001
  simp only [CollatzResearch.WordTrace]
  refine ⟨16959979788388267693290857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11306653192258845128860571 16959979788388267693290857)
  ·
    refine ⟨12719984841291200769968143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16959979788388267693290857 12719984841291200769968143)
    ·
      refine ⟨19079977261936801154952215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12719984841291200769968143 19079977261936801154952215)
      ·
        refine ⟨28619965892905201732428323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19079977261936801154952215 28619965892905201732428323)
        ·
          refine ⟨42929948839357802598642485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28619965892905201732428323 42929948839357802598642485)
          ·
            refine ⟨4024682703689793993622733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42929948839357802598642485 4024682703689793993622733)
            ·
              refine ⟨1509256013883672747608525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4024682703689793993622733 1509256013883672747608525)
              ·
                refine ⟨565971005206377280353197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1509256013883672747608525 565971005206377280353197)
                ·
                  refine ⟨212239126952391480132449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565971005206377280353197 212239126952391480132449)
                  ·
                    rfl

theorem cell20_465001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_465001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465001 prefixEnd_465001 := by exact prefixLift 465001
  have htrace : WordTrace (prefixWord ++ tailWord_465001) baseStart_465001 baseEnd_465001 := by
    simpa [prefixWord, tailWord_465001, baseEnd_465001] using wordTrace_append hprefix tailTrace_465001
  have hstable : (prefixWord ++ tailWord_465001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465001).length < 2 ^ (prefixWord ++ tailWord_465001).sum := by decide
  have hdescent : baseEnd_465001 < baseStart_465001 := by decide
  rcases family_descends (prefixWord ++ tailWord_465001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465015 : List Nat := [1, 1, 3, 1, 1, 5, 2, 6]
def baseStart_465015 : Nat := 118140960795 + 465015 * 2 ^ 59
def prefixEnd_465015 : Nat := 4983230072969 + 3 ^ 40 * 465015 * 2
def baseEnd_465015 : Nat := 70748505644623217888575

theorem tailTrace_465015 : CollatzResearch.WordTrace tailWord_465015 prefixEnd_465015 70748505644623217888575 := by
  unfold tailWord_465015
  simp only [CollatzResearch.WordTrace]
  refine ⟨16960490410337548084300499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11306993606891698722866999 16960490410337548084300499)
  ·
    refine ⟨25440735615506322126450749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16960490410337548084300499 25440735615506322126450749)
    ·
      refine ⟨9540275855814870797419031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25440735615506322126450749 9540275855814870797419031)
      ·
        refine ⟨14310413783722306196128547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9540275855814870797419031 14310413783722306196128547)
        ·
          refine ⟨21465620675583459294192821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14310413783722306196128547 21465620675583459294192821)
          ·
            refine ⟨2012401938335949308830577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21465620675583459294192821 2012401938335949308830577)
            ·
              refine ⟨1509301453751961981622933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2012401938335949308830577 1509301453751961981622933)
              ·
                refine ⟨70748505644623217888575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1509301453751961981622933 70748505644623217888575)
                ·
                  rfl

theorem cell20_465015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_465015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465015 prefixEnd_465015 := by exact prefixLift 465015
  have htrace : WordTrace (prefixWord ++ tailWord_465015) baseStart_465015 baseEnd_465015 := by
    simpa [prefixWord, tailWord_465015, baseEnd_465015] using wordTrace_append hprefix tailTrace_465015
  have hstable : (prefixWord ++ tailWord_465015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465015).length < 2 ^ (prefixWord ++ tailWord_465015).sum := by decide
  have hdescent : baseEnd_465015 < baseStart_465015 := by decide
  rcases family_descends (prefixWord ++ tailWord_465015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465038 : List Nat := [4, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_465038 : Nat := 118140960795 + 465038 * 2 ^ 59
def prefixEnd_465038 : Nat := 4983230072969 + 3 ^ 40 * 465038 * 2
def baseEnd_465038 : Nat := 212256014760583795898965

theorem tailTrace_465038 : CollatzResearch.WordTrace tailWord_465038 prefixEnd_465038 212256014760583795898965 := by
  unfold tailWord_465038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120166161156777876548471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11307552859502815341591845 2120166161156777876548471)
  ·
    refine ⟨3180249241735166814822707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2120166161156777876548471 3180249241735166814822707)
    ·
      refine ⟨4770373862602750222234061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180249241735166814822707 4770373862602750222234061)
      ·
        refine ⟨1788890198476031333337773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4770373862602750222234061 1788890198476031333337773)
        ·
          refine ⟨670833824428511750001665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1788890198476031333337773 670833824428511750001665)
          ·
            refine ⟨503125368321383812501249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670833824428511750001665 503125368321383812501249)
            ·
              refine ⟨377344026241037859375937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503125368321383812501249 377344026241037859375937)
              ·
                refine ⟨283008019680778394531953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377344026241037859375937 283008019680778394531953)
                ·
                  refine ⟨212256014760583795898965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283008019680778394531953 212256014760583795898965)
                  ·
                    rfl

theorem cell20_465038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_465038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465038 prefixEnd_465038 := by exact prefixLift 465038
  have htrace : WordTrace (prefixWord ++ tailWord_465038) baseStart_465038 baseEnd_465038 := by
    simpa [prefixWord, tailWord_465038, baseEnd_465038] using wordTrace_append hprefix tailTrace_465038
  have hstable : (prefixWord ++ tailWord_465038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465038).length < 2 ^ (prefixWord ++ tailWord_465038).sum := by decide
  have hdescent : baseEnd_465038 < baseStart_465038 := by decide
  rcases family_descends (prefixWord ++ tailWord_465038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465042 : List Nat := [3, 2, 3, 1, 1, 1, 3, 4, 2]
def baseStart_465042 : Nat := 118140960795 + 465042 * 2 ^ 59
def prefixEnd_465042 : Nat := 4983230072969 + 3 ^ 40 * 465042 * 2
def baseEnd_465042 : Nat := 212257840469577559765615

theorem tailTrace_465042 : CollatzResearch.WordTrace tailWord_465042 prefixEnd_465042 212257840469577559765615 := by
  unfold tailWord_465042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240368795309932923883345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11307650120826487797022253 4240368795309932923883345)
  ·
    refine ⟨3180276596482449692912509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4240368795309932923883345 3180276596482449692912509)
    ·
      refine ⟨1192603723680918634842191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3180276596482449692912509 1192603723680918634842191)
      ·
        refine ⟨1788905585521377952263287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192603723680918634842191 1788905585521377952263287)
        ·
          refine ⟨2683358378282066928394931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788905585521377952263287 2683358378282066928394931)
          ·
            refine ⟨4025037567423100392592397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683358378282066928394931 4025037567423100392592397)
            ·
              refine ⟨1509389087783662647222149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4025037567423100392592397 1509389087783662647222149)
              ·
                refine ⟨283010453959436746354153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1509389087783662647222149 283010453959436746354153)
                ·
                  refine ⟨212257840469577559765615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283010453959436746354153 212257840469577559765615)
                  ·
                    rfl

theorem cell20_465042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_465042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465042 prefixEnd_465042 := by exact prefixLift 465042
  have htrace : WordTrace (prefixWord ++ tailWord_465042) baseStart_465042 baseEnd_465042 := by
    simpa [prefixWord, tailWord_465042, baseEnd_465042] using wordTrace_append hprefix tailTrace_465042
  have hstable : (prefixWord ++ tailWord_465042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465042).length < 2 ^ (prefixWord ++ tailWord_465042).sum := by decide
  have hdescent : baseEnd_465042 < baseStart_465042 := by decide
  rcases family_descends (prefixWord ++ tailWord_465042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465066 : List Nat := [3, 1, 5, 1, 2, 1, 3, 4]
def baseStart_465066 : Nat := 118140960795 + 465066 * 2 ^ 59
def prefixEnd_465066 : Nat := 4983230072969 + 3 ^ 40 * 465066 * 2
def baseEnd_465066 : Nat := 70756264907846714321839

theorem tailTrace_465066 : CollatzResearch.WordTrace tailWord_465066 prefixEnd_465066 70756264907846714321839 := by
  unfold tailWord_465066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240587633288195948601763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11308233688768522529604701 4240587633288195948601763)
  ·
    refine ⟨6360881449932293922902645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4240587633288195948601763 6360881449932293922902645)
    ·
      refine ⟨596332635931152555272123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6360881449932293922902645 596332635931152555272123)
      ·
        refine ⟨894498953896728832908185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596332635931152555272123 894498953896728832908185)
        ·
          refine ⟨670874215422546624681139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894498953896728832908185 670874215422546624681139)
          ·
            refine ⟨1006311323133819937021709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670874215422546624681139 1006311323133819937021709)
            ·
              refine ⟨377366746175182476383141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1006311323133819937021709 377366746175182476383141)
              ·
                refine ⟨70756264907846714321839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377366746175182476383141 70756264907846714321839)
                ·
                  rfl

theorem cell20_465066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_465066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465066 prefixEnd_465066 := by exact prefixLift 465066
  have htrace : WordTrace (prefixWord ++ tailWord_465066) baseStart_465066 baseEnd_465066 := by
    simpa [prefixWord, tailWord_465066, baseEnd_465066] using wordTrace_append hprefix tailTrace_465066
  have hstable : (prefixWord ++ tailWord_465066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465066).length < 2 ^ (prefixWord ++ tailWord_465066).sum := by decide
  have hdescent : baseEnd_465066 < baseStart_465066 := by decide
  rcases family_descends (prefixWord ++ tailWord_465066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465090 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_465090 : Nat := 118140960795 + 465090 * 2 ^ 59
def prefixEnd_465090 : Nat := 4983230072969 + 3 ^ 40 * 465090 * 2
def baseEnd_465090 : Nat := 212279748977502726165419

theorem tailTrace_465090 : CollatzResearch.WordTrace tailWord_465090 prefixEnd_465090 212279748977502726165419 := by
  unfold tailWord_465090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240806471266458973320181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11308817256710557262187149 4240806471266458973320181)
  ·
    refine ⟨397575606681230528748767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4240806471266458973320181 397575606681230528748767)
    ·
      refine ⟨596363410021845793123151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397575606681230528748767 596363410021845793123151)
      ·
        refine ⟨894545115032768689684727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596363410021845793123151 894545115032768689684727)
        ·
          refine ⟨1341817672549153034527091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894545115032768689684727 1341817672549153034527091)
          ·
            refine ⟨2012726508823729551790637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341817672549153034527091 2012726508823729551790637)
            ·
              refine ⟨754772440808898581921489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2012726508823729551790637 754772440808898581921489)
              ·
                refine ⟨566079330606673936441117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754772440808898581921489 566079330606673936441117)
                ·
                  refine ⟨212279748977502726165419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566079330606673936441117 212279748977502726165419)
                  ·
                    rfl

theorem cell20_465090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_465090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465090 prefixEnd_465090 := by exact prefixLift 465090
  have htrace : WordTrace (prefixWord ++ tailWord_465090) baseStart_465090 baseEnd_465090 := by
    simpa [prefixWord, tailWord_465090, baseEnd_465090] using wordTrace_append hprefix tailTrace_465090
  have hstable : (prefixWord ++ tailWord_465090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465090).length < 2 ^ (prefixWord ++ tailWord_465090).sum := by decide
  have hdescent : baseEnd_465090 < baseStart_465090 := by decide
  rcases family_descends (prefixWord ++ tailWord_465090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465125 : List Nat := [1, 3, 1, 4, 2, 3, 2, 4]
def baseStart_465125 : Nat := 118140960795 + 465125 * 2 ^ 59
def prefixEnd_465125 : Nat := 4983230072969 + 3 ^ 40 * 465125 * 2
def baseEnd_465125 : Nat := 70765241310399386666203

theorem tailTrace_465125 : CollatzResearch.WordTrace tailWord_465125 prefixEnd_465125 70765241310399386666203 := by
  unfold tailWord_465125
  simp only [CollatzResearch.WordTrace]
  refine ⟨16964502439939036870804829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11309668293292691247203219 16964502439939036870804829)
  ·
    refine ⟨6361688414977138826551811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16964502439939036870804829 6361688414977138826551811)
    ·
      refine ⟨9542532622465708239827717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6361688414977138826551811 9542532622465708239827717)
      ·
        refine ⟨1789224866712320294967697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9542532622465708239827717 1789224866712320294967697)
        ·
          refine ⟨1341918650034240221225773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1789224866712320294967697 1341918650034240221225773)
          ·
            refine ⟨503219493762840082959665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1341918650034240221225773 503219493762840082959665)
            ·
              refine ⟨377414620322130062219749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503219493762840082959665 377414620322130062219749)
              ·
                refine ⟨70765241310399386666203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377414620322130062219749 70765241310399386666203)
                ·
                  rfl

theorem cell20_465125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 4].length) (baseStart_465125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465125 prefixEnd_465125 := by exact prefixLift 465125
  have htrace : WordTrace (prefixWord ++ tailWord_465125) baseStart_465125 baseEnd_465125 := by
    simpa [prefixWord, tailWord_465125, baseEnd_465125] using wordTrace_append hprefix tailTrace_465125
  have hstable : (prefixWord ++ tailWord_465125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465125).length < 2 ^ (prefixWord ++ tailWord_465125).sum := by decide
  have hdescent : baseEnd_465125 < baseStart_465125 := by decide
  rcases family_descends (prefixWord ++ tailWord_465125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465153 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 3]
def baseStart_465153 : Nat := 118140960795 + 465153 * 2 ^ 59
def prefixEnd_465153 : Nat := 4983230072969 + 3 ^ 40 * 465153 * 2
def baseEnd_465153 : Nat := 212308503894154507065161

theorem tailTrace_465153 : CollatzResearch.WordTrace tailWord_465153 prefixEnd_465153 212308503894154507065161 := by
  unfold tailWord_465153
  simp only [CollatzResearch.WordTrace]
  refine ⟨16965523683837597652824113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11310349122558398435216075 16965523683837597652824113)
  ·
    refine ⟨12724142762878198239618085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16965523683837597652824113 12724142762878198239618085)
    ·
      refine ⟨2385776768039662169928391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12724142762878198239618085 2385776768039662169928391)
      ·
        refine ⟨3578665152059493254892587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385776768039662169928391 3578665152059493254892587)
        ·
          refine ⟨5367997728089239882338881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578665152059493254892587 5367997728089239882338881)
          ·
            refine ⟨4025998296066929911754161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5367997728089239882338881 4025998296066929911754161)
            ·
              refine ⟨3019498722050197433815621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4025998296066929911754161 3019498722050197433815621)
              ·
                refine ⟨566156010384412018840429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3019498722050197433815621 566156010384412018840429)
                ·
                  refine ⟨212308503894154507065161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566156010384412018840429 212308503894154507065161)
                  ·
                    rfl

theorem cell20_465153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_465153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465153 prefixEnd_465153 := by exact prefixLift 465153
  have htrace : WordTrace (prefixWord ++ tailWord_465153) baseStart_465153 baseEnd_465153 := by
    simpa [prefixWord, tailWord_465153, baseEnd_465153] using wordTrace_append hprefix tailTrace_465153
  have hstable : (prefixWord ++ tailWord_465153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465153).length < 2 ^ (prefixWord ++ tailWord_465153).sum := by decide
  have hdescent : baseEnd_465153 < baseStart_465153 := by decide
  rcases family_descends (prefixWord ++ tailWord_465153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465156 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 4]
def baseStart_465156 : Nat := 118140960795 + 465156 * 2 ^ 59
def prefixEnd_465156 : Nat := 4983230072969 + 3 ^ 40 * 465156 * 2
def baseEnd_465156 : Nat := 212309873175899829965149

theorem tailTrace_465156 : CollatzResearch.WordTrace tailWord_465156 prefixEnd_465156 212309873175899829965149 := by
  unfold tailWord_465156
  simp only [CollatzResearch.WordTrace]
  refine ⟨8482816551413364582591661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11310422068551152776788881 8482816551413364582591661)
  ·
    refine ⟨3181056206780011718471873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8482816551413364582591661 3181056206780011718471873)
    ·
      refine ⟨2385792155085008788853905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3181056206780011718471873 2385792155085008788853905)
      ·
        refine ⟨1789344116313756591640429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2385792155085008788853905 1789344116313756591640429)
        ·
          refine ⟨671004043617658721865161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1789344116313756591640429 671004043617658721865161)
          ·
            refine ⟨503253032713244041398871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671004043617658721865161 503253032713244041398871)
            ·
              refine ⟨754879549069866062098307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503253032713244041398871 754879549069866062098307)
              ·
                refine ⟨1132319323604799093147461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754879549069866062098307 1132319323604799093147461)
                ·
                  refine ⟨212309873175899829965149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132319323604799093147461 212309873175899829965149)
                  ·
                    rfl

theorem cell20_465156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_465156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465156 prefixEnd_465156 := by exact prefixLift 465156
  have htrace : WordTrace (prefixWord ++ tailWord_465156) baseStart_465156 baseEnd_465156 := by
    simpa [prefixWord, tailWord_465156, baseEnd_465156] using wordTrace_append hprefix tailTrace_465156
  have hstable : (prefixWord ++ tailWord_465156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465156).length < 2 ^ (prefixWord ++ tailWord_465156).sum := by decide
  have hdescent : baseEnd_465156 < baseStart_465156 := by decide
  rcases family_descends (prefixWord ++ tailWord_465156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465215 : List Nat := [1, 1, 2, 2, 4, 1, 3, 4, 2]
def baseStart_465215 : Nat := 118140960795 + 465215 * 2 ^ 59
def prefixEnd_465215 : Nat := 4983230072969 + 3 ^ 40 * 465215 * 2
def baseEnd_465215 : Nat := 212336802383557846998241

theorem tailTrace_465215 : CollatzResearch.WordTrace tailWord_465215 prefixEnd_465215 212336802383557846998241 := by
  unfold tailWord_465215
  simp only [CollatzResearch.WordTrace]
  refine ⟨16967785009612982241581099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11311856673075321494387399 16967785009612982241581099)
  ·
    refine ⟨25451677514419473362371649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16967785009612982241581099 25451677514419473362371649)
    ·
      refine ⟨19088758135814605021778737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25451677514419473362371649 19088758135814605021778737)
      ·
        refine ⟨14316568601860953766334053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19088758135814605021778737 14316568601860953766334053)
        ·
          refine ⟨2684356612848928831187635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14316568601860953766334053 2684356612848928831187635)
          ·
            refine ⟨4026534919273393246781453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684356612848928831187635 4026534919273393246781453)
            ·
              refine ⟨1509950594727522467543045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4026534919273393246781453 1509950594727522467543045)
              ·
                refine ⟨283115736511410462664321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1509950594727522467543045 283115736511410462664321)
                ·
                  refine ⟨212336802383557846998241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283115736511410462664321 212336802383557846998241)
                  ·
                    rfl

theorem cell20_465215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 2].length) (baseStart_465215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465215 prefixEnd_465215 := by exact prefixLift 465215
  have htrace : WordTrace (prefixWord ++ tailWord_465215) baseStart_465215 baseEnd_465215 := by
    simpa [prefixWord, tailWord_465215, baseEnd_465215] using wordTrace_append hprefix tailTrace_465215
  have hstable : (prefixWord ++ tailWord_465215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465215).length < 2 ^ (prefixWord ++ tailWord_465215).sum := by decide
  have hdescent : baseEnd_465215 < baseStart_465215 := by decide
  rcases family_descends (prefixWord ++ tailWord_465215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465236 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_465236 : Nat := 118140960795 + 465236 * 2 ^ 59
def prefixEnd_465236 : Nat := 4983230072969 + 3 ^ 40 * 465236 * 2
def baseEnd_465236 : Nat := 212346387355775107298155

theorem tailTrace_465236 : CollatzResearch.WordTrace tailWord_465236 prefixEnd_465236 212346387355775107298155 := by
  unfold tailWord_465236
  simp only [CollatzResearch.WordTrace]
  refine ⟨8484275471268451414047781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11312367295024601885397041 8484275471268451414047781)
  ·
    refine ⟨1590801650862834640133959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8484275471268451414047781 1590801650862834640133959)
    ·
      refine ⟨2386202476294251960200939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1590801650862834640133959 2386202476294251960200939)
      ·
        refine ⟨3579303714441377940301409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2386202476294251960200939 3579303714441377940301409)
        ·
          refine ⟨2684477785831033455226057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3579303714441377940301409 2684477785831033455226057)
          ·
            refine ⟨2013358339373275091419543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2684477785831033455226057 2013358339373275091419543)
            ·
              refine ⟨3020037509059912637129315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013358339373275091419543 3020037509059912637129315)
              ·
                refine ⟨4530056263589868955693973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020037509059912637129315 4530056263589868955693973)
                ·
                  refine ⟨212346387355775107298155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4530056263589868955693973 212346387355775107298155)
                  ·
                    rfl

theorem cell20_465236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_465236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465236 prefixEnd_465236 := by exact prefixLift 465236
  have htrace : WordTrace (prefixWord ++ tailWord_465236) baseStart_465236 baseEnd_465236 := by
    simpa [prefixWord, tailWord_465236, baseEnd_465236] using wordTrace_append hprefix tailTrace_465236
  have hstable : (prefixWord ++ tailWord_465236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465236).length < 2 ^ (prefixWord ++ tailWord_465236).sum := by decide
  have hdescent : baseEnd_465236 < baseStart_465236 := by decide
  rcases family_descends (prefixWord ++ tailWord_465236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465253 : List Nat := [1, 3, 1, 3, 1, 3, 1, 5, 2]
def baseStart_465253 : Nat := 118140960795 + 465253 * 2 ^ 59
def prefixEnd_465253 : Nat := 4983230072969 + 3 ^ 40 * 465253 * 2
def baseEnd_465253 : Nat := 212354146618998603731419

theorem tailTrace_465253 : CollatzResearch.WordTrace tailWord_465253 prefixEnd_465253 212354146618998603731419 := by
  unfold tailWord_465253
  simp only [CollatzResearch.WordTrace]
  refine ⟨16969170983475314731464413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11312780655650209820976275 16969170983475314731464413)
  ·
    refine ⟨6363439118803243024299155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16969170983475314731464413 6363439118803243024299155)
    ·
      refine ⟨9545158678204864536448733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6363439118803243024299155 9545158678204864536448733)
      ·
        refine ⟨3579434504326824201168275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9545158678204864536448733 3579434504326824201168275)
        ·
          refine ⟨5369151756490236301752413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3579434504326824201168275 5369151756490236301752413)
          ·
            refine ⟨2013431908683838613157155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5369151756490236301752413 2013431908683838613157155)
            ·
              refine ⟨3020147863025757919735733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013431908683838613157155 3020147863025757919735733)
              ·
                refine ⟨283138862158664804975225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3020147863025757919735733 283138862158664804975225)
                ·
                  refine ⟨212354146618998603731419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283138862158664804975225 212354146618998603731419)
                  ·
                    rfl

theorem cell20_465253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_465253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465253 prefixEnd_465253 := by exact prefixLift 465253
  have htrace : WordTrace (prefixWord ++ tailWord_465253) baseStart_465253 baseEnd_465253 := by
    simpa [prefixWord, tailWord_465253, baseEnd_465253] using wordTrace_append hprefix tailTrace_465253
  have hstable : (prefixWord ++ tailWord_465253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465253).length < 2 ^ (prefixWord ++ tailWord_465253).sum := by decide
  have hdescent : baseEnd_465253 < baseStart_465253 := by decide
  rcases family_descends (prefixWord ++ tailWord_465253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465257 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_465257 : Nat := 118140960795 + 465257 * 2 ^ 59
def prefixEnd_465257 : Nat := 4983230072969 + 3 ^ 40 * 465257 * 2
def baseEnd_465257 : Nat := 212355972327992367598069

theorem tailTrace_465257 : CollatzResearch.WordTrace tailWord_465257 prefixEnd_465257 212355972327992367598069 := by
  unfold tailWord_465257
  simp only [CollatzResearch.WordTrace]
  refine ⟨16969316875460823414610025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11312877916973882276406683 16969316875460823414610025)
  ·
    refine ⟨12726987656595617560957519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16969316875460823414610025 12726987656595617560957519)
    ·
      refine ⟨19090481484893426341436279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12726987656595617560957519 19090481484893426341436279)
      ·
        refine ⟨28635722227340139512154419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19090481484893426341436279 28635722227340139512154419)
        ·
          refine ⟨42953583341010209268231629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28635722227340139512154419 42953583341010209268231629)
          ·
            refine ⟨16107593752878828475586861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42953583341010209268231629 16107593752878828475586861)
            ·
              refine ⟨6040347657329560678345073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16107593752878828475586861 6040347657329560678345073)
              ·
                refine ⟨4530260742997170508758805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6040347657329560678345073 4530260742997170508758805)
                ·
                  refine ⟨212355972327992367598069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4530260742997170508758805 212355972327992367598069)
                  ·
                    rfl

theorem cell20_465257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_465257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465257 prefixEnd_465257 := by exact prefixLift 465257
  have htrace : WordTrace (prefixWord ++ tailWord_465257) baseStart_465257 baseEnd_465257 := by
    simpa [prefixWord, tailWord_465257, baseEnd_465257] using wordTrace_append hprefix tailTrace_465257
  have hstable : (prefixWord ++ tailWord_465257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465257).length < 2 ^ (prefixWord ++ tailWord_465257).sum := by decide
  have hdescent : baseEnd_465257 < baseStart_465257 := by decide
  rcases family_descends (prefixWord ++ tailWord_465257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465284 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 3]
def baseStart_465284 : Nat := 118140960795 + 465284 * 2 ^ 59
def prefixEnd_465284 : Nat := 4983230072969 + 3 ^ 40 * 465284 * 2
def baseEnd_465284 : Nat := 212368295863700273697959

theorem tailTrace_465284 : CollatzResearch.WordTrace tailWord_465284 prefixEnd_465284 212368295863700273697959 := by
  unfold tailWord_465284
  simp only [CollatzResearch.WordTrace]
  refine ⟨8485150823181503512921453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11313534430908671350561937 8485150823181503512921453)
  ·
    refine ⟨3181931558693063817345545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8485150823181503512921453 3181931558693063817345545)
    ·
      refine ⟨2386448669019797863009159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3181931558693063817345545 2386448669019797863009159)
      ·
        refine ⟨3579673003529696794513739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2386448669019797863009159 3579673003529696794513739)
        ·
          refine ⟨5369509505294545191770609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3579673003529696794513739 5369509505294545191770609)
          ·
            refine ⟨4027132128970908893827957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5369509505294545191770609 4027132128970908893827957)
            ·
              refine ⟨377543637091022708796371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4027132128970908893827957 377543637091022708796371)
              ·
                refine ⟨566315455636534063194557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377543637091022708796371 566315455636534063194557)
                ·
                  refine ⟨212368295863700273697959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566315455636534063194557 212368295863700273697959)
                  ·
                    rfl

theorem cell20_465284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_465284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465284 prefixEnd_465284 := by exact prefixLift 465284
  have htrace : WordTrace (prefixWord ++ tailWord_465284) baseStart_465284 baseEnd_465284 := by
    simpa [prefixWord, tailWord_465284, baseEnd_465284] using wordTrace_append hprefix tailTrace_465284
  have hstable : (prefixWord ++ tailWord_465284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465284).length < 2 ^ (prefixWord ++ tailWord_465284).sum := by decide
  have hdescent : baseEnd_465284 < baseStart_465284 := by decide
  rcases family_descends (prefixWord ++ tailWord_465284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465319 : List Nat := [1, 1, 6, 1, 1, 2, 8]
def baseStart_465319 : Nat := 118140960795 + 465319 * 2 ^ 59
def prefixEnd_465319 : Nat := 4983230072969 + 3 ^ 40 * 465319 * 2
def baseEnd_465319 : Nat := 23598252313043967503461

theorem tailTrace_465319 : CollatzResearch.WordTrace tailWord_465319 prefixEnd_465319 23598252313043967503461 := by
  unfold tailWord_465319
  simp only [CollatzResearch.WordTrace]
  refine ⟨16971578201236208003367011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11314385467490805335578007 16971578201236208003367011)
  ·
    refine ⟨25457367301854312005050517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16971578201236208003367011 25457367301854312005050517)
    ·
      refine ⟨1193314092274420875236743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25457367301854312005050517 1193314092274420875236743)
      ·
        refine ⟨1789971138411631312855115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193314092274420875236743 1789971138411631312855115)
        ·
          refine ⟨2684956707617446969282673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789971138411631312855115 2684956707617446969282673)
          ·
            refine ⟨2013717530713085226962005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2684956707617446969282673 2013717530713085226962005)
            ·
              refine ⟨23598252313043967503461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2013717530713085226962005 23598252313043967503461)
              ·
                rfl

theorem cell20_465319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 8].length) (baseStart_465319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465319 prefixEnd_465319 := by exact prefixLift 465319
  have htrace : WordTrace (prefixWord ++ tailWord_465319) baseStart_465319 baseEnd_465319 := by
    simpa [prefixWord, tailWord_465319, baseEnd_465319] using wordTrace_append hprefix tailTrace_465319
  have hstable : (prefixWord ++ tailWord_465319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465319).length < 2 ^ (prefixWord ++ tailWord_465319).sum := by decide
  have hdescent : baseEnd_465319 < baseStart_465319 := by decide
  rcases family_descends (prefixWord ++ tailWord_465319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465325 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 4]
def baseStart_465325 : Nat := 118140960795 + 465325 * 2 ^ 59
def prefixEnd_465325 : Nat := 4983230072969 + 3 ^ 40 * 465325 * 2
def baseEnd_465325 : Nat := 212387009380886353331125

theorem tailTrace_465325 : CollatzResearch.WordTrace tailWord_465325 prefixEnd_465325 212387009380886353331125 := by
  unfold tailWord_465325
  simp only [CollatzResearch.WordTrace]
  refine ⟨16971797039214471028085429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11314531359476314018723619 16971797039214471028085429)
  ·
    refine ⟨1591105972426356658883009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16971797039214471028085429 1591105972426356658883009)
    ·
      refine ⟨1193329479319767494162257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1591105972426356658883009 1193329479319767494162257)
      ·
        refine ⟨894997109489825620621693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1193329479319767494162257 894997109489825620621693)
        ·
          refine ⟨335623916058684607733135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 894997109489825620621693 335623916058684607733135)
          ·
            refine ⟨503435874088026911599703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335623916058684607733135 503435874088026911599703)
            ·
              refine ⟨755153811132040367399555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503435874088026911599703 755153811132040367399555)
              ·
                refine ⟨1132730716698060551099333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755153811132040367399555 1132730716698060551099333)
                ·
                  refine ⟨212387009380886353331125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132730716698060551099333 212387009380886353331125)
                  ·
                    rfl

theorem cell20_465325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_465325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465325 prefixEnd_465325 := by exact prefixLift 465325
  have htrace : WordTrace (prefixWord ++ tailWord_465325) baseStart_465325 baseEnd_465325 := by
    simpa [prefixWord, tailWord_465325, baseEnd_465325] using wordTrace_append hprefix tailTrace_465325
  have hstable : (prefixWord ++ tailWord_465325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465325).length < 2 ^ (prefixWord ++ tailWord_465325).sum := by decide
  have hdescent : baseEnd_465325 < baseStart_465325 := by decide
  rcases family_descends (prefixWord ++ tailWord_465325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465329 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 4]
def baseStart_465329 : Nat := 118140960795 + 465329 * 2 ^ 59
def prefixEnd_465329 : Nat := 4983230072969 + 3 ^ 40 * 465329 * 2
def baseEnd_465329 : Nat := 212388835089880117197775

theorem tailTrace_465329 : CollatzResearch.WordTrace tailWord_465329 prefixEnd_465329 212388835089880117197775 := by
  unfold tailWord_465329
  simp only [CollatzResearch.WordTrace]
  refine ⟨16971942931199979711231041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11314628620799986474154027 16971942931199979711231041)
  ·
    refine ⟨12728957198399984783423281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16971942931199979711231041 12728957198399984783423281)
    ·
      refine ⟨9546717898799988587567461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12728957198399984783423281 9546717898799988587567461)
      ·
        refine ⟨1790009606024997860168899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9546717898799988587567461 1790009606024997860168899)
        ·
          refine ⟨2685014409037496790253349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790009606024997860168899 2685014409037496790253349)
          ·
            refine ⟨503440201694530648172503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2685014409037496790253349 503440201694530648172503)
            ·
              refine ⟨755160302541795972258755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503440201694530648172503 755160302541795972258755)
              ·
                refine ⟨1132740453812693958388133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755160302541795972258755 1132740453812693958388133)
                ·
                  refine ⟨212388835089880117197775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132740453812693958388133 212388835089880117197775)
                  ·
                    rfl

theorem cell20_465329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_465329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465329 prefixEnd_465329 := by exact prefixLift 465329
  have htrace : WordTrace (prefixWord ++ tailWord_465329) baseStart_465329 baseEnd_465329 := by
    simpa [prefixWord, tailWord_465329, baseEnd_465329] using wordTrace_append hprefix tailTrace_465329
  have hstable : (prefixWord ++ tailWord_465329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465329).length < 2 ^ (prefixWord ++ tailWord_465329).sum := by decide
  have hdescent : baseEnd_465329 < baseStart_465329 := by decide
  rcases family_descends (prefixWord ++ tailWord_465329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465332 : List Nat := [2, 5, 2, 2, 1, 1, 2, 5]
def baseStart_465332 : Nat := 118140960795 + 465332 * 2 ^ 59
def prefixEnd_465332 : Nat := 4983230072969 + 3 ^ 40 * 465332 * 2
def baseEnd_465332 : Nat := 70796734790541813365921

theorem tailTrace_465332 : CollatzResearch.WordTrace tailWord_465332 prefixEnd_465332 70796734790541813365921 := by
  unfold tailWord_465332
  simp only [CollatzResearch.WordTrace]
  refine ⟨8486026175094555611795125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11314701566792740815726833 8486026175094555611795125)
  ·
    refine ⟨795564953915114588605793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8486026175094555611795125 795564953915114588605793)
    ·
      refine ⟨596673715436335941454345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 795564953915114588605793 596673715436335941454345)
      ·
        refine ⟨447505286577251956090759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596673715436335941454345 447505286577251956090759)
        ·
          refine ⟨671257929865877934136139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447505286577251956090759 671257929865877934136139)
          ·
            refine ⟨1006886894798816901204209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671257929865877934136139 1006886894798816901204209)
            ·
              refine ⟨755165171099112675903157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006886894798816901204209 755165171099112675903157)
              ·
                refine ⟨70796734790541813365921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 755165171099112675903157 70796734790541813365921)
                ·
                  rfl

theorem cell20_465332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_465332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465332 prefixEnd_465332 := by exact prefixLift 465332
  have htrace : WordTrace (prefixWord ++ tailWord_465332) baseStart_465332 baseEnd_465332 := by
    simpa [prefixWord, tailWord_465332, baseEnd_465332] using wordTrace_append hprefix tailTrace_465332
  have hstable : (prefixWord ++ tailWord_465332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465332).length < 2 ^ (prefixWord ++ tailWord_465332).sum := by decide
  have hdescent : baseEnd_465332 < baseStart_465332 := by decide
  rcases family_descends (prefixWord ++ tailWord_465332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465384 : List Nat := [2, 1, 4, 1, 1, 3, 4, 2, 2]
def baseStart_465384 : Nat := 118140960795 + 465384 * 2 ^ 59
def prefixEnd_465384 : Nat := 4983230072969 + 3 ^ 40 * 465384 * 2
def baseEnd_465384 : Nat := 212413938588544370364217

theorem tailTrace_465384 : CollatzResearch.WordTrace tailWord_465384 prefixEnd_465384 212413938588544370364217 := by
  unfold tailWord_465384
  simp only [CollatzResearch.WordTrace]
  refine ⟨8486974473000362052241603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11315965964000482736322137 8486974473000362052241603)
  ·
    refine ⟨12730461709500543078362405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8486974473000362052241603 12730461709500543078362405)
    ·
      refine ⟨2386961570531351827192951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12730461709500543078362405 2386961570531351827192951)
      ·
        refine ⟨3580442355797027740789427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2386961570531351827192951 3580442355797027740789427)
        ·
          refine ⟨5370663533695541611184141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580442355797027740789427 5370663533695541611184141)
          ·
            refine ⟨2013998825135828104194053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5370663533695541611184141 2013998825135828104194053)
            ·
              refine ⟨377624779712967769536385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2013998825135828104194053 377624779712967769536385)
              ·
                refine ⟨283218584784725827152289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377624779712967769536385 283218584784725827152289)
                ·
                  refine ⟨212413938588544370364217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283218584784725827152289 212413938588544370364217)
                  ·
                    rfl

theorem cell20_465384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 2].length) (baseStart_465384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465384 prefixEnd_465384 := by exact prefixLift 465384
  have htrace : WordTrace (prefixWord ++ tailWord_465384) baseStart_465384 baseEnd_465384 := by
    simpa [prefixWord, tailWord_465384, baseEnd_465384] using wordTrace_append hprefix tailTrace_465384
  have hstable : (prefixWord ++ tailWord_465384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465384).length < 2 ^ (prefixWord ++ tailWord_465384).sum := by decide
  have hdescent : baseEnd_465384 < baseStart_465384 := by decide
  rcases family_descends (prefixWord ++ tailWord_465384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465422 : List Nat := [4, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_465422 : Nat := 118140960795 + 465422 * 2 ^ 59
def prefixEnd_465422 : Nat := 4983230072969 + 3 ^ 40 * 465422 * 2
def baseEnd_465422 : Nat := 212431282823985127097395

theorem tailTrace_465422 : CollatzResearch.WordTrace tailWord_465422 prefixEnd_465422 212431282823985127097395 := by
  unfold tailWord_465422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121916864982882074295815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11316889946575371062911013 2121916864982882074295815)
  ·
    refine ⟨3182875297474323111443723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2121916864982882074295815 3182875297474323111443723)
    ·
      refine ⟨4774312946211484667165585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3182875297474323111443723 4774312946211484667165585)
      ·
        refine ⟨3580734709658613500374189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4774312946211484667165585 3580734709658613500374189)
        ·
          refine ⟨1342775516121980062640321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3580734709658613500374189 1342775516121980062640321)
          ·
            refine ⟨1007081637091485046980241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1342775516121980062640321 1007081637091485046980241)
            ·
              refine ⟨755311227818613785235181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007081637091485046980241 755311227818613785235181)
              ·
                refine ⟨283241710431980169463193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 755311227818613785235181 283241710431980169463193)
                ·
                  refine ⟨212431282823985127097395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283241710431980169463193 212431282823985127097395)
                  ·
                    rfl

theorem cell20_465422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_465422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465422 prefixEnd_465422 := by exact prefixLift 465422
  have htrace : WordTrace (prefixWord ++ tailWord_465422) baseStart_465422 baseEnd_465422 := by
    simpa [prefixWord, tailWord_465422, baseEnd_465422] using wordTrace_append hprefix tailTrace_465422
  have hstable : (prefixWord ++ tailWord_465422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465422).length < 2 ^ (prefixWord ++ tailWord_465422).sum := by decide
  have hdescent : baseEnd_465422 < baseStart_465422 := by decide
  rcases family_descends (prefixWord ++ tailWord_465422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465436 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 3]
def baseStart_465436 : Nat := 118140960795 + 465436 * 2 ^ 59
def prefixEnd_465436 : Nat := 4983230072969 + 3 ^ 40 * 465436 * 2
def baseEnd_465436 : Nat := 212437672805463300630671

theorem tailTrace_465436 : CollatzResearch.WordTrace tailWord_465436 prefixEnd_465436 212437672805463300630671 := by
  unfold tailWord_465436
  simp only [CollatzResearch.WordTrace]
  refine ⟨8487922770906168492688081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11317230361208224656917441 8487922770906168492688081)
  ·
    refine ⟨6365942078179626369516061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8487922770906168492688081 6365942078179626369516061)
    ·
      refine ⟨2387228279317359888568523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6365942078179626369516061 2387228279317359888568523)
      ·
        refine ⟨3580842418976039832852785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387228279317359888568523 3580842418976039832852785)
        ·
          refine ⟨2685631814232029874639589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3580842418976039832852785 2685631814232029874639589)
          ·
            refine ⟨503555965168505601494923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2685631814232029874639589 503555965168505601494923)
            ·
              refine ⟨755333947752758402242385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503555965168505601494923 755333947752758402242385)
              ·
                refine ⟨566500460814568801681789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755333947752758402242385 566500460814568801681789)
                ·
                  refine ⟨212437672805463300630671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566500460814568801681789 212437672805463300630671)
                  ·
                    rfl

theorem cell20_465436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_465436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465436 prefixEnd_465436 := by exact prefixLift 465436
  have htrace : WordTrace (prefixWord ++ tailWord_465436) baseStart_465436 baseEnd_465436 := by
    simpa [prefixWord, tailWord_465436, baseEnd_465436] using wordTrace_append hprefix tailTrace_465436
  have hstable : (prefixWord ++ tailWord_465436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465436).length < 2 ^ (prefixWord ++ tailWord_465436).sum := by decide
  have hdescent : baseEnd_465436 < baseStart_465436 := by decide
  rcases family_descends (prefixWord ++ tailWord_465436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465443 : List Nat := [1, 1, 1, 4, 4, 1, 2, 4, 2]
def baseStart_465443 : Nat := 118140960795 + 465443 * 2 ^ 59
def prefixEnd_465443 : Nat := 4983230072969 + 3 ^ 40 * 465443 * 2
def baseEnd_465443 : Nat := 212440867796202387397309

theorem tailTrace_465443 : CollatzResearch.WordTrace tailWord_465443 prefixEnd_465443 212440867796202387397309 := by
  unfold tailWord_465443
  simp only [CollatzResearch.WordTrace]
  refine ⟨16976100852786977180880983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11317400568524651453920655 16976100852786977180880983)
  ·
    refine ⟨25464151279180465771321475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16976100852786977180880983 25464151279180465771321475)
    ·
      refine ⟨38196226918770698656982213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25464151279180465771321475 38196226918770698656982213)
      ·
        refine ⟨7161792547269505998184165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38196226918770698656982213 7161792547269505998184165)
        ·
          refine ⟨1342836102613032374659531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7161792547269505998184165 1342836102613032374659531)
          ·
            refine ⟨2014254153919548561989297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342836102613032374659531 2014254153919548561989297)
            ·
              refine ⟨1510690615439661421491973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014254153919548561989297 1510690615439661421491973)
              ·
                refine ⟨283254490394936516529745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1510690615439661421491973 283254490394936516529745)
                ·
                  refine ⟨212440867796202387397309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283254490394936516529745 212440867796202387397309)
                  ·
                    rfl

theorem cell20_465443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 2].length) (baseStart_465443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465443 prefixEnd_465443 := by exact prefixLift 465443
  have htrace : WordTrace (prefixWord ++ tailWord_465443) baseStart_465443 baseEnd_465443 := by
    simpa [prefixWord, tailWord_465443, baseEnd_465443] using wordTrace_append hprefix tailTrace_465443
  have hstable : (prefixWord ++ tailWord_465443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465443).length < 2 ^ (prefixWord ++ tailWord_465443).sum := by decide
  have hdescent : baseEnd_465443 < baseStart_465443 := by decide
  rcases family_descends (prefixWord ++ tailWord_465443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465512 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 3]
def baseStart_465512 : Nat := 118140960795 + 465512 * 2 ^ 59
def prefixEnd_465512 : Nat := 4983230072969 + 3 ^ 40 * 465512 * 2
def baseEnd_465512 : Nat := 212472361276344814097027

theorem tailTrace_465512 : CollatzResearch.WordTrace tailWord_465512 prefixEnd_465512 212472361276344814097027 := by
  unfold tailWord_465512
  simp only [CollatzResearch.WordTrace]
  refine ⟨8489308744768500982571395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11319078326358001310095193 8489308744768500982571395)
  ·
    refine ⟨12733963117152751473857093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8489308744768500982571395 12733963117152751473857093)
    ·
      refine ⟨2387618084466140901348205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12733963117152751473857093 2387618084466140901348205)
      ·
        refine ⟨895356781674802838005577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2387618084466140901348205 895356781674802838005577)
        ·
          refine ⟨671517586256102128504183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 895356781674802838005577 671517586256102128504183)
          ·
            refine ⟨1007276379384153192756275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671517586256102128504183 1007276379384153192756275)
            ·
              refine ⟨1510914569076229789134413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007276379384153192756275 1510914569076229789134413)
              ·
                refine ⟨566592963403586170925405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1510914569076229789134413 566592963403586170925405)
                ·
                  refine ⟨212472361276344814097027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566592963403586170925405 212472361276344814097027)
                  ·
                    rfl

theorem cell20_465512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_465512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465512 prefixEnd_465512 := by exact prefixLift 465512
  have htrace : WordTrace (prefixWord ++ tailWord_465512) baseStart_465512 baseEnd_465512 := by
    simpa [prefixWord, tailWord_465512, baseEnd_465512] using wordTrace_append hprefix tailTrace_465512
  have hstable : (prefixWord ++ tailWord_465512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465512).length < 2 ^ (prefixWord ++ tailWord_465512).sum := by decide
  have hdescent : baseEnd_465512 < baseStart_465512 := by decide
  rcases family_descends (prefixWord ++ tailWord_465512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465561 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 4]
def baseStart_465561 : Nat := 118140960795 + 465561 * 2 ^ 59
def prefixEnd_465561 : Nat := 4983230072969 + 3 ^ 40 * 465561 * 2
def baseEnd_465561 : Nat := 212494726211518421463493

theorem tailTrace_465561 : CollatzResearch.WordTrace tailWord_465561 prefixEnd_465561 212494726211518421463493 := by
  unfold tailWord_465561
  simp only [CollatzResearch.WordTrace]
  refine ⟨16980404666359483333676537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11320269777572988889117691 16980404666359483333676537)
  ·
    refine ⟨12735303499769612500257403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16980404666359483333676537 12735303499769612500257403)
    ·
      refine ⟨19102955249654418750386105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12735303499769612500257403 19102955249654418750386105)
      ·
        refine ⟨14327216437240814062789579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19102955249654418750386105 14327216437240814062789579)
        ·
          refine ⟨21490824655861221094184369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14327216437240814062789579 21490824655861221094184369)
          ·
            refine ⟨16118118491895915820638277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21490824655861221094184369 16118118491895915820638277)
            ·
              refine ⟨3022147217230484216369677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16118118491895915820638277 3022147217230484216369677)
              ·
                refine ⟨1133305206461431581138629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3022147217230484216369677 1133305206461431581138629)
                ·
                  refine ⟨212494726211518421463493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1133305206461431581138629 212494726211518421463493)
                  ·
                    rfl

theorem cell20_465561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_465561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465561 prefixEnd_465561 := by exact prefixLift 465561
  have htrace : WordTrace (prefixWord ++ tailWord_465561) baseStart_465561 baseEnd_465561 := by
    simpa [prefixWord, tailWord_465561, baseEnd_465561] using wordTrace_append hprefix tailTrace_465561
  have hstable : (prefixWord ++ tailWord_465561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465561).length < 2 ^ (prefixWord ++ tailWord_465561).sum := by decide
  have hdescent : baseEnd_465561 < baseStart_465561 := by decide
  rcases family_descends (prefixWord ++ tailWord_465561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465564 : List Nat := [2, 2, 3, 2, 2, 3, 1, 5]
def baseStart_465564 : Nat := 118140960795 + 465564 * 2 ^ 59
def prefixEnd_465564 : Nat := 4983230072969 + 3 ^ 40 * 465564 * 2
def baseEnd_465564 : Nat := 70832031831087914787827

theorem tailTrace_465564 : CollatzResearch.WordTrace tailWord_465564 prefixEnd_465564 70832031831087914787827 := by
  unfold tailWord_465564
  simp only [CollatzResearch.WordTrace]
  refine ⟨8490257042674307423017873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11320342723565743230690497 8490257042674307423017873)
  ·
    refine ⟨6367692782005730567263405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8490257042674307423017873 6367692782005730567263405)
    ·
      refine ⟨2387884793252148962723777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6367692782005730567263405 2387884793252148962723777)
      ·
        refine ⟨1790913594939111722042833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2387884793252148962723777 1790913594939111722042833)
        ·
          refine ⟨1343185196204333791532125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1790913594939111722042833 1343185196204333791532125)
          ·
            refine ⟨503694448576625171824547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1343185196204333791532125 503694448576625171824547)
            ·
              refine ⟨755541672864937757736821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503694448576625171824547 755541672864937757736821)
              ·
                refine ⟨70832031831087914787827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 755541672864937757736821 70832031831087914787827)
                ·
                  rfl

theorem cell20_465564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_465564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465564 prefixEnd_465564 := by exact prefixLift 465564
  have htrace : WordTrace (prefixWord ++ tailWord_465564) baseStart_465564 baseEnd_465564 := by
    simpa [prefixWord, tailWord_465564, baseEnd_465564] using wordTrace_append hprefix tailTrace_465564
  have hstable : (prefixWord ++ tailWord_465564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465564).length < 2 ^ (prefixWord ++ tailWord_465564).sum := by decide
  have hdescent : baseEnd_465564 < baseStart_465564 := by decide
  rcases family_descends (prefixWord ++ tailWord_465564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465650 : List Nat := [3, 2, 1, 3, 1, 4, 1, 3, 2]
def baseStart_465650 : Nat := 118140960795 + 465650 * 2 ^ 59
def prefixEnd_465650 : Nat := 4983230072969 + 3 ^ 40 * 465650 * 2
def baseEnd_465650 : Nat := 212535348236629667496463

theorem tailTrace_465650 : CollatzResearch.WordTrace tailWord_465650 prefixEnd_465650 212535348236629667496463 := by
  unfold tailWord_465650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4245912690759262883416601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11322433842024701022444269 4245912690759262883416601)
  ·
    refine ⟨3184434518069447162562451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4245912690759262883416601 3184434518069447162562451)
    ·
      refine ⟨4776651777104170743843677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3184434518069447162562451 4776651777104170743843677)
      ·
        refine ⟨1791244416414064028941379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4776651777104170743843677 1791244416414064028941379)
        ·
          refine ⟨2686866624621096043412069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791244416414064028941379 2686866624621096043412069)
          ·
            refine ⟨503787492116455508139763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2686866624621096043412069 503787492116455508139763)
            ·
              refine ⟨755681238174683262209645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503787492116455508139763 755681238174683262209645)
              ·
                refine ⟨283380464315506223328617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 755681238174683262209645 283380464315506223328617)
                ·
                  refine ⟨212535348236629667496463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283380464315506223328617 212535348236629667496463)
                  ·
                    rfl

theorem cell20_465650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_465650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465650 prefixEnd_465650 := by exact prefixLift 465650
  have htrace : WordTrace (prefixWord ++ tailWord_465650) baseStart_465650 baseEnd_465650 := by
    simpa [prefixWord, tailWord_465650, baseEnd_465650] using wordTrace_append hprefix tailTrace_465650
  have hstable : (prefixWord ++ tailWord_465650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465650).length < 2 ^ (prefixWord ++ tailWord_465650).sum := by decide
  have hdescent : baseEnd_465650 < baseStart_465650 := by decide
  rcases family_descends (prefixWord ++ tailWord_465650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465668 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_465668 : Nat := 118140960795 + 465668 * 2 ^ 59
def prefixEnd_465668 : Nat := 4983230072969 + 3 ^ 40 * 465668 * 2
def baseEnd_465668 : Nat := 212543563927101604896389

theorem tailTrace_465668 : CollatzResearch.WordTrace tailWord_465668 prefixEnd_465668 212543563927101604896389 := by
  unfold tailWord_465668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492153638485920303910829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11322871517981227071881105 8492153638485920303910829)
  ·
    refine ⟨3184557614432220113966561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8492153638485920303910829 3184557614432220113966561)
    ·
      refine ⟨2388418210824165085474921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3184557614432220113966561 2388418210824165085474921)
      ·
        refine ⟨1791313658118123814106191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2388418210824165085474921 1791313658118123814106191)
        ·
          refine ⟨2686970487177185721159287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791313658118123814106191 2686970487177185721159287)
          ·
            refine ⟨4030455730765778581738931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686970487177185721159287 4030455730765778581738931)
            ·
              refine ⟨6045683596148667872608397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030455730765778581738931 6045683596148667872608397)
              ·
                refine ⟨2267131348555750452228149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6045683596148667872608397 2267131348555750452228149)
                ·
                  refine ⟨212543563927101604896389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2267131348555750452228149 212543563927101604896389)
                  ·
                    rfl

theorem cell20_465668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_465668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465668 prefixEnd_465668 := by exact prefixLift 465668
  have htrace : WordTrace (prefixWord ++ tailWord_465668) baseStart_465668 baseEnd_465668 := by
    simpa [prefixWord, tailWord_465668, baseEnd_465668] using wordTrace_append hprefix tailTrace_465668
  have hstable : (prefixWord ++ tailWord_465668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465668).length < 2 ^ (prefixWord ++ tailWord_465668).sum := by decide
  have hdescent : baseEnd_465668 < baseStart_465668 := by decide
  rcases family_descends (prefixWord ++ tailWord_465668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465671 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 4]
def baseStart_465671 : Nat := 118140960795 + 465671 * 2 ^ 59
def prefixEnd_465671 : Nat := 4983230072969 + 3 ^ 40 * 465671 * 2
def baseEnd_465671 : Nat := 212544933208846927796377

theorem tailTrace_465671 : CollatzResearch.WordTrace tailWord_465671 prefixEnd_465671 212544933208846927796377 := by
  unfold tailWord_465671
  simp only [CollatzResearch.WordTrace]
  refine ⟨16984416695960972120180867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11322944463973981413453911 16984416695960972120180867)
  ·
    refine ⟨25476625043941458180271301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16984416695960972120180867 25476625043941458180271301)
    ·
      refine ⟨4776867195739023408800869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25476625043941458180271301 4776867195739023408800869)
      ·
        refine ⟨895662599201066889150163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4776867195739023408800869 895662599201066889150163)
        ·
          refine ⟨1343493898801600333725245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895662599201066889150163 1343493898801600333725245)
          ·
            refine ⟨503810212050600125146967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1343493898801600333725245 503810212050600125146967)
            ·
              refine ⟨755715318075900187720451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503810212050600125146967 755715318075900187720451)
              ·
                refine ⟨1133572977113850281580677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755715318075900187720451 1133572977113850281580677)
                ·
                  refine ⟨212544933208846927796377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1133572977113850281580677 212544933208846927796377)
                  ·
                    rfl

theorem cell20_465671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 4].length) (baseStart_465671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465671 prefixEnd_465671 := by exact prefixLift 465671
  have htrace : WordTrace (prefixWord ++ tailWord_465671) baseStart_465671 baseEnd_465671 := by
    simpa [prefixWord, tailWord_465671, baseEnd_465671] using wordTrace_append hprefix tailTrace_465671
  have hstable : (prefixWord ++ tailWord_465671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465671).length < 2 ^ (prefixWord ++ tailWord_465671).sum := by decide
  have hdescent : baseEnd_465671 < baseStart_465671 := by decide
  rcases family_descends (prefixWord ++ tailWord_465671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465689 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_465689 : Nat := 118140960795 + 465689 * 2 ^ 59
def prefixEnd_465689 : Nat := 4983230072969 + 3 ^ 40 * 465689 * 2
def baseEnd_465689 : Nat := 212553148899318865196303

theorem tailTrace_465689 : CollatzResearch.WordTrace tailWord_465689 prefixEnd_465689 212553148899318865196303 := by
  unfold tailWord_465689
  simp only [CollatzResearch.WordTrace]
  refine ⟨16985073209895761194336121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11323382139930507462890747 16985073209895761194336121)
  ·
    refine ⟨12738804907421820895752091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16985073209895761194336121 12738804907421820895752091)
    ·
      refine ⟨19108207361132731343628137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12738804907421820895752091 19108207361132731343628137)
      ·
        refine ⟨14331155520849548507721103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19108207361132731343628137 14331155520849548507721103)
        ·
          refine ⟨21496733281274322761581655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14331155520849548507721103 21496733281274322761581655)
          ·
            refine ⟨32245099921911484142372483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21496733281274322761581655 32245099921911484142372483)
            ·
              refine ⟨48367649882867226213558725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32245099921911484142372483 48367649882867226213558725)
              ·
                refine ⟨9068934353037604915042261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48367649882867226213558725 9068934353037604915042261)
                ·
                  refine ⟨212553148899318865196303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9068934353037604915042261 212553148899318865196303)
                  ·
                    rfl

theorem cell20_465689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_465689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465689 prefixEnd_465689 := by exact prefixLift 465689
  have htrace : WordTrace (prefixWord ++ tailWord_465689) baseStart_465689 baseEnd_465689 := by
    simpa [prefixWord, tailWord_465689, baseEnd_465689] using wordTrace_append hprefix tailTrace_465689
  have hstable : (prefixWord ++ tailWord_465689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465689).length < 2 ^ (prefixWord ++ tailWord_465689).sum := by decide
  have hdescent : baseEnd_465689 < baseStart_465689 := by decide
  rcases family_descends (prefixWord ++ tailWord_465689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465716 : List Nat := [2, 5, 1, 1, 4, 7]
def baseStart_465716 : Nat := 118140960795 + 465716 * 2 ^ 59
def prefixEnd_465716 : Nat := 4983230072969 + 3 ^ 40 * 465716 * 2
def baseEnd_465716 : Nat := 7872795275371361899859

theorem tailTrace_465716 : CollatzResearch.WordTrace tailWord_465716 prefixEnd_465716 7872795275371361899859 := by
  unfold tailWord_465716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493028990398972402784501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11324038653865296537046001 8493028990398972402784501)
  ·
    refine ⟨796221467849903662761047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8493028990398972402784501 796221467849903662761047)
    ·
      refine ⟨1194332201774855494141571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796221467849903662761047 1194332201774855494141571)
      ·
        refine ⟨1791498302662283241212357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194332201774855494141571 1791498302662283241212357)
        ·
          refine ⟨335905931749178107727317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1791498302662283241212357 335905931749178107727317)
          ·
            refine ⟨7872795275371361899859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 335905931749178107727317 7872795275371361899859)
            ·
              rfl

theorem cell20_465716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 7].length) (baseStart_465716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465716 prefixEnd_465716 := by exact prefixLift 465716
  have htrace : WordTrace (prefixWord ++ tailWord_465716) baseStart_465716 baseEnd_465716 := by
    simpa [prefixWord, tailWord_465716, baseEnd_465716] using wordTrace_append hprefix tailTrace_465716
  have hstable : (prefixWord ++ tailWord_465716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465716).length < 2 ^ (prefixWord ++ tailWord_465716).sum := by decide
  have hdescent : baseEnd_465716 < baseStart_465716 := by decide
  rcases family_descends (prefixWord ++ tailWord_465716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465726 : List Nat := [4, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_465726 : Nat := 118140960795 + 465726 * 2 ^ 59
def prefixEnd_465726 : Nat := 4983230072969 + 3 ^ 40 * 465726 * 2
def baseEnd_465726 : Nat := 212570036707511180962819

theorem tailTrace_465726 : CollatzResearch.WordTrace tailWord_465726 prefixEnd_465726 212570036707511180962819 := by
  unfold tailWord_465726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2123302838845214564179129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11324281807174477675622021 2123302838845214564179129)
  ·
    refine ⟨1592477129133910923134347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2123302838845214564179129 1592477129133910923134347)
    ·
      refine ⟨2388715693700866384701521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1592477129133910923134347 2388715693700866384701521)
      ·
        refine ⟨1791536770275649788526141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2388715693700866384701521 1791536770275649788526141)
        ·
          refine ⟨671826288853368670697303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1791536770275649788526141 671826288853368670697303)
          ·
            refine ⟨1007739433280053006045955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671826288853368670697303 1007739433280053006045955)
            ·
              refine ⟨1511609149920079509068933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007739433280053006045955 1511609149920079509068933)
              ·
                refine ⟨283426715610014907950425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1511609149920079509068933 283426715610014907950425)
                ·
                  refine ⟨212570036707511180962819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283426715610014907950425 212570036707511180962819)
                  ·
                    rfl

theorem cell20_465726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_465726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465726 prefixEnd_465726 := by exact prefixLift 465726
  have htrace : WordTrace (prefixWord ++ tailWord_465726) baseStart_465726 baseEnd_465726 := by
    simpa [prefixWord, tailWord_465726, baseEnd_465726] using wordTrace_append hprefix tailTrace_465726
  have hstable : (prefixWord ++ tailWord_465726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465726).length < 2 ^ (prefixWord ++ tailWord_465726).sum := by decide
  have hdescent : baseEnd_465726 < baseStart_465726 := by decide
  rcases family_descends (prefixWord ++ tailWord_465726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465737 : List Nat := [1, 2, 1, 1, 2, 7, 1, 5]
def baseStart_465737 : Nat := 118140960795 + 465737 * 2 ^ 59
def prefixEnd_465737 : Nat := 4983230072969 + 3 ^ 40 * 465737 * 2
def baseEnd_465737 : Nat := 70858352469081343865369

theorem tailTrace_465737 : CollatzResearch.WordTrace tailWord_465737 prefixEnd_465737 70858352469081343865369 := by
  unfold tailWord_465737
  simp only [CollatzResearch.WordTrace]
  refine ⟨16986823913721865392083465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11324549275814576928055643 16986823913721865392083465)
  ·
    refine ⟨12740117935291399044062599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16986823913721865392083465 12740117935291399044062599)
    ·
      refine ⟨19110176902937098566093899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12740117935291399044062599 19110176902937098566093899)
      ·
        refine ⟨28665265354405647849140849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19110176902937098566093899 28665265354405647849140849)
        ·
          refine ⟨21498949015804235886855637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28665265354405647849140849 21498949015804235886855637)
          ·
            refine ⟨503881617557911778598179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 21498949015804235886855637 503881617557911778598179)
            ·
              refine ⟨755822426336867667897269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503881617557911778598179 755822426336867667897269)
              ·
                refine ⟨70858352469081343865369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 755822426336867667897269 70858352469081343865369)
                ·
                  rfl

theorem cell20_465737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 5].length) (baseStart_465737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465737 prefixEnd_465737 := by exact prefixLift 465737
  have htrace : WordTrace (prefixWord ++ tailWord_465737) baseStart_465737 baseEnd_465737 := by
    simpa [prefixWord, tailWord_465737, baseEnd_465737] using wordTrace_append hprefix tailTrace_465737
  have hstable : (prefixWord ++ tailWord_465737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465737).length < 2 ^ (prefixWord ++ tailWord_465737).sum := by decide
  have hdescent : baseEnd_465737 < baseStart_465737 := by decide
  rcases family_descends (prefixWord ++ tailWord_465737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465744 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 3]
def baseStart_465744 : Nat := 118140960795 + 465744 * 2 ^ 59
def prefixEnd_465744 : Nat := 4983230072969 + 3 ^ 40 * 465744 * 2
def baseEnd_465744 : Nat := 212578252397983118362745

theorem tailTrace_465744 : CollatzResearch.WordTrace tailWord_465744 prefixEnd_465744 212578252397983118362745 := by
  unfold tailWord_465744
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493539612348252793794143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11324719483131003725058857 8493539612348252793794143)
  ·
    refine ⟨12740309418522379190691215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8493539612348252793794143 12740309418522379190691215)
    ·
      refine ⟨19110464127783568786036823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12740309418522379190691215 19110464127783568786036823)
      ·
        refine ⟨28665696191675353179055235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19110464127783568786036823 28665696191675353179055235)
        ·
          refine ⟨42998544287513029768582853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28665696191675353179055235 42998544287513029768582853)
          ·
            refine ⟨8062227053908693081609285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42998544287513029768582853 8062227053908693081609285)
            ·
              refine ⟨1511667572607879952801741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8062227053908693081609285 1511667572607879952801741)
              ·
                refine ⟨566875339727954982300653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1511667572607879952801741 566875339727954982300653)
                ·
                  refine ⟨212578252397983118362745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566875339727954982300653 212578252397983118362745)
                  ·
                    rfl

theorem cell20_465744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_465744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465744 prefixEnd_465744 := by exact prefixLift 465744
  have htrace : WordTrace (prefixWord ++ tailWord_465744) baseStart_465744 baseEnd_465744 := by
    simpa [prefixWord, tailWord_465744, baseEnd_465744] using wordTrace_append hprefix tailTrace_465744
  have hstable : (prefixWord ++ tailWord_465744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465744).length < 2 ^ (prefixWord ++ tailWord_465744).sum := by decide
  have hdescent : baseEnd_465744 < baseStart_465744 := by decide
  rcases family_descends (prefixWord ++ tailWord_465744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465751 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 6]
def baseStart_465751 : Nat := 118140960795 + 465751 * 2 ^ 59
def prefixEnd_465751 : Nat := 4983230072969 + 3 ^ 40 * 465751 * 2
def baseEnd_465751 : Nat := 212581447388722205129383

theorem tailTrace_465751 : CollatzResearch.WordTrace tailWord_465751 prefixEnd_465751 212581447388722205129383 := by
  unfold tailWord_465751
  simp only [CollatzResearch.WordTrace]
  refine ⟨16987334535671145783093107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11324889690447430522062071 16987334535671145783093107)
  ·
    refine ⟨25481001803506718674639661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16987334535671145783093107 25481001803506718674639661)
    ·
      refine ⟨9555375676315019502989873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25481001803506718674639661 9555375676315019502989873)
      ·
        refine ⟨7166531757236264627242405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9555375676315019502989873 7166531757236264627242405)
        ·
          refine ⟨1343724704481799617607951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7166531757236264627242405 1343724704481799617607951)
          ·
            refine ⟨2015587056722699426411927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343724704481799617607951 2015587056722699426411927)
            ·
              refine ⟨3023380585084049139617891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2015587056722699426411927 3023380585084049139617891)
              ·
                refine ⟨4535070877626073709426837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023380585084049139617891 4535070877626073709426837)
                ·
                  refine ⟨212581447388722205129383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4535070877626073709426837 212581447388722205129383)
                  ·
                    rfl

theorem cell20_465751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_465751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465751 prefixEnd_465751 := by exact prefixLift 465751
  have htrace : WordTrace (prefixWord ++ tailWord_465751) baseStart_465751 baseEnd_465751 := by
    simpa [prefixWord, tailWord_465751, baseEnd_465751] using wordTrace_append hprefix tailTrace_465751
  have hstable : (prefixWord ++ tailWord_465751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465751).length < 2 ^ (prefixWord ++ tailWord_465751).sum := by decide
  have hdescent : baseEnd_465751 < baseStart_465751 := by decide
  rcases family_descends (prefixWord ++ tailWord_465751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465789 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 4]
def baseStart_465789 : Nat := 118140960795 + 465789 * 2 ^ 59
def prefixEnd_465789 : Nat := 4983230072969 + 3 ^ 40 * 465789 * 2
def baseEnd_465789 : Nat := 212598791624162961862561

theorem tailTrace_465789 : CollatzResearch.WordTrace tailWord_465789 prefixEnd_465789 212598791624162961862561 := by
  unfold tailWord_465789
  simp only [CollatzResearch.WordTrace]
  refine ⟨16988720509533478272976421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11325813673022318848650947 16988720509533478272976421)
  ·
    refine ⟨3185385095537527176183079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16988720509533478272976421 3185385095537527176183079)
    ·
      refine ⟨4778077643306290764274619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3185385095537527176183079 4778077643306290764274619)
      ·
        refine ⟨7167116464959436146411929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4778077643306290764274619 7167116464959436146411929)
        ·
          refine ⟨5375337348719577109808947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7167116464959436146411929 5375337348719577109808947)
          ·
            refine ⟨8063006023079365664713421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375337348719577109808947 8063006023079365664713421)
            ·
              refine ⟨3023627258654762124267533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8063006023079365664713421 3023627258654762124267533)
              ·
                refine ⟨1133860221995535796600325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3023627258654762124267533 1133860221995535796600325)
                ·
                  refine ⟨212598791624162961862561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1133860221995535796600325 212598791624162961862561)
                  ·
                    rfl

theorem cell20_465789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_465789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465789 prefixEnd_465789 := by exact prefixLift 465789
  have htrace : WordTrace (prefixWord ++ tailWord_465789) baseStart_465789 baseEnd_465789 := by
    simpa [prefixWord, tailWord_465789, baseEnd_465789] using wordTrace_append hprefix tailTrace_465789
  have hstable : (prefixWord ++ tailWord_465789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465789).length < 2 ^ (prefixWord ++ tailWord_465789).sum := by decide
  have hdescent : baseEnd_465789 < baseStart_465789 := by decide
  rcases family_descends (prefixWord ++ tailWord_465789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465796 : List Nat := [2, 3, 2, 1, 1, 1, 1, 9]
def baseStart_465796 : Nat := 118140960795 + 465796 * 2 ^ 59
def prefixEnd_465796 : Nat := 4983230072969 + 3 ^ 40 * 465796 * 2
def baseEnd_465796 : Nat := 70867328871634016209733

theorem tailTrace_465796 : CollatzResearch.WordTrace tailWord_465796 prefixEnd_465796 70867328871634016209733 := by
  unfold tailWord_465796
  simp only [CollatzResearch.WordTrace]
  refine ⟨8494487910254059234240621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11325983880338745645654161 8494487910254059234240621)
  ·
    refine ⟨3185432966345272212840233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8494487910254059234240621 3185432966345272212840233)
    ·
      refine ⟨2389074724758954159630175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3185432966345272212840233 2389074724758954159630175)
      ·
        refine ⟨3583612087138431239445263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2389074724758954159630175 3583612087138431239445263)
        ·
          refine ⟨5375418130707646859167895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583612087138431239445263 5375418130707646859167895)
          ·
            refine ⟨8063127196061470288751843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375418130707646859167895 8063127196061470288751843)
            ·
              refine ⟨12094690794092205433127765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8063127196061470288751843 12094690794092205433127765)
              ·
                refine ⟨70867328871634016209733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12094690794092205433127765 70867328871634016209733)
                ·
                  rfl

theorem cell20_465796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_465796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465796 prefixEnd_465796 := by exact prefixLift 465796
  have htrace : WordTrace (prefixWord ++ tailWord_465796) baseStart_465796 baseEnd_465796 := by
    simpa [prefixWord, tailWord_465796, baseEnd_465796] using wordTrace_append hprefix tailTrace_465796
  have hstable : (prefixWord ++ tailWord_465796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465796).length < 2 ^ (prefixWord ++ tailWord_465796).sum := by decide
  have hdescent : baseEnd_465796 < baseStart_465796 := by decide
  rcases family_descends (prefixWord ++ tailWord_465796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465813 : List Nat := [1, 3, 2, 1, 1, 4, 4, 4]
def baseStart_465813 : Nat := 118140960795 + 465813 * 2 ^ 59
def prefixEnd_465813 : Nat := 4983230072969 + 3 ^ 40 * 465813 * 2
def baseEnd_465813 : Nat := 70869915292708515020821

theorem tailTrace_465813 : CollatzResearch.WordTrace tailWord_465813 prefixEnd_465813 70869915292708515020821 := by
  unfold tailWord_465813
  simp only [CollatzResearch.WordTrace]
  refine ⟨16989595861446530371850093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11326397240964353581233395 16989595861446530371850093)
  ·
    refine ⟨6371098448042448889443785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16989595861446530371850093 6371098448042448889443785)
    ·
      refine ⟨4778323836031836667082839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6371098448042448889443785 4778323836031836667082839)
      ·
        refine ⟨7167485754047755000624259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4778323836031836667082839 7167485754047755000624259)
        ·
          refine ⟨10751228631071632500936389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7167485754047755000624259 10751228631071632500936389)
          ·
            refine ⟨2015855368325931093925573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10751228631071632500936389 2015855368325931093925573)
            ·
              refine ⟨377972881561112080111045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2015855368325931093925573 377972881561112080111045)
              ·
                refine ⟨70869915292708515020821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377972881561112080111045 70869915292708515020821)
                ·
                  rfl

theorem cell20_465813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 4].length) (baseStart_465813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465813 prefixEnd_465813 := by exact prefixLift 465813
  have htrace : WordTrace (prefixWord ++ tailWord_465813) baseStart_465813 baseEnd_465813 := by
    simpa [prefixWord, tailWord_465813, baseEnd_465813] using wordTrace_append hprefix tailTrace_465813
  have hstable : (prefixWord ++ tailWord_465813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465813).length < 2 ^ (prefixWord ++ tailWord_465813).sum := by decide
  have hdescent : baseEnd_465813 < baseStart_465813 := by decide
  rcases family_descends (prefixWord ++ tailWord_465813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465823 : List Nat := [1, 1, 2, 5, 2, 1, 3, 3, 2]
def baseStart_465823 : Nat := 118140960795 + 465823 * 2 ^ 59
def prefixEnd_465823 : Nat := 4983230072969 + 3 ^ 40 * 465823 * 2
def baseEnd_465823 : Nat := 212614310150609954729089

theorem tailTrace_465823 : CollatzResearch.WordTrace tailWord_465823 prefixEnd_465823 212614310150609954729089 := by
  unfold tailWord_465823
  simp only [CollatzResearch.WordTrace]
  refine ⟨16989960591410302079714123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11326640394273534719809415 16989960591410302079714123)
  ·
    refine ⟨25484940887115453119571185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16989960591410302079714123 25484940887115453119571185)
    ·
      refine ⟨19113705665336589839678389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25484940887115453119571185 19113705665336589839678389)
      ·
        refine ⟨1791909906125305297469849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19113705665336589839678389 1791909906125305297469849)
        ·
          refine ⟨1343932429593978973102387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1791909906125305297469849 1343932429593978973102387)
          ·
            refine ⟨2015898644390968459653581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343932429593978973102387 2015898644390968459653581)
            ·
              refine ⟨755961991646613172370093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2015898644390968459653581 755961991646613172370093)
              ·
                refine ⟨283485746867479939638785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 755961991646613172370093 283485746867479939638785)
                ·
                  refine ⟨212614310150609954729089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283485746867479939638785 212614310150609954729089)
                  ·
                    rfl

theorem cell20_465823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 3, 2].length) (baseStart_465823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465823 prefixEnd_465823 := by exact prefixLift 465823
  have htrace : WordTrace (prefixWord ++ tailWord_465823) baseStart_465823 baseEnd_465823 := by
    simpa [prefixWord, tailWord_465823, baseEnd_465823] using wordTrace_append hprefix tailTrace_465823
  have hstable : (prefixWord ++ tailWord_465823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465823).length < 2 ^ (prefixWord ++ tailWord_465823).sum := by decide
  have hdescent : baseEnd_465823 < baseStart_465823 := by decide
  rcases family_descends (prefixWord ++ tailWord_465823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465846 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_465846 : Nat := 118140960795 + 465846 * 2 ^ 59
def prefixEnd_465846 : Nat := 4983230072969 + 3 ^ 40 * 465846 * 2
def baseEnd_465846 : Nat := 212624807977324096962329

theorem tailTrace_465846 : CollatzResearch.WordTrace tailWord_465846 prefixEnd_465846 212624807977324096962329 := by
  unfold tailWord_465846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061924966895436062987587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11327199646884651338534261 1061924966895436062987587)
  ·
    refine ⟨1592887450343154094481381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1061924966895436062987587 1592887450343154094481381)
    ·
      refine ⟨298666396939341392715259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1592887450343154094481381 298666396939341392715259)
      ·
        refine ⟨447999595409012089072889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298666396939341392715259 447999595409012089072889)
        ·
          refine ⟨335999696556759066804667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447999595409012089072889 335999696556759066804667)
          ·
            refine ⟨503999544835138600207001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335999696556759066804667 503999544835138600207001)
            ·
              refine ⟨377999658626353950155251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503999544835138600207001 377999658626353950155251)
              ·
                refine ⟨566999487939530925232877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377999658626353950155251 566999487939530925232877)
                ·
                  refine ⟨212624807977324096962329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566999487939530925232877 212624807977324096962329)
                  ·
                    rfl

theorem cell20_465846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_465846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465846 prefixEnd_465846 := by exact prefixLift 465846
  have htrace : WordTrace (prefixWord ++ tailWord_465846) baseStart_465846 baseEnd_465846 := by
    simpa [prefixWord, tailWord_465846, baseEnd_465846] using wordTrace_append hprefix tailTrace_465846
  have hstable : (prefixWord ++ tailWord_465846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465846).length < 2 ^ (prefixWord ++ tailWord_465846).sum := by decide
  have hdescent : baseEnd_465846 < baseStart_465846 := by decide
  rcases family_descends (prefixWord ++ tailWord_465846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465879 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_465879 : Nat := 118140960795 + 465879 * 2 ^ 59
def prefixEnd_465879 : Nat := 4983230072969 + 3 ^ 40 * 465879 * 2
def baseEnd_465879 : Nat := 212639870076522648862193

theorem tailTrace_465879 : CollatzResearch.WordTrace tailWord_465879 prefixEnd_465879 212639870076522648862193 := by
  unfold tailWord_465879
  simp only [CollatzResearch.WordTrace]
  refine ⟨16992003079207423643752691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11328002052804949095835127 16992003079207423643752691)
  ·
    refine ⟨25488004618811135465629037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16992003079207423643752691 25488004618811135465629037)
    ·
      refine ⟨9558001732054175799610889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25488004618811135465629037 9558001732054175799610889)
      ·
        refine ⟨7168501299040631849708167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9558001732054175799610889 7168501299040631849708167)
        ·
          refine ⟨10752751948560947774562251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7168501299040631849708167 10752751948560947774562251)
          ·
            refine ⟨16129127922841421661843377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10752751948560947774562251 16129127922841421661843377)
            ·
              refine ⟨12096845942131066246382533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16129127922841421661843377 12096845942131066246382533)
              ·
                refine ⟨2268158614149574921196725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12096845942131066246382533 2268158614149574921196725)
                ·
                  refine ⟨212639870076522648862193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2268158614149574921196725 212639870076522648862193)
                  ·
                    rfl

theorem cell20_465879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_465879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465879 prefixEnd_465879 := by exact prefixLift 465879
  have htrace : WordTrace (prefixWord ++ tailWord_465879) baseStart_465879 baseEnd_465879 := by
    simpa [prefixWord, tailWord_465879, baseEnd_465879] using wordTrace_append hprefix tailTrace_465879
  have hstable : (prefixWord ++ tailWord_465879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465879).length < 2 ^ (prefixWord ++ tailWord_465879).sum := by decide
  have hdescent : baseEnd_465879 < baseStart_465879 := by decide
  rcases family_descends (prefixWord ++ tailWord_465879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465896 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 3]
def baseStart_465896 : Nat := 118140960795 + 465896 * 2 ^ 59
def prefixEnd_465896 : Nat := 4983230072969 + 3 ^ 40 * 465896 * 2
def baseEnd_465896 : Nat := 212647629339746145295457

theorem tailTrace_465896 : CollatzResearch.WordTrace tailWord_465896 prefixEnd_465896 212647629339746145295457 := by
  unfold tailWord_465896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8496311560072917773560771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11328415413430557031414361 8496311560072917773560771)
  ·
    refine ⟨12744467340109376660341157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8496311560072917773560771 12744467340109376660341157)
    ·
      refine ⟨2389587626270508123813967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12744467340109376660341157 2389587626270508123813967)
      ·
        refine ⟨3584381439405762185720951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2389587626270508123813967 3584381439405762185720951)
        ·
          refine ⟨5376572159108643278581427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584381439405762185720951 5376572159108643278581427)
          ·
            refine ⟨8064858238662964917872141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5376572159108643278581427 8064858238662964917872141)
            ·
              refine ⟨3024321839498611844202053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8064858238662964917872141 3024321839498611844202053)
              ·
                refine ⟨567060344905989720787885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3024321839498611844202053 567060344905989720787885)
                ·
                  refine ⟨212647629339746145295457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567060344905989720787885 212647629339746145295457)
                  ·
                    rfl

theorem cell20_465896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_465896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465896 prefixEnd_465896 := by exact prefixLift 465896
  have htrace : WordTrace (prefixWord ++ tailWord_465896) baseStart_465896 baseEnd_465896 := by
    simpa [prefixWord, tailWord_465896, baseEnd_465896] using wordTrace_append hprefix tailTrace_465896
  have hstable : (prefixWord ++ tailWord_465896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465896).length < 2 ^ (prefixWord ++ tailWord_465896).sum := by decide
  have hdescent : baseEnd_465896 < baseStart_465896 := by decide
  rcases family_descends (prefixWord ++ tailWord_465896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465917 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_465917 : Nat := 118140960795 + 465917 * 2 ^ 59
def prefixEnd_465917 : Nat := 4983230072969 + 3 ^ 40 * 465917 * 2
def baseEnd_465917 : Nat := 212657214311963405595371

theorem tailTrace_465917 : CollatzResearch.WordTrace tailWord_465917 prefixEnd_465917 212657214311963405595371 := by
  unfold tailWord_465917
  simp only [CollatzResearch.WordTrace]
  refine ⟨16993389053069756133636005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11328926035379837422424003 16993389053069756133636005)
  ·
    refine ⟨3186260447450579275056751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16993389053069756133636005 3186260447450579275056751)
    ·
      refine ⟨4779390671175868912585127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3186260447450579275056751 4779390671175868912585127)
      ·
        refine ⟨7169086006763803368877691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779390671175868912585127 7169086006763803368877691)
        ·
          refine ⟨10753629010145705053316537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169086006763803368877691 10753629010145705053316537)
          ·
            refine ⟨8065221757609278789987403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10753629010145705053316537 8065221757609278789987403)
            ·
              refine ⟨12097832636413918184981105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8065221757609278789987403 12097832636413918184981105)
              ·
                refine ⟨9073374477310438638735829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12097832636413918184981105 9073374477310438638735829)
                ·
                  refine ⟨212657214311963405595371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9073374477310438638735829 212657214311963405595371)
                  ·
                    rfl

theorem cell20_465917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_465917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465917 prefixEnd_465917 := by exact prefixLift 465917
  have htrace : WordTrace (prefixWord ++ tailWord_465917) baseStart_465917 baseEnd_465917 := by
    simpa [prefixWord, tailWord_465917, baseEnd_465917] using wordTrace_append hprefix tailTrace_465917
  have hstable : (prefixWord ++ tailWord_465917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465917).length < 2 ^ (prefixWord ++ tailWord_465917).sum := by decide
  have hdescent : baseEnd_465917 < baseStart_465917 := by decide
  rcases family_descends (prefixWord ++ tailWord_465917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465927 : List Nat := [1, 1, 4, 3, 1, 1, 5, 4]
def baseStart_465927 : Nat := 118140960795 + 465927 * 2 ^ 59
def prefixEnd_465927 : Nat := 4983230072969 + 3 ^ 40 * 465927 * 2
def baseEnd_465927 : Nat := 70887259528149271753999

theorem tailTrace_465927 : CollatzResearch.WordTrace tailWord_465927 prefixEnd_465927 70887259528149271753999 := by
  unfold tailWord_465927
  simp only [CollatzResearch.WordTrace]
  refine ⟨16993753783033527841500035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11329169188689018561000023 16993753783033527841500035)
  ·
    refine ⟨25490630674550291762250053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16993753783033527841500035 25490630674550291762250053)
    ·
      refine ⟨4779493251478179705421885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25490630674550291762250053 4779493251478179705421885)
      ·
        refine ⟨1792309969304317389533207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4779493251478179705421885 1792309969304317389533207)
        ·
          refine ⟨2688464953956476084299811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1792309969304317389533207 2688464953956476084299811)
          ·
            refine ⟨4032697430934714126449717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688464953956476084299811 4032697430934714126449717)
            ·
              refine ⟨378065384150129449354661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4032697430934714126449717 378065384150129449354661)
              ·
                refine ⟨70887259528149271753999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378065384150129449354661 70887259528149271753999)
                ·
                  rfl

theorem cell20_465927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 4].length) (baseStart_465927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465927 prefixEnd_465927 := by exact prefixLift 465927
  have htrace : WordTrace (prefixWord ++ tailWord_465927) baseStart_465927 baseEnd_465927 := by
    simpa [prefixWord, tailWord_465927, baseEnd_465927] using wordTrace_append hprefix tailTrace_465927
  have hstable : (prefixWord ++ tailWord_465927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465927).length < 2 ^ (prefixWord ++ tailWord_465927).sum := by decide
  have hdescent : baseEnd_465927 < baseStart_465927 := by decide
  rcases family_descends (prefixWord ++ tailWord_465927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465951 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 3]
def baseStart_465951 : Nat := 118140960795 + 465951 * 2 ^ 59
def prefixEnd_465951 : Nat := 4983230072969 + 3 ^ 40 * 465951 * 2
def baseEnd_465951 : Nat := 212672732838410398461899

theorem tailTrace_465951 : CollatzResearch.WordTrace tailWord_465951 prefixEnd_465951 212672732838410398461899 := by
  unfold tailWord_465951
  simp only [CollatzResearch.WordTrace]
  refine ⟨16994629134946579940373707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11329752756631053293582471 16994629134946579940373707)
  ·
    refine ⟨25491943702419869910560561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16994629134946579940373707 25491943702419869910560561)
    ·
      refine ⟨19118957776814902432920421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25491943702419869910560561 19118957776814902432920421)
      ·
        refine ⟨3584804583152794206172579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19118957776814902432920421 3584804583152794206172579)
        ·
          refine ⟨5377206874729191309258869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584804583152794206172579 5377206874729191309258869)
          ·
            refine ⟨504113144505861685243019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5377206874729191309258869 504113144505861685243019)
            ·
              refine ⟨756169716758792527864529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504113144505861685243019 756169716758792527864529)
              ·
                refine ⟨567127287569094395898397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 756169716758792527864529 567127287569094395898397)
                ·
                  refine ⟨212672732838410398461899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567127287569094395898397 212672732838410398461899)
                  ·
                    rfl

theorem cell20_465951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 3].length) (baseStart_465951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465951 prefixEnd_465951 := by exact prefixLift 465951
  have htrace : WordTrace (prefixWord ++ tailWord_465951) baseStart_465951 baseEnd_465951 := by
    simpa [prefixWord, tailWord_465951, baseEnd_465951] using wordTrace_append hprefix tailTrace_465951
  have hstable : (prefixWord ++ tailWord_465951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465951).length < 2 ^ (prefixWord ++ tailWord_465951).sum := by decide
  have hdescent : baseEnd_465951 < baseStart_465951 := by decide
  rcases family_descends (prefixWord ++ tailWord_465951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465982 : List Nat := [4, 2, 1, 3, 1, 1, 4, 4]
def baseStart_465982 : Nat := 118140960795 + 465982 * 2 ^ 59
def prefixEnd_465982 : Nat := 4983230072969 + 3 ^ 40 * 465982 * 2
def baseEnd_465982 : Nat := 70895627361037356142813

theorem tailTrace_465982 : CollatzResearch.WordTrace tailWord_465982 prefixEnd_465982 70895627361037356142813 := by
  unfold tailWord_465982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2124469974729284029344025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11330506531889514823168133 2124469974729284029344025)
  ·
    refine ⟨1593352481046963022008019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2124469974729284029344025 1593352481046963022008019)
    ·
      refine ⟨2390028721570444533012029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1593352481046963022008019 2390028721570444533012029)
      ·
        refine ⟨896260770588916699879511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2390028721570444533012029 896260770588916699879511)
        ·
          refine ⟨1344391155883375049819267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896260770588916699879511 1344391155883375049819267)
          ·
            refine ⟨2016586733825062574728901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344391155883375049819267 2016586733825062574728901)
            ·
              refine ⟨378110012592199232761669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2016586733825062574728901 378110012592199232761669)
              ·
                refine ⟨70895627361037356142813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378110012592199232761669 70895627361037356142813)
                ·
                  rfl

theorem cell20_465982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_465982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_465982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_465982 prefixEnd_465982 := by exact prefixLift 465982
  have htrace : WordTrace (prefixWord ++ tailWord_465982) baseStart_465982 baseEnd_465982 := by
    simpa [prefixWord, tailWord_465982, baseEnd_465982] using wordTrace_append hprefix tailTrace_465982
  have hstable : (prefixWord ++ tailWord_465982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465982).length < 2 ^ (prefixWord ++ tailWord_465982).sum := by decide
  have hdescent : baseEnd_465982 < baseStart_465982 := by decide
  rcases family_descends (prefixWord ++ tailWord_465982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466000 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_466000 : Nat := 118140960795 + 466000 * 2 ^ 59
def prefixEnd_466000 : Nat := 4983230072969 + 3 ^ 40 * 466000 * 2
def baseEnd_466000 : Nat := 212695097773584005828365

theorem tailTrace_466000 : CollatzResearch.WordTrace tailWord_466000 prefixEnd_466000 212695097773584005828365 := by
  unfold tailWord_466000
  simp only [CollatzResearch.WordTrace]
  refine ⟨8498208155884530654453727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11330944207846040872604969 8498208155884530654453727)
  ·
    refine ⟨12747312233826795981680591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8498208155884530654453727 12747312233826795981680591)
    ·
      refine ⟨19120968350740193972520887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12747312233826795981680591 19120968350740193972520887)
      ·
        refine ⟨28681452526110290958781331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19120968350740193972520887 28681452526110290958781331)
        ·
          refine ⟨43022178789165436438171997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28681452526110290958781331 43022178789165436438171997)
          ·
            refine ⟨16133317045937038664314499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43022178789165436438171997 16133317045937038664314499)
            ·
              refine ⟨24199975568905557996471749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16133317045937038664314499 24199975568905557996471749)
              ·
                refine ⟨4537495419169792124338453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24199975568905557996471749 4537495419169792124338453)
                ·
                  refine ⟨212695097773584005828365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4537495419169792124338453 212695097773584005828365)
                  ·
                    rfl

theorem cell20_466000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_466000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466000 prefixEnd_466000 := by exact prefixLift 466000
  have htrace : WordTrace (prefixWord ++ tailWord_466000) baseStart_466000 baseEnd_466000 := by
    simpa [prefixWord, tailWord_466000, baseEnd_466000] using wordTrace_append hprefix tailTrace_466000
  have hstable : (prefixWord ++ tailWord_466000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466000).length < 2 ^ (prefixWord ++ tailWord_466000).sum := by decide
  have hdescent : baseEnd_466000 < baseStart_466000 := by decide
  rcases family_descends (prefixWord ++ tailWord_466000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466017 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 4]
def baseStart_466017 : Nat := 118140960795 + 466017 * 2 ^ 59
def prefixEnd_466017 : Nat := 4983230072969 + 3 ^ 40 * 466017 * 2
def baseEnd_466017 : Nat := 212702857036807502261629

theorem tailTrace_466017 : CollatzResearch.WordTrace tailWord_466017 prefixEnd_466017 212702857036807502261629 := by
  unfold tailWord_466017
  simp only [CollatzResearch.WordTrace]
  refine ⟨16997036352707473212276305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11331357568471648808184203 16997036352707473212276305)
  ·
    refine ⟨12747777264530604909207229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16997036352707473212276305 12747777264530604909207229)
    ·
      refine ⟨4780416474198976840952711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12747777264530604909207229 4780416474198976840952711)
      ·
        refine ⟨7170624711298465261429067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4780416474198976840952711 7170624711298465261429067)
        ·
          refine ⟨10755937066947697892143601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7170624711298465261429067 10755937066947697892143601)
          ·
            refine ⟨8066952800210773419107701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10755937066947697892143601 8066952800210773419107701)
            ·
              refine ⟨756276825019760008041347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8066952800210773419107701 756276825019760008041347)
              ·
                refine ⟨1134415237529640012062021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756276825019760008041347 1134415237529640012062021)
                ·
                  refine ⟨212702857036807502261629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1134415237529640012062021 212702857036807502261629)
                  ·
                    rfl

theorem cell20_466017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_466017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466017 prefixEnd_466017 := by exact prefixLift 466017
  have htrace : WordTrace (prefixWord ++ tailWord_466017) baseStart_466017 baseEnd_466017 := by
    simpa [prefixWord, tailWord_466017, baseEnd_466017] using wordTrace_append hprefix tailTrace_466017
  have hstable : (prefixWord ++ tailWord_466017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466017).length < 2 ^ (prefixWord ++ tailWord_466017).sum := by decide
  have hdescent : baseEnd_466017 < baseStart_466017 := by decide
  rcases family_descends (prefixWord ++ tailWord_466017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466062 : List Nat := [4, 1, 1, 3, 2, 9]
def baseStart_466062 : Nat := 118140960795 + 466062 * 2 ^ 59
def prefixEnd_466062 : Nat := 4983230072969 + 3 ^ 40 * 466062 * 2
def baseEnd_466062 : Nat := 7878644306036568361535

theorem tailTrace_466062 : CollatzResearch.WordTrace tailWord_466062 prefixEnd_466062 7878644306036568361535 := by
  unfold tailWord_466062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2124834704693055737208055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11332451758362963931776293 2124834704693055737208055)
  ·
    refine ⟨3187252057039583605812083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2124834704693055737208055 3187252057039583605812083)
    ·
      refine ⟨4780878085559375408718125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3187252057039583605812083 4780878085559375408718125)
      ·
        refine ⟨1792829282084765778269297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4780878085559375408718125 1792829282084765778269297)
        ·
          refine ⟨1344621961563574333701973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1792829282084765778269297 1344621961563574333701973)
          ·
            refine ⟨7878644306036568361535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1344621961563574333701973 7878644306036568361535)
            ·
              rfl

theorem cell20_466062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 9].length) (baseStart_466062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466062 prefixEnd_466062 := by exact prefixLift 466062
  have htrace : WordTrace (prefixWord ++ tailWord_466062) baseStart_466062 baseEnd_466062 := by
    simpa [prefixWord, tailWord_466062, baseEnd_466062] using wordTrace_append hprefix tailTrace_466062
  have hstable : (prefixWord ++ tailWord_466062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466062).length < 2 ^ (prefixWord ++ tailWord_466062).sum := by decide
  have hdescent : baseEnd_466062 < baseStart_466062 := by decide
  rcases family_descends (prefixWord ++ tailWord_466062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466151 : List Nat := [1, 1, 5, 3, 3, 1, 2, 4]
def baseStart_466151 : Nat := 118140960795 + 466151 * 2 ^ 59
def prefixEnd_466151 : Nat := 4983230072969 + 3 ^ 40 * 466151 * 2
def baseEnd_466151 : Nat := 70921339429366197264805

theorem tailTrace_466151 : CollatzResearch.WordTrace tailWord_466151 prefixEnd_466151 70921339429366197264805 := by
  unfold tailWord_466151
  simp only [CollatzResearch.WordTrace]
  refine ⟨17001923734222014097654307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11334615822814676065102871 17001923734222014097654307)
  ·
    refine ⟨25502885601333021146481461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17001923734222014097654307 25502885601333021146481461)
    ·
      refine ⟨2390895525124970732482637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25502885601333021146481461 2390895525124970732482637)
      ·
        refine ⟨896585821921864024680989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2390895525124970732482637 896585821921864024680989)
        ·
          refine ⟨336219683220699009255371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 896585821921864024680989 336219683220699009255371)
          ·
            refine ⟨504329524831048513883057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336219683220699009255371 504329524831048513883057)
            ·
              refine ⟨378247143623286385412293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504329524831048513883057 378247143623286385412293)
              ·
                refine ⟨70921339429366197264805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378247143623286385412293 70921339429366197264805)
                ·
                  rfl

theorem cell20_466151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 4].length) (baseStart_466151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466151 prefixEnd_466151 := by exact prefixLift 466151
  have htrace : WordTrace (prefixWord ++ tailWord_466151) baseStart_466151 baseEnd_466151 := by
    simpa [prefixWord, tailWord_466151, baseEnd_466151] using wordTrace_append hprefix tailTrace_466151
  have hstable : (prefixWord ++ tailWord_466151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466151).length < 2 ^ (prefixWord ++ tailWord_466151).sum := by decide
  have hdescent : baseEnd_466151 < baseStart_466151 := by decide
  rcases family_descends (prefixWord ++ tailWord_466151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466155 : List Nat := [1, 1, 1, 1, 2, 8, 2, 4]
def baseStart_466155 : Nat := 118140960795 + 466155 * 2 ^ 59
def prefixEnd_466155 : Nat := 4983230072969 + 3 ^ 40 * 466155 * 2
def baseEnd_466155 : Nat := 70921947999030785220355

theorem tailTrace_466155 : CollatzResearch.WordTrace tailWord_466155 prefixEnd_466155 70921947999030785220355 := by
  unfold tailWord_466155
  simp only [CollatzResearch.WordTrace]
  refine ⟨17002069626207522780799919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11334713084138348520533279 17002069626207522780799919)
  ·
    refine ⟨25503104439311284171199879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17002069626207522780799919 25503104439311284171199879)
    ·
      refine ⟨38254656658966926256799819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25503104439311284171199879 38254656658966926256799819)
      ·
        refine ⟨57381984988450389385199729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38254656658966926256799819 57381984988450389385199729)
        ·
          refine ⟨43036488741337792038899797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57381984988450389385199729 43036488741337792038899797)
          ·
            refine ⟨504333852437552250455857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 43036488741337792038899797 504333852437552250455857)
            ·
              refine ⟨378250389328164187841893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504333852437552250455857 378250389328164187841893)
              ·
                refine ⟨70921947999030785220355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378250389328164187841893 70921947999030785220355)
                ·
                  rfl

theorem cell20_466155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 4].length) (baseStart_466155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466155 prefixEnd_466155 := by exact prefixLift 466155
  have htrace : WordTrace (prefixWord ++ tailWord_466155) baseStart_466155 baseEnd_466155 := by
    simpa [prefixWord, tailWord_466155, baseEnd_466155] using wordTrace_append hprefix tailTrace_466155
  have hstable : (prefixWord ++ tailWord_466155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466155).length < 2 ^ (prefixWord ++ tailWord_466155).sum := by decide
  have hdescent : baseEnd_466155 < baseStart_466155 := by decide
  rcases family_descends (prefixWord ++ tailWord_466155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466200 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 3]
def baseStart_466200 : Nat := 118140960795 + 466200 * 2 ^ 59
def prefixEnd_466200 : Nat := 4983230072969 + 3 ^ 40 * 466200 * 2
def baseEnd_466200 : Nat := 212786383223272199160881

theorem tailTrace_466200 : CollatzResearch.WordTrace tailWord_466200 prefixEnd_466200 212786383223272199160881 := by
  unfold tailWord_466200
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501855455522247733094027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11335807274029663644125369 8501855455522247733094027)
  ·
    refine ⟨12752783183283371599641041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8501855455522247733094027 12752783183283371599641041)
    ·
      refine ⟨9564587387462528699730781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12752783183283371599641041 9564587387462528699730781)
      ·
        refine ⟨3586720270298448262399043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9564587387462528699730781 3586720270298448262399043)
        ·
          refine ⟨5380080405447672393598565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586720270298448262399043 5380080405447672393598565)
          ·
            refine ⟨1008765076021438573799731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5380080405447672393598565 1008765076021438573799731)
            ·
              refine ⟨1513147614032157860699597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008765076021438573799731 1513147614032157860699597)
              ·
                refine ⟨567430355262059197762349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1513147614032157860699597 567430355262059197762349)
                ·
                  refine ⟨212786383223272199160881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567430355262059197762349 212786383223272199160881)
                  ·
                    rfl

theorem cell20_466200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_466200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466200 prefixEnd_466200 := by exact prefixLift 466200
  have htrace : WordTrace (prefixWord ++ tailWord_466200) baseStart_466200 baseEnd_466200 := by
    simpa [prefixWord, tailWord_466200, baseEnd_466200] using wordTrace_append hprefix tailTrace_466200
  have hstable : (prefixWord ++ tailWord_466200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466200).length < 2 ^ (prefixWord ++ tailWord_466200).sum := by decide
  have hdescent : baseEnd_466200 < baseStart_466200 := by decide
  rcases family_descends (prefixWord ++ tailWord_466200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466237 : List Nat := [1, 4, 1, 5, 1, 2, 2, 2, 2]
def baseStart_466237 : Nat := 118140960795 + 466237 * 2 ^ 59
def prefixEnd_466237 : Nat := 4983230072969 + 3 ^ 40 * 466237 * 2
def baseEnd_466237 : Nat := 212803271031464514927397

theorem tailTrace_466237 : CollatzResearch.WordTrace tailWord_466237 prefixEnd_466237 212803271031464514927397 := by
  unfold tailWord_466237
  simp only [CollatzResearch.WordTrace]
  refine ⟨17005060411910450785284965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11336706941273633856856643 17005060411910450785284965)
  ·
    refine ⟨3188448827233209522240931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17005060411910450785284965 3188448827233209522240931)
    ·
      refine ⟨4782673240849814283361397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3188448827233209522240931 4782673240849814283361397)
      ·
        refine ⟨448375616329670089065131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4782673240849814283361397 448375616329670089065131)
        ·
          refine ⟨672563424494505133597697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448375616329670089065131 672563424494505133597697)
          ·
            refine ⟨504422568370878850198273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672563424494505133597697 504422568370878850198273)
            ·
              refine ⟨378316926278159137648705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504422568370878850198273 378316926278159137648705)
              ·
                refine ⟨283737694708619353236529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378316926278159137648705 283737694708619353236529)
                ·
                  refine ⟨212803271031464514927397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283737694708619353236529 212803271031464514927397)
                  ·
                    rfl

theorem cell20_466237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_466237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466237 prefixEnd_466237 := by exact prefixLift 466237
  have htrace : WordTrace (prefixWord ++ tailWord_466237) baseStart_466237 baseEnd_466237 := by
    simpa [prefixWord, tailWord_466237, baseEnd_466237] using wordTrace_append hprefix tailTrace_466237
  have hstable : (prefixWord ++ tailWord_466237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466237).length < 2 ^ (prefixWord ++ tailWord_466237).sum := by decide
  have hdescent : baseEnd_466237 < baseStart_466237 := by decide
  rcases family_descends (prefixWord ++ tailWord_466237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466241 : List Nat := [1, 2, 5, 2, 1, 2, 1, 4, 2]
def baseStart_466241 : Nat := 118140960795 + 466241 * 2 ^ 59
def prefixEnd_466241 : Nat := 4983230072969 + 3 ^ 40 * 466241 * 2
def baseEnd_466241 : Nat := 212805096740458278794047

theorem tailTrace_466241 : CollatzResearch.WordTrace tailWord_466241 prefixEnd_466241 212805096740458278794047 := by
  unfold tailWord_466241
  simp only [CollatzResearch.WordTrace]
  refine ⟨17005206303895959468430577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11336804202597306312287051 17005206303895959468430577)
  ·
    refine ⟨12753904727921969601322933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17005206303895959468430577 12753904727921969601322933)
    ·
      refine ⟨1195678568242684650124025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12753904727921969601322933 1195678568242684650124025)
      ·
        refine ⟨896758926182013487593019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1195678568242684650124025 896758926182013487593019)
        ·
          refine ⟨1345138389273020231389529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896758926182013487593019 1345138389273020231389529)
          ·
            refine ⟨1008853791954765173542147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1345138389273020231389529 1008853791954765173542147)
            ·
              refine ⟨1513280687932147760313221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008853791954765173542147 1513280687932147760313221)
              ·
                refine ⟨283740128987277705058729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1513280687932147760313221 283740128987277705058729)
                ·
                  refine ⟨212805096740458278794047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283740128987277705058729 212805096740458278794047)
                  ·
                    rfl

theorem cell20_466241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 2].length) (baseStart_466241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466241 prefixEnd_466241 := by exact prefixLift 466241
  have htrace : WordTrace (prefixWord ++ tailWord_466241) baseStart_466241 baseEnd_466241 := by
    simpa [prefixWord, tailWord_466241, baseEnd_466241] using wordTrace_append hprefix tailTrace_466241
  have hstable : (prefixWord ++ tailWord_466241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466241).length < 2 ^ (prefixWord ++ tailWord_466241).sum := by decide
  have hdescent : baseEnd_466241 < baseStart_466241 := by decide
  rcases family_descends (prefixWord ++ tailWord_466241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466252 : List Nat := [2, 2, 1, 3, 2, 2, 3, 5]
def baseStart_466252 : Nat := 118140960795 + 466252 * 2 ^ 59
def prefixEnd_466252 : Nat := 4983230072969 + 3 ^ 40 * 466252 * 2
def baseEnd_466252 : Nat := 70936705813397043142445

theorem tailTrace_466252 : CollatzResearch.WordTrace tailWord_466252 prefixEnd_466252 70936705813397043142445 := by
  unfold tailWord_466252
  simp only [CollatzResearch.WordTrace]
  refine ⟨8502803753428054173540505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11337071671237405564720673 8502803753428054173540505)
  ·
    refine ⟨6377102815071040630155379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8502803753428054173540505 6377102815071040630155379)
    ·
      refine ⟨9565654222606560945233069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6377102815071040630155379 9565654222606560945233069)
      ·
        refine ⟨3587120333477460354462401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9565654222606560945233069 3587120333477460354462401)
        ·
          refine ⟨2690340250108095265846801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3587120333477460354462401 2690340250108095265846801)
          ·
            refine ⟨2017755187581071449385101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2690340250108095265846801 2017755187581071449385101)
            ·
              refine ⟨756658195342901793519413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2017755187581071449385101 756658195342901793519413)
              ·
                refine ⟨70936705813397043142445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 756658195342901793519413 70936705813397043142445)
                ·
                  rfl

theorem cell20_466252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_466252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466252 prefixEnd_466252 := by exact prefixLift 466252
  have htrace : WordTrace (prefixWord ++ tailWord_466252) baseStart_466252 baseEnd_466252 := by
    simpa [prefixWord, tailWord_466252, baseEnd_466252] using wordTrace_append hprefix tailTrace_466252
  have hstable : (prefixWord ++ tailWord_466252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466252).length < 2 ^ (prefixWord ++ tailWord_466252).sum := by decide
  have hdescent : baseEnd_466252 < baseStart_466252 := by decide
  rcases family_descends (prefixWord ++ tailWord_466252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466259 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 3]
def baseStart_466259 : Nat := 118140960795 + 466259 * 2 ^ 59
def prefixEnd_466259 : Nat := 4983230072969 + 3 ^ 40 * 466259 * 2
def baseEnd_466259 : Nat := 212813312430930216193973

theorem tailTrace_466259 : CollatzResearch.WordTrace tailWord_466259 prefixEnd_466259 212813312430930216193973 := by
  unfold tailWord_466259
  simp only [CollatzResearch.WordTrace]
  refine ⟨17005862817830748542585831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11337241878553832361723887 17005862817830748542585831)
  ·
    refine ⟨25508794226746122813878747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17005862817830748542585831 25508794226746122813878747)
    ·
      refine ⟨38263191340119184220818121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25508794226746122813878747 38263191340119184220818121)
      ·
        refine ⟨28697393505089388165613591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38263191340119184220818121 28697393505089388165613591)
        ·
          refine ⟨43046090257634082248420387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28697393505089388165613591 43046090257634082248420387)
          ·
            refine ⟨64569135386451123372630581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43046090257634082248420387 64569135386451123372630581)
            ·
              refine ⟨6053356442479792816184117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64569135386451123372630581 6053356442479792816184117)
              ·
                refine ⟨567502166482480576517261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6053356442479792816184117 567502166482480576517261)
                ·
                  refine ⟨212813312430930216193973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567502166482480576517261 212813312430930216193973)
                  ·
                    rfl

theorem cell20_466259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 3].length) (baseStart_466259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466259 prefixEnd_466259 := by exact prefixLift 466259
  have htrace : WordTrace (prefixWord ++ tailWord_466259) baseStart_466259 baseEnd_466259 := by
    simpa [prefixWord, tailWord_466259, baseEnd_466259] using wordTrace_append hprefix tailTrace_466259
  have hstable : (prefixWord ++ tailWord_466259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466259).length < 2 ^ (prefixWord ++ tailWord_466259).sum := by decide
  have hdescent : baseEnd_466259 < baseStart_466259 := by decide
  rcases family_descends (prefixWord ++ tailWord_466259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466266 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_466266 : Nat := 118140960795 + 466266 * 2 ^ 59
def prefixEnd_466266 : Nat := 4983230072969 + 3 ^ 40 * 466266 * 2
def baseEnd_466266 : Nat := 212816507421669302960611

theorem tailTrace_466266 : CollatzResearch.WordTrace tailWord_466266 prefixEnd_466266 212816507421669302960611 := by
  unfold tailWord_466266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4251529532201347184522663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11337412085870259158727101 4251529532201347184522663)
  ·
    refine ⟨6377294298302020776783995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4251529532201347184522663 6377294298302020776783995)
    ·
      refine ⟨9565941447453031165175993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6377294298302020776783995 9565941447453031165175993)
      ·
        refine ⟨7174456085589773373881995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9565941447453031165175993 7174456085589773373881995)
        ·
          refine ⟨10761684128384660060822993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7174456085589773373881995 10761684128384660060822993)
          ·
            refine ⟨8071263096288495045617245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10761684128384660060822993 8071263096288495045617245)
            ·
              refine ⟨3026723661108185642106467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8071263096288495045617245 3026723661108185642106467)
              ·
                refine ⟨4540085491662278463159701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026723661108185642106467 4540085491662278463159701)
                ·
                  refine ⟨212816507421669302960611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4540085491662278463159701 212816507421669302960611)
                  ·
                    rfl

theorem cell20_466266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_466266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466266 prefixEnd_466266 := by exact prefixLift 466266
  have htrace : WordTrace (prefixWord ++ tailWord_466266) baseStart_466266 baseEnd_466266 := by
    simpa [prefixWord, tailWord_466266, baseEnd_466266] using wordTrace_append hprefix tailTrace_466266
  have hstable : (prefixWord ++ tailWord_466266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466266).length < 2 ^ (prefixWord ++ tailWord_466266).sum := by decide
  have hdescent : baseEnd_466266 < baseStart_466266 := by decide
  rcases family_descends (prefixWord ++ tailWord_466266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466273 : List Nat := [1, 2, 3, 1, 1, 1, 1, 10]
def baseStart_466273 : Nat := 118140960795 + 466273 * 2 ^ 59
def prefixEnd_466273 : Nat := 4983230072969 + 3 ^ 40 * 466273 * 2
def baseEnd_466273 : Nat := 70939900804136129909083

theorem tailTrace_466273 : CollatzResearch.WordTrace tailWord_466273 prefixEnd_466273 70939900804136129909083 := by
  unfold tailWord_466273
  simp only [CollatzResearch.WordTrace]
  refine ⟨17006373439780028933595473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11337582293186685955730315 17006373439780028933595473)
  ·
    refine ⟨12754780079835021700196605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17006373439780028933595473 12754780079835021700196605)
    ·
      refine ⟨4783042529938133137573727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12754780079835021700196605 4783042529938133137573727)
      ·
        refine ⟨7174563794907199706360591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4783042529938133137573727 7174563794907199706360591)
        ·
          refine ⟨10761845692360799559540887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7174563794907199706360591 10761845692360799559540887)
          ·
            refine ⟨16142768538541199339311331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10761845692360799559540887 16142768538541199339311331)
            ·
              refine ⟨24214152807811799008966997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16142768538541199339311331 24214152807811799008966997)
              ·
                refine ⟨70939900804136129909083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24214152807811799008966997 70939900804136129909083)
                ·
                  rfl

theorem cell20_466273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_466273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466273 prefixEnd_466273 := by exact prefixLift 466273
  have htrace : WordTrace (prefixWord ++ tailWord_466273) baseStart_466273 baseEnd_466273 := by
    simpa [prefixWord, tailWord_466273, baseEnd_466273] using wordTrace_append hprefix tailTrace_466273
  have hstable : (prefixWord ++ tailWord_466273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466273).length < 2 ^ (prefixWord ++ tailWord_466273).sum := by decide
  have hdescent : baseEnd_466273 < baseStart_466273 := by decide
  rcases family_descends (prefixWord ++ tailWord_466273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466279 : List Nat := [1, 1, 5, 1, 4, 1, 2, 3, 2]
def baseStart_466279 : Nat := 118140960795 + 466279 * 2 ^ 59
def prefixEnd_466279 : Nat := 4983230072969 + 3 ^ 40 * 466279 * 2
def baseEnd_466279 : Nat := 212822440975899035527225

theorem tailTrace_466279 : CollatzResearch.WordTrace tailWord_466279 prefixEnd_466279 212822440975899035527225 := by
  unfold tailWord_466279
  simp only [CollatzResearch.WordTrace]
  refine ⟨17006592277758291958313891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11337728185172194638875927 17006592277758291958313891)
  ·
    refine ⟨25509888416637437937470837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17006592277758291958313891 25509888416637437937470837)
    ·
      refine ⟨2391552039059759806637891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25509888416637437937470837 2391552039059759806637891)
      ·
        refine ⟨3587328058589639709956837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391552039059759806637891 3587328058589639709956837)
        ·
          refine ⟨672624010985557445616907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3587328058589639709956837 672624010985557445616907)
          ·
            refine ⟨1008936016478336168425361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672624010985557445616907 1008936016478336168425361)
            ·
              refine ⟨756702012358752126319021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008936016478336168425361 756702012358752126319021)
              ·
                refine ⟨283763254634532047369633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 756702012358752126319021 283763254634532047369633)
                ·
                  refine ⟨212822440975899035527225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283763254634532047369633 212822440975899035527225)
                  ·
                    rfl

theorem cell20_466279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 2].length) (baseStart_466279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466279 prefixEnd_466279 := by exact prefixLift 466279
  have htrace : WordTrace (prefixWord ++ tailWord_466279) baseStart_466279 baseEnd_466279 := by
    simpa [prefixWord, tailWord_466279, baseEnd_466279] using wordTrace_append hprefix tailTrace_466279
  have hstable : (prefixWord ++ tailWord_466279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466279).length < 2 ^ (prefixWord ++ tailWord_466279).sum := by decide
  have hdescent : baseEnd_466279 < baseStart_466279 := by decide
  rcases family_descends (prefixWord ++ tailWord_466279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466324 : List Nat := [2, 4, 2, 1, 2, 3, 2, 4]
def baseStart_466324 : Nat := 118140960795 + 466324 * 2 ^ 59
def prefixEnd_466324 : Nat := 4983230072969 + 3 ^ 40 * 466324 * 2
def baseEnd_466324 : Nat := 70947660067359626342347

theorem tailTrace_466324 : CollatzResearch.WordTrace tailWord_466324 prefixEnd_466324 70947660067359626342347 := by
  unfold tailWord_466324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504116781297632321851013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11338822375063509762468017 8504116781297632321851013)
  ·
    refine ⟨1594521896493306060347065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8504116781297632321851013 1594521896493306060347065)
    ·
      refine ⟨1195891422369979545260299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1594521896493306060347065 1195891422369979545260299)
      ·
        refine ⟨1793837133554969317890449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195891422369979545260299 1793837133554969317890449)
        ·
          refine ⟨1345377850166226988417837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1793837133554969317890449 1345377850166226988417837)
          ·
            refine ⟨504516693812335120656689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1345377850166226988417837 504516693812335120656689)
            ·
              refine ⟨378387520359251340492517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504516693812335120656689 378387520359251340492517)
              ·
                refine ⟨70947660067359626342347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378387520359251340492517 70947660067359626342347)
                ·
                  rfl

theorem cell20_466324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_466324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466324 prefixEnd_466324 := by exact prefixLift 466324
  have htrace : WordTrace (prefixWord ++ tailWord_466324) baseStart_466324 baseEnd_466324 := by
    simpa [prefixWord, tailWord_466324, baseEnd_466324] using wordTrace_append hprefix tailTrace_466324
  have hstable : (prefixWord ++ tailWord_466324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466324).length < 2 ^ (prefixWord ++ tailWord_466324).sum := by decide
  have hdescent : baseEnd_466324 < baseStart_466324 := by decide
  rcases family_descends (prefixWord ++ tailWord_466324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466335 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 5]
def baseStart_466335 : Nat := 118140960795 + 466335 * 2 ^ 59
def prefixEnd_466335 : Nat := 4983230072969 + 3 ^ 40 * 466335 * 2
def baseEnd_466335 : Nat := 212848000901811729660329

theorem tailTrace_466335 : CollatzResearch.WordTrace tailWord_466335 prefixEnd_466335 212848000901811729660329 := by
  unfold tailWord_466335
  simp only [CollatzResearch.WordTrace]
  refine ⟨17008634765555413522352459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11339089843703609014901639 17008634765555413522352459)
  ·
    refine ⟨25512952148333120283528689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17008634765555413522352459 25512952148333120283528689)
    ·
      refine ⟨19134714111249840212646517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25512952148333120283528689 19134714111249840212646517)
      ·
        refine ⟨1793879447929672519935611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19134714111249840212646517 1793879447929672519935611)
        ·
          refine ⟨2690819171894508779903417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793879447929672519935611 2690819171894508779903417)
          ·
            refine ⟨2018114378920881584927563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2690819171894508779903417 2018114378920881584927563)
            ·
              refine ⟨3027171568381322377391345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018114378920881584927563 3027171568381322377391345)
              ·
                refine ⟨2270378676285991783043509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3027171568381322377391345 2270378676285991783043509)
                ·
                  refine ⟨212848000901811729660329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2270378676285991783043509 212848000901811729660329)
                  ·
                    rfl

theorem cell20_466335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_466335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466335 prefixEnd_466335 := by exact prefixLift 466335
  have htrace : WordTrace (prefixWord ++ tailWord_466335) baseStart_466335 baseEnd_466335 := by
    simpa [prefixWord, tailWord_466335, baseEnd_466335] using wordTrace_append hprefix tailTrace_466335
  have hstable : (prefixWord ++ tailWord_466335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466335).length < 2 ^ (prefixWord ++ tailWord_466335).sum := by decide
  have hdescent : baseEnd_466335 < baseStart_466335 := by decide
  rcases family_descends (prefixWord ++ tailWord_466335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466410 : List Nat := [3, 1, 3, 1, 4, 2, 2, 2, 2]
def baseStart_466410 : Nat := 118140960795 + 466410 * 2 ^ 59
def prefixEnd_466410 : Nat := 4983230072969 + 3 ^ 40 * 466410 * 2
def baseEnd_466410 : Nat := 212882232945444802160023

theorem tailTrace_466410 : CollatzResearch.WordTrace tailWord_466410 prefixEnd_466410 212882232945444802160023 := by
  unfold tailWord_466410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4252842560070925332833171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11340913493522467554221789 4252842560070925332833171)
  ·
    refine ⟨6379263840106387999249757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4252842560070925332833171 6379263840106387999249757)
    ·
      refine ⟨2392223940039895499718659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6379263840106387999249757 2392223940039895499718659)
      ·
        refine ⟨3588335910059843249577989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392223940039895499718659 3588335910059843249577989)
        ·
          refine ⟨672812983136220609295873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3588335910059843249577989 672812983136220609295873)
          ·
            refine ⟨504609737352165456971905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672812983136220609295873 504609737352165456971905)
            ·
              refine ⟨378457303014124092728929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504609737352165456971905 378457303014124092728929)
              ·
                refine ⟨283842977260593069546697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378457303014124092728929 283842977260593069546697)
                ·
                  refine ⟨212882232945444802160023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283842977260593069546697 212882232945444802160023)
                  ·
                    rfl

theorem cell20_466410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_466410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466410 prefixEnd_466410 := by exact prefixLift 466410
  have htrace : WordTrace (prefixWord ++ tailWord_466410) baseStart_466410 baseEnd_466410 := by
    simpa [prefixWord, tailWord_466410, baseEnd_466410] using wordTrace_append hprefix tailTrace_466410
  have hstable : (prefixWord ++ tailWord_466410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466410).length < 2 ^ (prefixWord ++ tailWord_466410).sum := by decide
  have hdescent : baseEnd_466410 < baseStart_466410 := by decide
  rcases family_descends (prefixWord ++ tailWord_466410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466414 : List Nat := [4, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_466414 : Nat := 118140960795 + 466414 * 2 ^ 59
def prefixEnd_466414 : Nat := 4983230072969 + 3 ^ 40 * 466414 * 2
def baseEnd_466414 : Nat := 212884058654438566026673

theorem tailTrace_466414 : CollatzResearch.WordTrace tailWord_466414 prefixEnd_466414 212884058654438566026673 := by
  unfold tailWord_466414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2126439516533651251809787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11341010754846140009652197 2126439516533651251809787)
  ·
    refine ⟨3189659274800476877714681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2126439516533651251809787 3189659274800476877714681)
    ·
      refine ⟨2392244456100357658286011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3189659274800476877714681 2392244456100357658286011)
      ·
        refine ⟨3588366684150536487429017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392244456100357658286011 3588366684150536487429017)
        ·
          refine ⟨2691275013112902365571763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3588366684150536487429017 2691275013112902365571763)
          ·
            refine ⟨4036912519669353548357645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691275013112902365571763 4036912519669353548357645)
            ·
              refine ⟨1513842194876007580634117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4036912519669353548357645 1513842194876007580634117)
              ·
                refine ⟨283845411539251421368897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1513842194876007580634117 283845411539251421368897)
                ·
                  refine ⟨212884058654438566026673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283845411539251421368897 212884058654438566026673)
                  ·
                    rfl

theorem cell20_466414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_466414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466414 prefixEnd_466414 := by exact prefixLift 466414
  have htrace : WordTrace (prefixWord ++ tailWord_466414) baseStart_466414 baseEnd_466414 := by
    simpa [prefixWord, tailWord_466414, baseEnd_466414] using wordTrace_append hprefix tailTrace_466414
  have hstable : (prefixWord ++ tailWord_466414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466414).length < 2 ^ (prefixWord ++ tailWord_466414).sum := by decide
  have hdescent : baseEnd_466414 < baseStart_466414 := by decide
  rcases family_descends (prefixWord ++ tailWord_466414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466421 : List Nat := [1, 3, 5, 1, 1, 1, 3, 5]
def baseStart_466421 : Nat := 118140960795 + 466421 * 2 ^ 59
def prefixEnd_466421 : Nat := 4983230072969 + 3 ^ 40 * 466421 * 2
def baseEnd_466421 : Nat := 70962417881725884264437

theorem tailTrace_466421 : CollatzResearch.WordTrace tailWord_466421 prefixEnd_466421 70962417881725884264437 := by
  unfold tailWord_466421
  simp only [CollatzResearch.WordTrace]
  refine ⟨17011771443243850209983117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11341180962162566806655411 17011771443243850209983117)
  ·
    refine ⟨6379414291216443828743669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17011771443243850209983117 6379414291216443828743669)
    ·
      refine ⟨598070089801541608944719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6379414291216443828743669 598070089801541608944719)
      ·
        refine ⟨897105134702312413417079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598070089801541608944719 897105134702312413417079)
        ·
          refine ⟨1345657702053468620125619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897105134702312413417079 1345657702053468620125619)
          ·
            refine ⟨2018486553080202930188429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345657702053468620125619 2018486553080202930188429)
            ·
              refine ⟨756932457405076098820661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2018486553080202930188429 756932457405076098820661)
              ·
                refine ⟨70962417881725884264437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 756932457405076098820661 70962417881725884264437)
                ·
                  rfl

theorem cell20_466421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 5].length) (baseStart_466421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466421 prefixEnd_466421 := by exact prefixLift 466421
  have htrace : WordTrace (prefixWord ++ tailWord_466421) baseStart_466421 baseEnd_466421 := by
    simpa [prefixWord, tailWord_466421, baseEnd_466421] using wordTrace_append hprefix tailTrace_466421
  have hstable : (prefixWord ++ tailWord_466421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466421).length < 2 ^ (prefixWord ++ tailWord_466421).sum := by decide
  have hdescent : baseEnd_466421 < baseStart_466421 := by decide
  rcases family_descends (prefixWord ++ tailWord_466421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466466 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_466466 : Nat := 118140960795 + 466466 * 2 ^ 59
def prefixEnd_466466 : Nat := 4983230072969 + 3 ^ 40 * 466466 * 2
def baseEnd_466466 : Nat := 212907792871357496293127

theorem tailTrace_466466 : CollatzResearch.WordTrace tailWord_466466 prefixEnd_466466 212907792871357496293127 := by
  unfold tailWord_466466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253353182020205723842813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11342275152053881930247501 4253353182020205723842813)
  ·
    refine ⟨1595007443257577146441055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4253353182020205723842813 1595007443257577146441055)
    ·
      refine ⟨2392511164886365719661583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1595007443257577146441055 2392511164886365719661583)
      ·
        refine ⟨3588766747329548579492375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392511164886365719661583 3588766747329548579492375)
        ·
          refine ⟨5383150120994322869238563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588766747329548579492375 5383150120994322869238563)
          ·
            refine ⟨8074725181491484303857845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5383150120994322869238563 8074725181491484303857845)
            ·
              refine ⟨757005485764826653486673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8074725181491484303857845 757005485764826653486673)
              ·
                refine ⟨567754114323619990115005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757005485764826653486673 567754114323619990115005)
                ·
                  refine ⟨212907792871357496293127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567754114323619990115005 212907792871357496293127)
                  ·
                    rfl

theorem cell20_466466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_466466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466466 prefixEnd_466466 := by exact prefixLift 466466
  have htrace : WordTrace (prefixWord ++ tailWord_466466) baseStart_466466 baseEnd_466466 := by
    simpa [prefixWord, tailWord_466466, baseEnd_466466] using wordTrace_append hprefix tailTrace_466466
  have hstable : (prefixWord ++ tailWord_466466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466466).length < 2 ^ (prefixWord ++ tailWord_466466).sum := by decide
  have hdescent : baseEnd_466466 < baseStart_466466 := by decide
  rcases family_descends (prefixWord ++ tailWord_466466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466501 : List Nat := [1, 3, 1, 1, 1, 4, 3, 6]
def baseStart_466501 : Nat := 118140960795 + 466501 * 2 ^ 59
def prefixEnd_466501 : Nat := 4983230072969 + 3 ^ 40 * 466501 * 2
def baseEnd_466501 : Nat := 70974589275017643375439

theorem tailTrace_466501 : CollatzResearch.WordTrace tailWord_466501 prefixEnd_466501 70974589275017643375439 := by
  unfold tailWord_466501
  simp only [CollatzResearch.WordTrace]
  refine ⟨17014689282954023872895357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11343126188636015915263571 17014689282954023872895357)
  ·
    refine ⟨6380508481107758952335759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17014689282954023872895357 6380508481107758952335759)
    ·
      refine ⟨9570762721661638428503639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6380508481107758952335759 9570762721661638428503639)
      ·
        refine ⟨14356144082492457642755459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9570762721661638428503639 14356144082492457642755459)
        ·
          refine ⟨21534216123738686464133189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14356144082492457642755459 21534216123738686464133189)
          ·
            refine ⟨4037665523201003712024973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21534216123738686464133189 4037665523201003712024973)
            ·
              refine ⟨1514124571200376392009365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4037665523201003712024973 1514124571200376392009365)
              ·
                refine ⟨70974589275017643375439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1514124571200376392009365 70974589275017643375439)
                ·
                  rfl

theorem cell20_466501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_466501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466501 prefixEnd_466501 := by exact prefixLift 466501
  have htrace : WordTrace (prefixWord ++ tailWord_466501) baseStart_466501 baseEnd_466501 := by
    simpa [prefixWord, tailWord_466501, baseEnd_466501] using wordTrace_append hprefix tailTrace_466501
  have hstable : (prefixWord ++ tailWord_466501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466501).length < 2 ^ (prefixWord ++ tailWord_466501).sum := by decide
  have hdescent : baseEnd_466501 < baseStart_466501 := by decide
  rcases family_descends (prefixWord ++ tailWord_466501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466583 : List Nat := [1, 1, 3, 3, 2, 4, 2, 2, 2]
def baseStart_466583 : Nat := 118140960795 + 466583 * 2 ^ 59
def prefixEnd_466583 : Nat := 4983230072969 + 3 ^ 40 * 466583 * 2
def baseEnd_466583 : Nat := 212961194859425089392649

theorem tailTrace_466583 : CollatzResearch.WordTrace tailWord_466583 prefixEnd_466583 212961194859425089392649 := by
  unfold tailWord_466583
  simp only [CollatzResearch.WordTrace]
  refine ⟨17017680068656951877380403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11345120045771301251586935 17017680068656951877380403)
  ·
    refine ⟨25526520102985427816070605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17017680068656951877380403 25526520102985427816070605)
    ·
      refine ⟨9572445038619535431026477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25526520102985427816070605 9572445038619535431026477)
      ·
        refine ⟨3589666889482325786634929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9572445038619535431026477 3589666889482325786634929)
        ·
          refine ⟨2692250167111744339976197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3589666889482325786634929 2692250167111744339976197)
          ·
            refine ⟨504796906333452063745537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2692250167111744339976197 504796906333452063745537)
            ·
              refine ⟨378597679750089047809153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504796906333452063745537 378597679750089047809153)
              ·
                refine ⟨283948259812566785856865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378597679750089047809153 283948259812566785856865)
                ·
                  refine ⟨212961194859425089392649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283948259812566785856865 212961194859425089392649)
                  ·
                    rfl

theorem cell20_466583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 2].length) (baseStart_466583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466583 prefixEnd_466583 := by exact prefixLift 466583
  have htrace : WordTrace (prefixWord ++ tailWord_466583) baseStart_466583 baseEnd_466583 := by
    simpa [prefixWord, tailWord_466583, baseEnd_466583] using wordTrace_append hprefix tailTrace_466583
  have hstable : (prefixWord ++ tailWord_466583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466583).length < 2 ^ (prefixWord ++ tailWord_466583).sum := by decide
  have hdescent : baseEnd_466583 < baseStart_466583 := by decide
  rcases family_descends (prefixWord ++ tailWord_466583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466642 : List Nat := [3, 2, 2, 2, 2, 1, 2, 4, 2]
def baseStart_466642 : Nat := 118140960795 + 466642 * 2 ^ 59
def prefixEnd_466642 : Nat := 4983230072969 + 3 ^ 40 * 466642 * 2
def baseEnd_466642 : Nat := 212988124067083106425741

theorem tailTrace_466642 : CollatzResearch.WordTrace tailWord_466642 prefixEnd_466642 212988124067083106425741 := by
  unfold tailWord_466642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4254957993860801238444545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11346554650295469969185453 4254957993860801238444545)
  ·
    refine ⟨3191218495395600928833409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4254957993860801238444545 3191218495395600928833409)
    ·
      refine ⟨2393413871546700696625057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3191218495395600928833409 2393413871546700696625057)
      ·
        refine ⟨1795060403660025522468793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2393413871546700696625057 1795060403660025522468793)
        ·
          refine ⟨1346295302745019141851595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1795060403660025522468793 1346295302745019141851595)
          ·
            refine ⟨2019442954117528712777393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346295302745019141851595 2019442954117528712777393)
            ·
              refine ⟨1514582215588146534583045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019442954117528712777393 1514582215588146534583045)
              ·
                refine ⟨283984165422777475234321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1514582215588146534583045 283984165422777475234321)
                ·
                  refine ⟨212988124067083106425741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283984165422777475234321 212988124067083106425741)
                  ·
                    rfl

theorem cell20_466642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_466642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466642 prefixEnd_466642 := by exact prefixLift 466642
  have htrace : WordTrace (prefixWord ++ tailWord_466642) baseStart_466642 baseEnd_466642 := by
    simpa [prefixWord, tailWord_466642, baseEnd_466642] using wordTrace_append hprefix tailTrace_466642
  have hstable : (prefixWord ++ tailWord_466642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466642).length < 2 ^ (prefixWord ++ tailWord_466642).sum := by decide
  have hdescent : baseEnd_466642 < baseStart_466642 := by decide
  rcases family_descends (prefixWord ++ tailWord_466642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466652 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 3]
def baseStart_466652 : Nat := 118140960795 + 466652 * 2 ^ 59
def prefixEnd_466652 : Nat := 4983230072969 + 3 ^ 40 * 466652 * 2
def baseEnd_466652 : Nat := 212992688339567516092367

theorem tailTrace_466652 : CollatzResearch.WordTrace tailWord_466652 prefixEnd_466652 212992688339567516092367 := by
  unfold tailWord_466652
  simp only [CollatzResearch.WordTrace]
  refine ⟨8510098352703488330821105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11346797803604651107761473 8510098352703488330821105)
  ·
    refine ⟨6382573764527616248115829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8510098352703488330821105 6382573764527616248115829)
    ·
      refine ⟨598366290424464023260859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6382573764527616248115829 598366290424464023260859)
      ·
        refine ⟨897549435636696034891289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598366290424464023260859 897549435636696034891289)
        ·
          refine ⟨673162076727522026168467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897549435636696034891289 673162076727522026168467)
          ·
            refine ⟨1009743115091283039252701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673162076727522026168467 1009743115091283039252701)
            ·
              refine ⟨378653668159231139719763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1009743115091283039252701 378653668159231139719763)
              ·
                refine ⟨567980502238846709579645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378653668159231139719763 567980502238846709579645)
                ·
                  refine ⟨212992688339567516092367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567980502238846709579645 212992688339567516092367)
                  ·
                    rfl

theorem cell20_466652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_466652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466652 prefixEnd_466652 := by exact prefixLift 466652
  have htrace : WordTrace (prefixWord ++ tailWord_466652) baseStart_466652 baseEnd_466652 := by
    simpa [prefixWord, tailWord_466652, baseEnd_466652] using wordTrace_append hprefix tailTrace_466652
  have hstable : (prefixWord ++ tailWord_466652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466652).length < 2 ^ (prefixWord ++ tailWord_466652).sum := by decide
  have hdescent : baseEnd_466652 < baseStart_466652 := by decide
  rcases family_descends (prefixWord ++ tailWord_466652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466676 : List Nat := [2, 6, 1, 1, 1, 1, 3, 3, 2]
def baseStart_466676 : Nat := 118140960795 + 466676 * 2 ^ 59
def prefixEnd_466676 : Nat := 4983230072969 + 3 ^ 40 * 466676 * 2
def baseEnd_466676 : Nat := 213003642593530099292269

theorem tailTrace_466676 : CollatzResearch.WordTrace tailWord_466676 prefixEnd_466676 213003642593530099292269 := by
  unfold tailWord_466676
  simp only [CollatzResearch.WordTrace]
  refine ⟨8510536028660014380257941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11347381371546685840343921 8510536028660014380257941)
  ·
    refine ⟨398931376343438174074591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8510536028660014380257941 398931376343438174074591)
    ·
      refine ⟨598397064515157261111887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398931376343438174074591 598397064515157261111887)
      ·
        refine ⟨897595596772735891667831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598397064515157261111887 897595596772735891667831)
        ·
          refine ⟨1346393395159103837501747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897595596772735891667831 1346393395159103837501747)
          ·
            refine ⟨2019590092738655756252621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346393395159103837501747 2019590092738655756252621)
            ·
              refine ⟨757346284776995908594733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2019590092738655756252621 757346284776995908594733)
              ·
                refine ⟨284004856791373465723025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 757346284776995908594733 284004856791373465723025)
                ·
                  refine ⟨213003642593530099292269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284004856791373465723025 213003642593530099292269)
                  ·
                    rfl

theorem cell20_466676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_466676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466676 prefixEnd_466676 := by exact prefixLift 466676
  have htrace : WordTrace (prefixWord ++ tailWord_466676) baseStart_466676 baseEnd_466676 := by
    simpa [prefixWord, tailWord_466676, baseEnd_466676] using wordTrace_append hprefix tailTrace_466676
  have hstable : (prefixWord ++ tailWord_466676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466676).length < 2 ^ (prefixWord ++ tailWord_466676).sum := by decide
  have hdescent : baseEnd_466676 < baseStart_466676 := by decide
  rcases family_descends (prefixWord ++ tailWord_466676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466711 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 3]
def baseStart_466711 : Nat := 118140960795 + 466711 * 2 ^ 59
def prefixEnd_466711 : Nat := 4983230072969 + 3 ^ 40 * 466711 * 2
def baseEnd_466711 : Nat := 213019617547225533125459

theorem tailTrace_466711 : CollatzResearch.WordTrace tailWord_466711 prefixEnd_466711 213019617547225533125459 := by
  unfold tailWord_466711
  simp only [CollatzResearch.WordTrace]
  refine ⟨17022348612193229738039987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11348232408128819825359991 17022348612193229738039987)
  ·
    refine ⟨25533522918289844607059981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17022348612193229738039987 25533522918289844607059981)
    ·
      refine ⟨9575071094358691727647493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25533522918289844607059981 9575071094358691727647493)
      ·
        refine ⟨1795325830192254698933905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9575071094358691727647493 1795325830192254698933905)
        ·
          refine ⟨1346494372644191024200429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1795325830192254698933905 1346494372644191024200429)
          ·
            refine ⟨504935389741571634075161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1346494372644191024200429 504935389741571634075161)
            ·
              refine ⟨378701542306178725556371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504935389741571634075161 378701542306178725556371)
              ·
                refine ⟨568052313459268088334557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378701542306178725556371 568052313459268088334557)
                ·
                  refine ⟨213019617547225533125459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568052313459268088334557 213019617547225533125459)
                  ·
                    rfl

theorem cell20_466711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 3].length) (baseStart_466711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466711 prefixEnd_466711 := by exact prefixLift 466711
  have htrace : WordTrace (prefixWord ++ tailWord_466711) baseStart_466711 baseEnd_466711 := by
    simpa [prefixWord, tailWord_466711, baseEnd_466711] using wordTrace_append hprefix tailTrace_466711
  have hstable : (prefixWord ++ tailWord_466711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466711).length < 2 ^ (prefixWord ++ tailWord_466711).sum := by decide
  have hdescent : baseEnd_466711 < baseStart_466711 := by decide
  rcases family_descends (prefixWord ++ tailWord_466711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466722 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_466722 : Nat := 118140960795 + 466722 * 2 ^ 59
def prefixEnd_466722 : Nat := 4983230072969 + 3 ^ 40 * 466722 * 2
def baseEnd_466722 : Nat := 213024638246958383758747

theorem tailTrace_466722 : CollatzResearch.WordTrace tailWord_466722 prefixEnd_466722 213024638246958383758747 := by
  unfold tailWord_466722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255687453788344654172605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11348499876768919077793613 4255687453788344654172605)
  ·
    refine ⟨1595882795170629245314727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4255687453788344654172605 1595882795170629245314727)
    ·
      refine ⟨2393824192755943867972091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1595882795170629245314727 2393824192755943867972091)
      ·
        refine ⟨3590736289133915801958137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2393824192755943867972091 3590736289133915801958137)
        ·
          refine ⟨2693052216850436851468603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3590736289133915801958137 2693052216850436851468603)
          ·
            refine ⟨4039578325275655277202905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693052216850436851468603 4039578325275655277202905)
            ·
              refine ⟨3029683743956741457902179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4039578325275655277202905 3029683743956741457902179)
              ·
                refine ⟨4544525615935112186853269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029683743956741457902179 4544525615935112186853269)
                ·
                  refine ⟨213024638246958383758747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4544525615935112186853269 213024638246958383758747)
                  ·
                    rfl

theorem cell20_466722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_466722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466722 prefixEnd_466722 := by exact prefixLift 466722
  have htrace : WordTrace (prefixWord ++ tailWord_466722) baseStart_466722 baseEnd_466722 := by
    simpa [prefixWord, tailWord_466722, baseEnd_466722] using wordTrace_append hprefix tailTrace_466722
  have hstable : (prefixWord ++ tailWord_466722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466722).length < 2 ^ (prefixWord ++ tailWord_466722).sum := by decide
  have hdescent : baseEnd_466722 < baseStart_466722 := by decide
  rcases family_descends (prefixWord ++ tailWord_466722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466743 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_466743 : Nat := 118140960795 + 466743 * 2 ^ 59
def prefixEnd_466743 : Nat := 4983230072969 + 3 ^ 40 * 466743 * 2
def baseEnd_466743 : Nat := 213034223219175644058661

theorem tailTrace_466743 : CollatzResearch.WordTrace tailWord_466743 prefixEnd_466743 213034223219175644058661 := by
  unfold tailWord_466743
  simp only [CollatzResearch.WordTrace]
  refine ⟨17023515748077299203204883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11349010498718199468803255 17023515748077299203204883)
  ·
    refine ⟨25535273622115948804807325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17023515748077299203204883 25535273622115948804807325)
    ·
      refine ⟨9575727608293480801802747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25535273622115948804807325 9575727608293480801802747)
      ·
        refine ⟨14363591412440221202704121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9575727608293480801802747 14363591412440221202704121)
        ·
          refine ⟨10772693559330165902028091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14363591412440221202704121 10772693559330165902028091)
          ·
            refine ⟨16159040338995248853042137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10772693559330165902028091 16159040338995248853042137)
            ·
              refine ⟨12119280254246436639781603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16159040338995248853042137 12119280254246436639781603)
              ·
                refine ⟨18178920381369654959672405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12119280254246436639781603 18178920381369654959672405)
                ·
                  refine ⟨213034223219175644058661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18178920381369654959672405 213034223219175644058661)
                  ·
                    rfl

theorem cell20_466743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_466743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466743 prefixEnd_466743 := by exact prefixLift 466743
  have htrace : WordTrace (prefixWord ++ tailWord_466743) baseStart_466743 baseEnd_466743 := by
    simpa [prefixWord, tailWord_466743, baseEnd_466743] using wordTrace_append hprefix tailTrace_466743
  have hstable : (prefixWord ++ tailWord_466743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466743).length < 2 ^ (prefixWord ++ tailWord_466743).sum := by decide
  have hdescent : baseEnd_466743 < baseStart_466743 := by decide
  rcases family_descends (prefixWord ++ tailWord_466743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466784 : List Nat := [2, 1, 1, 3, 3, 3, 3, 4]
def baseStart_466784 : Nat := 118140960795 + 466784 * 2 ^ 59
def prefixEnd_466784 : Nat := 4983230072969 + 3 ^ 40 * 466784 * 2
def baseEnd_466784 : Nat := 71017645578787241230609

theorem tailTrace_466784 : CollatzResearch.WordTrace tailWord_466784 prefixEnd_466784 71017645578787241230609 := by
  unfold tailWord_466784
  simp only [CollatzResearch.WordTrace]
  refine ⟨8512505570464381602723703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11350007427285842136964937 8512505570464381602723703)
  ·
    refine ⟨12768758355696572404085555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8512505570464381602723703 12768758355696572404085555)
    ·
      refine ⟨19153137533544858606128333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12768758355696572404085555 19153137533544858606128333)
      ·
        refine ⟨7182426575079321977298125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19153137533544858606128333 7182426575079321977298125)
        ·
          refine ⟨2693409965654745741486797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7182426575079321977298125 2693409965654745741486797)
          ·
            refine ⟨1010028737120529653057549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2693409965654745741486797 1010028737120529653057549)
            ·
              refine ⟨378760776420198619896581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1010028737120529653057549 378760776420198619896581)
              ·
                refine ⟨71017645578787241230609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378760776420198619896581 71017645578787241230609)
                ·
                  rfl

theorem cell20_466784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_466784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466784 prefixEnd_466784 := by exact prefixLift 466784
  have htrace : WordTrace (prefixWord ++ tailWord_466784) baseStart_466784 baseEnd_466784 := by
    simpa [prefixWord, tailWord_466784, baseEnd_466784] using wordTrace_append hprefix tailTrace_466784
  have hstable : (prefixWord ++ tailWord_466784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466784).length < 2 ^ (prefixWord ++ tailWord_466784).sum := by decide
  have hdescent : baseEnd_466784 < baseStart_466784 := by decide
  rcases family_descends (prefixWord ++ tailWord_466784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466805 : List Nat := [1, 3, 4, 1, 1, 1, 9]
def baseStart_466805 : Nat := 118140960795 + 466805 * 2 ^ 59
def prefixEnd_466805 : Nat := 4983230072969 + 3 ^ 40 * 466805 * 2
def baseEnd_466805 : Nat := 23673613523175442665749

theorem tailTrace_466805 : CollatzResearch.WordTrace tailWord_466805 prefixEnd_466805 23673613523175442665749 := by
  unfold tailWord_466805
  simp only [CollatzResearch.WordTrace]
  refine ⟨17025777073852683791961869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11350518049235122527974579 17025777073852683791961869)
  ·
    refine ⟨6384666402694756421985701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17025777073852683791961869 6384666402694756421985701)
    ·
      refine ⟨1197124950505266829122319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6384666402694756421985701 1197124950505266829122319)
      ·
        refine ⟨1795687425757900243683479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197124950505266829122319 1795687425757900243683479)
        ·
          refine ⟨2693531138636850365525219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795687425757900243683479 2693531138636850365525219)
          ·
            refine ⟨4040296707955275548287829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693531138636850365525219 4040296707955275548287829)
            ·
              refine ⟨23673613523175442665749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4040296707955275548287829 23673613523175442665749)
              ·
                rfl

theorem cell20_466805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 9].length) (baseStart_466805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466805 prefixEnd_466805 := by exact prefixLift 466805
  have htrace : WordTrace (prefixWord ++ tailWord_466805) baseStart_466805 baseEnd_466805 := by
    simpa [prefixWord, tailWord_466805, baseEnd_466805] using wordTrace_append hprefix tailTrace_466805
  have hstable : (prefixWord ++ tailWord_466805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466805).length < 2 ^ (prefixWord ++ tailWord_466805).sum := by decide
  have hdescent : baseEnd_466805 < baseStart_466805 := by decide
  rcases family_descends (prefixWord ++ tailWord_466805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466849 : List Nat := [1, 2, 3, 4, 2, 2, 1, 3, 2]
def baseStart_466849 : Nat := 118140960795 + 466849 * 2 ^ 59
def prefixEnd_466849 : Nat := 4983230072969 + 3 ^ 40 * 466849 * 2
def baseEnd_466849 : Nat := 213082604507510386524895

theorem tailTrace_466849 : CollatzResearch.WordTrace tailWord_466849 prefixEnd_466849 213082604507510386524895 := by
  unfold tailWord_466849
  simp only [CollatzResearch.WordTrace]
  refine ⟨17027381885693279306563601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11351587923795519537709067 17027381885693279306563601)
  ·
    refine ⟨12770536414269959479922701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17027381885693279306563601 12770536414269959479922701)
    ·
      refine ⟨4788951155351234804971013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12770536414269959479922701 4788951155351234804971013)
      ·
        refine ⟨897928341628356525932065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4788951155351234804971013 897928341628356525932065)
        ·
          refine ⟨673446256221267394449049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897928341628356525932065 673446256221267394449049)
          ·
            refine ⟨505084692165950545836787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673446256221267394449049 505084692165950545836787)
            ·
              refine ⟨757627038248925818755181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505084692165950545836787 757627038248925818755181)
              ·
                refine ⟨284110139343347182033193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 757627038248925818755181 284110139343347182033193)
                ·
                  refine ⟨213082604507510386524895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284110139343347182033193 213082604507510386524895)
                  ·
                    rfl

theorem cell20_466849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 2].length) (baseStart_466849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466849 prefixEnd_466849 := by exact prefixLift 466849
  have htrace : WordTrace (prefixWord ++ tailWord_466849) baseStart_466849 baseEnd_466849 := by
    simpa [prefixWord, tailWord_466849, baseEnd_466849] using wordTrace_append hprefix tailTrace_466849
  have hstable : (prefixWord ++ tailWord_466849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466849).length < 2 ^ (prefixWord ++ tailWord_466849).sum := by decide
  have hdescent : baseEnd_466849 < baseStart_466849 := by decide
  rcases family_descends (prefixWord ++ tailWord_466849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466856 : List Nat := [2, 1, 6, 2, 2, 1, 6]
def baseStart_466856 : Nat := 118140960795 + 466856 * 2 ^ 59
def prefixEnd_466856 : Nat := 4983230072969 + 3 ^ 40 * 466856 * 2
def baseEnd_466856 : Nat := 23676199944249941476837

theorem tailTrace_466856 : CollatzResearch.WordTrace tailWord_466856 prefixEnd_466856 23676199944249941476837 := by
  unfold tailWord_466856
  simp only [CollatzResearch.WordTrace]
  refine ⟨8513818598333959751034211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11351758131111946334712281 8513818598333959751034211)
  ·
    refine ⟨12770727897500939626551317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8513818598333959751034211 12770727897500939626551317)
    ·
      refine ⟨598627870195356544994593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12770727897500939626551317 598627870195356544994593)
      ·
        refine ⟨448970902646517408745945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598627870195356544994593 448970902646517408745945)
        ·
          refine ⟨336728176984888056559459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448970902646517408745945 336728176984888056559459)
          ·
            refine ⟨505092265477332084839189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336728176984888056559459 505092265477332084839189)
            ·
              refine ⟨23676199944249941476837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 505092265477332084839189 23676199944249941476837)
              ·
                rfl

theorem cell20_466856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 6].length) (baseStart_466856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466856 prefixEnd_466856 := by exact prefixLift 466856
  have htrace : WordTrace (prefixWord ++ tailWord_466856) baseStart_466856 baseEnd_466856 := by
    simpa [prefixWord, tailWord_466856, baseEnd_466856] using wordTrace_append hprefix tailTrace_466856
  have hstable : (prefixWord ++ tailWord_466856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466856).length < 2 ^ (prefixWord ++ tailWord_466856).sum := by decide
  have hdescent : baseEnd_466856 < baseStart_466856 := by decide
  rcases family_descends (prefixWord ++ tailWord_466856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466895 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_466895 : Nat := 118140960795 + 466895 * 2 ^ 59
def prefixEnd_466895 : Nat := 4983230072969 + 3 ^ 40 * 466895 * 2
def baseEnd_466895 : Nat := 213103600160938670991373

theorem tailTrace_466895 : CollatzResearch.WordTrace tailWord_466895 prefixEnd_466895 213103600160938670991373 := by
  unfold tailWord_466895
  simp only [CollatzResearch.WordTrace]
  refine ⟨17029059643526629162738139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11352706429017752775158759 17029059643526629162738139)
  ·
    refine ⟨25543589465289943744107209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17029059643526629162738139 25543589465289943744107209)
    ·
      refine ⟨19157692098967457808080407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25543589465289943744107209 19157692098967457808080407)
      ·
        refine ⟨28736538148451186712120611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19157692098967457808080407 28736538148451186712120611)
        ·
          refine ⟨43104807222676780068180917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28736538148451186712120611 43104807222676780068180917)
          ·
            refine ⟨4041075677125948131391961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43104807222676780068180917 4041075677125948131391961)
            ·
              refine ⟨3030806757844461098543971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4041075677125948131391961 3030806757844461098543971)
              ·
                refine ⟨4546210136766691647815957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030806757844461098543971 4546210136766691647815957)
                ·
                  refine ⟨213103600160938670991373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4546210136766691647815957 213103600160938670991373)
                  ·
                    rfl

theorem cell20_466895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_466895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466895 prefixEnd_466895 := by exact prefixLift 466895
  have htrace : WordTrace (prefixWord ++ tailWord_466895) baseStart_466895 baseEnd_466895 := by
    simpa [prefixWord, tailWord_466895, baseEnd_466895] using wordTrace_append hprefix tailTrace_466895
  have hstable : (prefixWord ++ tailWord_466895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466895).length < 2 ^ (prefixWord ++ tailWord_466895).sum := by decide
  have hdescent : baseEnd_466895 < baseStart_466895 := by decide
  rcases family_descends (prefixWord ++ tailWord_466895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466919 : List Nat := [1, 1, 5, 2, 3, 8]
def baseStart_466919 : Nat := 118140960795 + 466919 * 2 ^ 59
def prefixEnd_466919 : Nat := 4983230072969 + 3 ^ 40 * 466919 * 2
def baseEnd_466919 : Nat := 7893131644996342747825

theorem tailTrace_466919 : CollatzResearch.WordTrace tailWord_466919 prefixEnd_466919 7893131644996342747825 := by
  unfold tailWord_466919
  simp only [CollatzResearch.WordTrace]
  refine ⟨17029934995439681261611811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11353289996959787507741207 17029934995439681261611811)
  ·
    refine ⟨25544902493159521892417717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17029934995439681261611811 25544902493159521892417717)
    ·
      refine ⟨2394834608733705177414161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25544902493159521892417717 2394834608733705177414161)
      ·
        refine ⟨1796125956550278883060621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2394834608733705177414161 1796125956550278883060621)
        ·
          refine ⟨673547233706354581147733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1796125956550278883060621 673547233706354581147733)
          ·
            refine ⟨7893131644996342747825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 673547233706354581147733 7893131644996342747825)
            ·
              rfl

theorem cell20_466919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 8].length) (baseStart_466919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466919 prefixEnd_466919 := by exact prefixLift 466919
  have htrace : WordTrace (prefixWord ++ tailWord_466919) baseStart_466919 baseEnd_466919 := by
    simpa [prefixWord, tailWord_466919, baseEnd_466919] using wordTrace_append hprefix tailTrace_466919
  have hstable : (prefixWord ++ tailWord_466919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466919).length < 2 ^ (prefixWord ++ tailWord_466919).sum := by decide
  have hdescent : baseEnd_466919 < baseStart_466919 := by decide
  rcases family_descends (prefixWord ++ tailWord_466919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466925 : List Nat := [1, 5, 1, 4, 1, 1, 1, 4, 2]
def baseStart_466925 : Nat := 118140960795 + 466925 * 2 ^ 59
def prefixEnd_466925 : Nat := 4983230072969 + 3 ^ 40 * 466925 * 2
def baseEnd_466925 : Nat := 213117292978391899991251

theorem tailTrace_466925 : CollatzResearch.WordTrace tailWord_466925 prefixEnd_466925 213117292978391899991251 := by
  unfold tailWord_466925
  simp only [CollatzResearch.WordTrace]
  refine ⟨17030153833417944286330229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11353435888945296190886819 17030153833417944286330229)
  ·
    refine ⟨1596576921882932276843459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17030153833417944286330229 1596576921882932276843459)
    ·
      refine ⟨2394865382824398415265189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1596576921882932276843459 2394865382824398415265189)
      ·
        refine ⟨449037259279574702862223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2394865382824398415265189 449037259279574702862223)
        ·
          refine ⟨673555888919362054293335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449037259279574702862223 673555888919362054293335)
          ·
            refine ⟨1010333833379043081440003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673555888919362054293335 1010333833379043081440003)
            ·
              refine ⟨1515500750068564622160005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010333833379043081440003 1515500750068564622160005)
              ·
                refine ⟨284156390637855866655001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1515500750068564622160005 284156390637855866655001)
                ·
                  refine ⟨213117292978391899991251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284156390637855866655001 213117292978391899991251)
                  ·
                    rfl

theorem cell20_466925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_466925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466925 prefixEnd_466925 := by exact prefixLift 466925
  have htrace : WordTrace (prefixWord ++ tailWord_466925) baseStart_466925 baseEnd_466925 := by
    simpa [prefixWord, tailWord_466925, baseEnd_466925] using wordTrace_append hprefix tailTrace_466925
  have hstable : (prefixWord ++ tailWord_466925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466925).length < 2 ^ (prefixWord ++ tailWord_466925).sum := by decide
  have hdescent : baseEnd_466925 < baseStart_466925 := by decide
  rcases family_descends (prefixWord ++ tailWord_466925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466977 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 3]
def baseStart_466977 : Nat := 118140960795 + 466977 * 2 ^ 59
def prefixEnd_466977 : Nat := 4983230072969 + 3 ^ 40 * 466977 * 2
def baseEnd_466977 : Nat := 213141027195310830257705

theorem tailTrace_466977 : CollatzResearch.WordTrace tailWord_466977 prefixEnd_466977 213141027195310830257705 := by
  unfold tailWord_466977
  simp only [CollatzResearch.WordTrace]
  refine ⟨17032050429229557167223185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11354700286153038111482123 17032050429229557167223185)
  ·
    refine ⟨12774037821922167875417389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17032050429229557167223185 12774037821922167875417389)
    ·
      refine ⟨4790264183220812953281521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12774037821922167875417389 4790264183220812953281521)
      ·
        refine ⟨3592698137415609714961141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4790264183220812953281521 3592698137415609714961141)
        ·
          refine ⟨336815450382713410777607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3592698137415609714961141 336815450382713410777607)
          ·
            refine ⟨505223175574070116166411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336815450382713410777607 505223175574070116166411)
            ·
              refine ⟨757834763361105174249617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505223175574070116166411 757834763361105174249617)
              ·
                refine ⟨568376072520828880687213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757834763361105174249617 568376072520828880687213)
                ·
                  refine ⟨213141027195310830257705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568376072520828880687213 213141027195310830257705)
                  ·
                    rfl

theorem cell20_466977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 3].length) (baseStart_466977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466977 prefixEnd_466977 := by exact prefixLift 466977
  have htrace : WordTrace (prefixWord ++ tailWord_466977) baseStart_466977 baseEnd_466977 := by
    simpa [prefixWord, tailWord_466977, baseEnd_466977] using wordTrace_append hprefix tailTrace_466977
  have hstable : (prefixWord ++ tailWord_466977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466977).length < 2 ^ (prefixWord ++ tailWord_466977).sum := by decide
  have hdescent : baseEnd_466977 < baseStart_466977 := by decide
  rcases family_descends (prefixWord ++ tailWord_466977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466981 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 3]
def baseStart_466981 : Nat := 118140960795 + 466981 * 2 ^ 59
def prefixEnd_466981 : Nat := 4983230072969 + 3 ^ 40 * 466981 * 2
def baseEnd_466981 : Nat := 213142852904304594124355

theorem tailTrace_466981 : CollatzResearch.WordTrace tailWord_466981 prefixEnd_466981 213142852904304594124355 := by
  unfold tailWord_466981
  simp only [CollatzResearch.WordTrace]
  refine ⟨17032196321215065850368797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11354797547476710566912531 17032196321215065850368797)
  ·
    refine ⟨6387073620455649693888299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17032196321215065850368797 6387073620455649693888299)
    ·
      refine ⟨9580610430683474540832449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6387073620455649693888299 9580610430683474540832449)
      ·
        refine ⟨7185457823012605905624337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9580610430683474540832449 7185457823012605905624337)
        ·
          refine ⟨5389093367259454429218253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7185457823012605905624337 5389093367259454429218253)
          ·
            refine ⟨2020910012722295410956845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5389093367259454429218253 2020910012722295410956845)
            ·
              refine ⟨757841254770860779108817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2020910012722295410956845 757841254770860779108817)
              ·
                refine ⟨568380941078145584331613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757841254770860779108817 568380941078145584331613)
                ·
                  refine ⟨213142852904304594124355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568380941078145584331613 213142852904304594124355)
                  ·
                    rfl

theorem cell20_466981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_466981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466981 prefixEnd_466981 := by exact prefixLift 466981
  have htrace : WordTrace (prefixWord ++ tailWord_466981) baseStart_466981 baseEnd_466981 := by
    simpa [prefixWord, tailWord_466981, baseEnd_466981] using wordTrace_append hprefix tailTrace_466981
  have hstable : (prefixWord ++ tailWord_466981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466981).length < 2 ^ (prefixWord ++ tailWord_466981).sum := by decide
  have hdescent : baseEnd_466981 < baseStart_466981 := by decide
  rcases family_descends (prefixWord ++ tailWord_466981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466984 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 4]
def baseStart_466984 : Nat := 118140960795 + 466984 * 2 ^ 59
def prefixEnd_466984 : Nat := 4983230072969 + 3 ^ 40 * 466984 * 2
def baseEnd_466984 : Nat := 213144222186049917024343

theorem tailTrace_466984 : CollatzResearch.WordTrace tailWord_466984 prefixEnd_466984 213144222186049917024343 := by
  unfold tailWord_466984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8516152870102098681364003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11354870493469464908485337 8516152870102098681364003)
  ·
    refine ⟨12774229305153148022046005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8516152870102098681364003 12774229305153148022046005)
    ·
      refine ⟨1197583997358107627066813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12774229305153148022046005 1197583997358107627066813)
      ·
        refine ⟨449093999009290360150055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1197583997358107627066813 449093999009290360150055)
        ·
          refine ⟨673640998513935540225083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449093999009290360150055 673640998513935540225083)
          ·
            refine ⟨1010461497770903310337625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673640998513935540225083 1010461497770903310337625)
            ·
              refine ⟨757846123328177482753219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010461497770903310337625 757846123328177482753219)
              ·
                refine ⟨1136769184992266224129829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 757846123328177482753219 1136769184992266224129829)
                ·
                  refine ⟨213144222186049917024343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1136769184992266224129829 213144222186049917024343)
                  ·
                    rfl

theorem cell20_466984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_466984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_466984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_466984 prefixEnd_466984 := by exact prefixLift 466984
  have htrace : WordTrace (prefixWord ++ tailWord_466984) baseStart_466984 baseEnd_466984 := by
    simpa [prefixWord, tailWord_466984, baseEnd_466984] using wordTrace_append hprefix tailTrace_466984
  have hstable : (prefixWord ++ tailWord_466984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466984).length < 2 ^ (prefixWord ++ tailWord_466984).sum := by decide
  have hdescent : baseEnd_466984 < baseStart_466984 := by decide
  rcases family_descends (prefixWord ++ tailWord_466984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467022 : List Nat := [4, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_467022 : Nat := 118140960795 + 467022 * 2 ^ 59
def prefixEnd_467022 : Nat := 4983230072969 + 3 ^ 40 * 467022 * 2
def baseEnd_467022 : Nat := 213161566421490673757521

theorem tailTrace_467022 : CollatzResearch.WordTrace tailWord_467022 prefixEnd_467022 213161566421490673757521 := by
  unfold tailWord_467022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2129211464258316231576415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11355794476044353235074213 2129211464258316231576415)
  ·
    refine ⟨3193817196387474347364623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2129211464258316231576415 3193817196387474347364623)
    ·
      refine ⟨4790725794581211521046935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3193817196387474347364623 4790725794581211521046935)
      ·
        refine ⟨7186088691871817281570403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4790725794581211521046935 7186088691871817281570403)
        ·
          refine ⟨10779133037807725922355605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7186088691871817281570403 10779133037807725922355605)
          ·
            refine ⟨505271861147237152610419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10779133037807725922355605 505271861147237152610419)
            ·
              refine ⟨757907791720855728915629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505271861147237152610419 757907791720855728915629)
              ·
                refine ⟨284215421895320898343361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 757907791720855728915629 284215421895320898343361)
                ·
                  refine ⟨213161566421490673757521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284215421895320898343361 213161566421490673757521)
                  ·
                    rfl

theorem cell20_467022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_467022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467022 prefixEnd_467022 := by exact prefixLift 467022
  have htrace : WordTrace (prefixWord ++ tailWord_467022) baseStart_467022 baseEnd_467022 := by
    simpa [prefixWord, tailWord_467022, baseEnd_467022] using wordTrace_append hprefix tailTrace_467022
  have hstable : (prefixWord ++ tailWord_467022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467022).length < 2 ^ (prefixWord ++ tailWord_467022).sum := by decide
  have hdescent : baseEnd_467022 < baseStart_467022 := by decide
  rcases family_descends (prefixWord ++ tailWord_467022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467040 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_467040 : Nat := 118140960795 + 467040 * 2 ^ 59
def prefixEnd_467040 : Nat := 4983230072969 + 3 ^ 40 * 467040 * 2
def baseEnd_467040 : Nat := 213169782111962611157447

theorem tailTrace_467040 : CollatzResearch.WordTrace tailWord_467040 prefixEnd_467040 213169782111962611157447 := by
  unfold tailWord_467040
  simp only [CollatzResearch.WordTrace]
  refine ⟨8517174114000659463383287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11356232152000879284511049 8517174114000659463383287)
  ·
    refine ⟨12775761171000989195074931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8517174114000659463383287 12775761171000989195074931)
    ·
      refine ⟨19163641756501483792612397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12775761171000989195074931 19163641756501483792612397)
      ·
        refine ⟨7186365658688056422229649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19163641756501483792612397 7186365658688056422229649)
        ·
          refine ⟨5389774244016042316672237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7186365658688056422229649 5389774244016042316672237)
          ·
            refine ⟨2021165341506015868752089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5389774244016042316672237 2021165341506015868752089)
            ·
              refine ⟨1515874006129511901564067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021165341506015868752089 1515874006129511901564067)
              ·
                refine ⟨2273811009194267852346101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515874006129511901564067 2273811009194267852346101)
                ·
                  refine ⟨213169782111962611157447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2273811009194267852346101 213169782111962611157447)
                  ·
                    rfl

theorem cell20_467040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_467040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467040 prefixEnd_467040 := by exact prefixLift 467040
  have htrace : WordTrace (prefixWord ++ tailWord_467040) baseStart_467040 baseEnd_467040 := by
    simpa [prefixWord, tailWord_467040, baseEnd_467040] using wordTrace_append hprefix tailTrace_467040
  have hstable : (prefixWord ++ tailWord_467040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467040).length < 2 ^ (prefixWord ++ tailWord_467040).sum := by decide
  have hdescent : baseEnd_467040 < baseStart_467040 := by decide
  rcases family_descends (prefixWord ++ tailWord_467040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467050 : List Nat := [3, 1, 3, 2, 3, 1, 2, 5]
def baseStart_467050 : Nat := 118140960795 + 467050 * 2 ^ 59
def prefixEnd_467050 : Nat := 4983230072969 + 3 ^ 40 * 467050 * 2
def baseEnd_467050 : Nat := 71058115461482340274691

theorem tailTrace_467050 : CollatzResearch.WordTrace tailWord_467050 prefixEnd_467050 71058115461482340274691 := by
  unfold tailWord_467050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4258678239491272658657651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11356475305310060423087069 4258678239491272658657651)
  ·
    refine ⟨6388017359236908987986477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4258678239491272658657651 6388017359236908987986477)
    ·
      refine ⟨2395506509713840870494929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6388017359236908987986477 2395506509713840870494929)
      ·
        refine ⟨1796629882285380652871197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2395506509713840870494929 1796629882285380652871197)
        ·
          refine ⟨673736205857017744826699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1796629882285380652871197 673736205857017744826699)
          ·
            refine ⟨1010604308785526617240049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673736205857017744826699 1010604308785526617240049)
            ·
              refine ⟨757953231589144962930037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010604308785526617240049 757953231589144962930037)
              ·
                refine ⟨71058115461482340274691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 757953231589144962930037 71058115461482340274691)
                ·
                  rfl

theorem cell20_467050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_467050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467050 prefixEnd_467050 := by exact prefixLift 467050
  have htrace : WordTrace (prefixWord ++ tailWord_467050) baseStart_467050 baseEnd_467050 := by
    simpa [prefixWord, tailWord_467050, baseEnd_467050] using wordTrace_append hprefix tailTrace_467050
  have hstable : (prefixWord ++ tailWord_467050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467050).length < 2 ^ (prefixWord ++ tailWord_467050).sum := by decide
  have hdescent : baseEnd_467050 < baseStart_467050 := by decide
  rcases family_descends (prefixWord ++ tailWord_467050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467098 : List Nat := [3, 1, 1, 5, 2, 1, 1, 4, 2]
def baseStart_467098 : Nat := 118140960795 + 467098 * 2 ^ 59
def prefixEnd_467098 : Nat := 4983230072969 + 3 ^ 40 * 467098 * 2
def baseEnd_467098 : Nat := 213196254892372187223877

theorem tailTrace_467098 : CollatzResearch.WordTrace tailWord_467098 prefixEnd_467098 213196254892372187223877 := by
  unfold tailWord_467098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259115915447798708094487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11357642441194129888251965 4259115915447798708094487)
  ·
    refine ⟨6388673873171698062141731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4259115915447798708094487 6388673873171698062141731)
    ·
      refine ⟨9583010809757547093212597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6388673873171698062141731 9583010809757547093212597)
      ·
        refine ⟨898407263414770039988681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9583010809757547093212597 898407263414770039988681)
        ·
          refine ⟨673805447561077529991511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898407263414770039988681 673805447561077529991511)
          ·
            refine ⟨1010708171341616294987267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673805447561077529991511 1010708171341616294987267)
            ·
              refine ⟨1516062257012424442480901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010708171341616294987267 1516062257012424442480901)
              ·
                refine ⟨284261673189829582965169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1516062257012424442480901 284261673189829582965169)
                ·
                  refine ⟨213196254892372187223877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284261673189829582965169 213196254892372187223877)
                  ·
                    rfl

theorem cell20_467098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_467098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467098 prefixEnd_467098 := by exact prefixLift 467098
  have htrace : WordTrace (prefixWord ++ tailWord_467098) baseStart_467098 baseEnd_467098 := by
    simpa [prefixWord, tailWord_467098, baseEnd_467098] using wordTrace_append hprefix tailTrace_467098
  have hstable : (prefixWord ++ tailWord_467098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467098).length < 2 ^ (prefixWord ++ tailWord_467098).sum := by decide
  have hdescent : baseEnd_467098 < baseStart_467098 := by decide
  rcases family_descends (prefixWord ++ tailWord_467098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467130 : List Nat := [3, 1, 1, 1, 2, 2, 2, 8]
def baseStart_467130 : Nat := 118140960795 + 467130 * 2 ^ 59
def prefixEnd_467130 : Nat := 4983230072969 + 3 ^ 40 * 467130 * 2
def baseEnd_467130 : Nat := 71070286854774099385693

theorem tailTrace_467130 : CollatzResearch.WordTrace tailWord_467130 prefixEnd_467130 71070286854774099385693 := by
  unfold tailWord_467130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259407699418816074385711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11358420531783509531695229 4259407699418816074385711)
  ·
    refine ⟨6389111549128224111578567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4259407699418816074385711 6389111549128224111578567)
    ·
      refine ⟨9583667323692336167367851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6389111549128224111578567 9583667323692336167367851)
      ·
        refine ⟨14375500985538504251051777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9583667323692336167367851 14375500985538504251051777)
        ·
          refine ⟨10781625739153878188288833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14375500985538504251051777 10781625739153878188288833)
          ·
            refine ⟨8086219304365408641216625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10781625739153878188288833 8086219304365408641216625)
            ·
              refine ⟨6064664478274056480912469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8086219304365408641216625 6064664478274056480912469)
              ·
                refine ⟨71070286854774099385693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6064664478274056480912469 71070286854774099385693)
                ·
                  rfl

theorem cell20_467130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_467130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467130 prefixEnd_467130 := by exact prefixLift 467130
  have htrace : WordTrace (prefixWord ++ tailWord_467130) baseStart_467130 baseEnd_467130 := by
    simpa [prefixWord, tailWord_467130, baseEnd_467130] using wordTrace_append hprefix tailTrace_467130
  have hstable : (prefixWord ++ tailWord_467130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467130).length < 2 ^ (prefixWord ++ tailWord_467130).sum := by decide
  have hdescent : baseEnd_467130 < baseStart_467130 := by decide
  rcases family_descends (prefixWord ++ tailWord_467130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467150 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_467150 : Nat := 118140960795 + 467150 * 2 ^ 59
def prefixEnd_467150 : Nat := 4983230072969 + 3 ^ 40 * 467150 * 2
def baseEnd_467150 : Nat := 213219989109291117490331

theorem tailTrace_467150 : CollatzResearch.WordTrace tailWord_467150 prefixEnd_467150 213219989109291117490331 := by
  unfold tailWord_467150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2129795032200350964158863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11358906838401871808847269 2129795032200350964158863)
  ·
    refine ⟨3194692548300526446238295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2129795032200350964158863 3194692548300526446238295)
    ·
      refine ⟨4792038822450789669357443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3194692548300526446238295 4792038822450789669357443)
      ·
        refine ⟨7188058233676184504036165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4792038822450789669357443 7188058233676184504036165)
        ·
          refine ⟨1347760918814284594506781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7188058233676184504036165 1347760918814284594506781)
          ·
            refine ⟨505410344555356722940043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1347760918814284594506781 505410344555356722940043)
            ·
              refine ⟨758115516833035084410065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505410344555356722940043 758115516833035084410065)
              ·
                refine ⟨568586637624776313307549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758115516833035084410065 568586637624776313307549)
                ·
                  refine ⟨213219989109291117490331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568586637624776313307549 213219989109291117490331)
                  ·
                    rfl

theorem cell20_467150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_467150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467150 prefixEnd_467150 := by exact prefixLift 467150
  have htrace : WordTrace (prefixWord ++ tailWord_467150) baseStart_467150 baseEnd_467150 := by
    simpa [prefixWord, tailWord_467150, baseEnd_467150] using wordTrace_append hprefix tailTrace_467150
  have hstable : (prefixWord ++ tailWord_467150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467150).length < 2 ^ (prefixWord ++ tailWord_467150).sum := by decide
  have hdescent : baseEnd_467150 < baseStart_467150 := by decide
  rcases family_descends (prefixWord ++ tailWord_467150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467157 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 4]
def baseStart_467157 : Nat := 118140960795 + 467157 * 2 ^ 59
def prefixEnd_467157 : Nat := 4983230072969 + 3 ^ 40 * 467157 * 2
def baseEnd_467157 : Nat := 213223184100030204256969

theorem tailTrace_467157 : CollatzResearch.WordTrace tailWord_467157 prefixEnd_467157 213223184100030204256969 := by
  unfold tailWord_467157
  simp only [CollatzResearch.WordTrace]
  refine ⟨17038615568577447908775725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11359077045718298605850483 17038615568577447908775725)
  ·
    refine ⟨6389480838216542965790897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17038615568577447908775725 6389480838216542965790897)
    ·
      refine ⟨4792110628662407224343173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6389480838216542965790897 4792110628662407224343173)
      ·
        refine ⟨898520742874201354564345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4792110628662407224343173 898520742874201354564345)
        ·
          refine ⟨673890557155651015923259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898520742874201354564345 673890557155651015923259)
          ·
            refine ⟨1010835835733476523884889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673890557155651015923259 1010835835733476523884889)
            ·
              refine ⟨758126876800107392913667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010835835733476523884889 758126876800107392913667)
              ·
                refine ⟨1137190315200161089370501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758126876800107392913667 1137190315200161089370501)
                ·
                  refine ⟨213223184100030204256969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137190315200161089370501 213223184100030204256969)
                  ·
                    rfl

theorem cell20_467157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_467157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467157 prefixEnd_467157 := by exact prefixLift 467157
  have htrace : WordTrace (prefixWord ++ tailWord_467157) baseStart_467157 baseEnd_467157 := by
    simpa [prefixWord, tailWord_467157, baseEnd_467157] using wordTrace_append hprefix tailTrace_467157
  have hstable : (prefixWord ++ tailWord_467157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467157).length < 2 ^ (prefixWord ++ tailWord_467157).sum := by decide
  have hdescent : baseEnd_467157 < baseStart_467157 := by decide
  rcases family_descends (prefixWord ++ tailWord_467157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467161 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 4]
def baseStart_467161 : Nat := 118140960795 + 467161 * 2 ^ 59
def prefixEnd_467161 : Nat := 4983230072969 + 3 ^ 40 * 467161 * 2
def baseEnd_467161 : Nat := 213225009809023968123619

theorem tailTrace_467161 : CollatzResearch.WordTrace tailWord_467161 prefixEnd_467161 213225009809023968123619 := by
  unfold tailWord_467161
  simp only [CollatzResearch.WordTrace]
  refine ⟨17038761460562956591921337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11359174307041971061280891 17038761460562956591921337)
  ·
    refine ⟨12779071095422217443941003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17038761460562956591921337 12779071095422217443941003)
    ·
      refine ⟨19168606643133326165911505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12779071095422217443941003 19168606643133326165911505)
      ·
        refine ⟨14376454982349994624433629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19168606643133326165911505 14376454982349994624433629)
        ·
          refine ⟨5391170618381247984162611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14376454982349994624433629 5391170618381247984162611)
          ·
            refine ⟨8086755927571871976243917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391170618381247984162611 8086755927571871976243917)
            ·
              refine ⟨3032533472839451991091469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8086755927571871976243917 3032533472839451991091469)
              ·
                refine ⟨1137200052314794496659301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3032533472839451991091469 1137200052314794496659301)
                ·
                  refine ⟨213225009809023968123619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137200052314794496659301 213225009809023968123619)
                  ·
                    rfl

theorem cell20_467161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_467161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467161 prefixEnd_467161 := by exact prefixLift 467161
  have htrace : WordTrace (prefixWord ++ tailWord_467161) baseStart_467161 baseEnd_467161 := by
    simpa [prefixWord, tailWord_467161, baseEnd_467161] using wordTrace_append hprefix tailTrace_467161
  have hstable : (prefixWord ++ tailWord_467161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467161).length < 2 ^ (prefixWord ++ tailWord_467161).sum := by decide
  have hdescent : baseEnd_467161 < baseStart_467161 := by decide
  rcases family_descends (prefixWord ++ tailWord_467161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467168 : List Nat := [2, 1, 1, 3, 1, 3, 2, 7]
def baseStart_467168 : Nat := 118140960795 + 467168 * 2 ^ 59
def prefixEnd_467168 : Nat := 4983230072969 + 3 ^ 40 * 467168 * 2
def baseEnd_467168 : Nat := 71076068266587684963419

theorem tailTrace_467168 : CollatzResearch.WordTrace tailWord_467168 prefixEnd_467168 71076068266587684963419 := by
  unfold tailWord_467168
  simp only [CollatzResearch.WordTrace]
  refine ⟨8519508385768798393713079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11359344514358397858284105 8519508385768798393713079)
  ·
    refine ⟨12779262578653197590569619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8519508385768798393713079 12779262578653197590569619)
    ·
      refine ⟨19168893867979796385854429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12779262578653197590569619 19168893867979796385854429)
      ·
        refine ⟨7188335200492423644695411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19168893867979796385854429 7188335200492423644695411)
        ·
          refine ⟨10782502800738635467043117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7188335200492423644695411 10782502800738635467043117)
          ·
            refine ⟨4043438550276988300141169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10782502800738635467043117 4043438550276988300141169)
            ·
              refine ⟨3032578912707741225105877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4043438550276988300141169 3032578912707741225105877)
              ·
                refine ⟨71076068266587684963419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3032578912707741225105877 71076068266587684963419)
                ·
                  rfl

theorem cell20_467168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_467168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467168 prefixEnd_467168 := by exact prefixLift 467168
  have htrace : WordTrace (prefixWord ++ tailWord_467168) baseStart_467168 baseEnd_467168 := by
    simpa [prefixWord, tailWord_467168, baseEnd_467168] using wordTrace_append hprefix tailTrace_467168
  have hstable : (prefixWord ++ tailWord_467168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467168).length < 2 ^ (prefixWord ++ tailWord_467168).sum := by decide
  have hdescent : baseEnd_467168 < baseStart_467168 := by decide
  rcases family_descends (prefixWord ++ tailWord_467168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467181 : List Nat := [1, 5, 1, 2, 3, 2, 2, 4]
def baseStart_467181 : Nat := 118140960795 + 467181 * 2 ^ 59
def prefixEnd_467181 : Nat := 4983230072969 + 3 ^ 40 * 467181 * 2
def baseEnd_467181 : Nat := 71078046117997595818957

theorem tailTrace_467181 : CollatzResearch.WordTrace tailWord_467181 prefixEnd_467181 71078046117997595818957 := by
  unfold tailWord_467181
  simp only [CollatzResearch.WordTrace]
  refine ⟨17039490920490500007649397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11359660613660333338432931 17039490920490500007649397)
  ·
    refine ⟨1597452273795984375717131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17039490920490500007649397 1597452273795984375717131)
    ·
      refine ⟨2396178410693976563575697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597452273795984375717131 2396178410693976563575697)
      ·
        refine ⟨1797133808020482422681773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2396178410693976563575697 1797133808020482422681773)
        ·
          refine ⟨673925178007680908505665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1797133808020482422681773 673925178007680908505665)
          ·
            refine ⟨505443883505760681379249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673925178007680908505665 505443883505760681379249)
            ·
              refine ⟨379082912629320511034437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505443883505760681379249 379082912629320511034437)
              ·
                refine ⟨71078046117997595818957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379082912629320511034437 71078046117997595818957)
                ·
                  rfl

theorem cell20_467181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 4].length) (baseStart_467181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467181 prefixEnd_467181 := by exact prefixLift 467181
  have htrace : WordTrace (prefixWord ++ tailWord_467181) baseStart_467181 baseEnd_467181 := by
    simpa [prefixWord, tailWord_467181, baseEnd_467181] using wordTrace_append hprefix tailTrace_467181
  have hstable : (prefixWord ++ tailWord_467181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467181).length < 2 ^ (prefixWord ++ tailWord_467181).sum := by decide
  have hdescent : baseEnd_467181 < baseStart_467181 := by decide
  rcases family_descends (prefixWord ++ tailWord_467181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467185 : List Nat := [1, 2, 2, 2, 2, 1, 6, 4]
def baseStart_467185 : Nat := 118140960795 + 467185 * 2 ^ 59
def prefixEnd_467185 : Nat := 4983230072969 + 3 ^ 40 * 467185 * 2
def baseEnd_467185 : Nat := 71078654687662183774507

theorem tailTrace_467185 : CollatzResearch.WordTrace tailWord_467185 prefixEnd_467185 71078654687662183774507 := by
  unfold tailWord_467185
  simp only [CollatzResearch.WordTrace]
  refine ⟨17039636812476008690795009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11359757874984005793863339 17039636812476008690795009)
  ·
    refine ⟨12779727609357006518096257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17039636812476008690795009 12779727609357006518096257)
    ·
      refine ⟨9584795707017754888572193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12779727609357006518096257 9584795707017754888572193)
      ·
        refine ⟨7188596780263316166429145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9584795707017754888572193 7188596780263316166429145)
        ·
          refine ⟨5391447585197487124821859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7188596780263316166429145 5391447585197487124821859)
          ·
            refine ⟨8087171377796230687232789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5391447585197487124821859 8087171377796230687232789)
            ·
              refine ⟨379086158334198313464037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8087171377796230687232789 379086158334198313464037)
              ·
                refine ⟨71078654687662183774507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379086158334198313464037 71078654687662183774507)
                ·
                  rfl

theorem cell20_467185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 4].length) (baseStart_467185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467185 prefixEnd_467185 := by exact prefixLift 467185
  have htrace : WordTrace (prefixWord ++ tailWord_467185) baseStart_467185 baseEnd_467185 := by
    simpa [prefixWord, tailWord_467185, baseEnd_467185] using wordTrace_append hprefix tailTrace_467185
  have hstable : (prefixWord ++ tailWord_467185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467185).length < 2 ^ (prefixWord ++ tailWord_467185).sum := by decide
  have hdescent : baseEnd_467185 < baseStart_467185 := by decide
  rcases family_descends (prefixWord ++ tailWord_467185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467202 : List Nat := [3, 4, 1, 1, 2, 3, 6]
def baseStart_467202 : Nat := 118140960795 + 467202 * 2 ^ 59
def prefixEnd_467202 : Nat := 4983230072969 + 3 ^ 40 * 467202 * 2
def baseEnd_467202 : Nat := 23693747036245560861865

theorem tailTrace_467202 : CollatzResearch.WordTrace tailWord_467202 prefixEnd_467202 23693747036245560861865 := by
  unfold tailWord_467202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4260064213353605148540965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11360171235609613729442573 4260064213353605148540965)
  ·
    refine ⟨798762040003800965351431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4260064213353605148540965 798762040003800965351431)
    ·
      refine ⟨1198143060005701448027147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 798762040003800965351431 1198143060005701448027147)
      ·
        refine ⟨1797214590008552172040721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1198143060005701448027147 1797214590008552172040721)
        ·
          refine ⟨1347910942506414129030541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1797214590008552172040721 1347910942506414129030541)
          ·
            refine ⟨505466603439905298386453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1347910942506414129030541 505466603439905298386453)
            ·
              refine ⟨23693747036245560861865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 505466603439905298386453 23693747036245560861865)
              ·
                rfl

theorem cell20_467202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 6].length) (baseStart_467202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467202 prefixEnd_467202 := by exact prefixLift 467202
  have htrace : WordTrace (prefixWord ++ tailWord_467202) baseStart_467202 baseEnd_467202 := by
    simpa [prefixWord, tailWord_467202, baseEnd_467202] using wordTrace_append hprefix tailTrace_467202
  have hstable : (prefixWord ++ tailWord_467202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467202).length < 2 ^ (prefixWord ++ tailWord_467202).sum := by decide
  have hdescent : baseEnd_467202 < baseStart_467202 := by decide
  rcases family_descends (prefixWord ++ tailWord_467202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467223 : List Nat := [1, 1, 3, 4, 1, 3, 2, 5]
def baseStart_467223 : Nat := 118140960795 + 467223 * 2 ^ 59
def prefixEnd_467223 : Nat := 4983230072969 + 3 ^ 40 * 467223 * 2
def baseEnd_467223 : Nat := 71084436099475769352233

theorem tailTrace_467223 : CollatzResearch.WordTrace tailWord_467223 prefixEnd_467223 71084436099475769352233 := by
  unfold tailWord_467223
  simp only [CollatzResearch.WordTrace]
  refine ⟨17041022786338341180678323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11360681857558894120452215 17041022786338341180678323)
  ·
    refine ⟨25561534179507511771017485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17041022786338341180678323 25561534179507511771017485)
    ·
      refine ⟨9585575317315316914131557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25561534179507511771017485 9585575317315316914131557)
      ·
        refine ⟨1797295371996621921399667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9585575317315316914131557 1797295371996621921399667)
        ·
          refine ⟨2695943057994932882099501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797295371996621921399667 2695943057994932882099501)
          ·
            refine ⟨1010978646748099830787313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2695943057994932882099501 1010978646748099830787313)
            ·
              refine ⟨758233985061074873090485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010978646748099830787313 758233985061074873090485)
              ·
                refine ⟨71084436099475769352233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 758233985061074873090485 71084436099475769352233)
                ·
                  rfl

theorem cell20_467223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_467223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467223 prefixEnd_467223 := by exact prefixLift 467223
  have htrace : WordTrace (prefixWord ++ tailWord_467223) baseStart_467223 baseEnd_467223 := by
    simpa [prefixWord, tailWord_467223, baseEnd_467223] using wordTrace_append hprefix tailTrace_467223
  have hstable : (prefixWord ++ tailWord_467223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467223).length < 2 ^ (prefixWord ++ tailWord_467223).sum := by decide
  have hdescent : baseEnd_467223 < baseStart_467223 := by decide
  rcases family_descends (prefixWord ++ tailWord_467223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467244 : List Nat := [2, 2, 1, 1, 1, 3, 4, 6]
def baseStart_467244 : Nat := 118140960795 + 467244 * 2 ^ 59
def prefixEnd_467244 : Nat := 4983230072969 + 3 ^ 40 * 467244 * 2
def baseEnd_467244 : Nat := 71087631090214856118871

theorem tailTrace_467244 : CollatzResearch.WordTrace tailWord_467244 prefixEnd_467244 71087631090214856118871 := by
  unfold tailWord_467244
  simp only [CollatzResearch.WordTrace]
  refine ⟨8520894359631130883596393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11361192479508174511461857 8520894359631130883596393)
  ·
    refine ⟨6390670769723348162697295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8520894359631130883596393 6390670769723348162697295)
    ·
      refine ⟨9586006154585022244045943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6390670769723348162697295 9586006154585022244045943)
      ·
        refine ⟨14379009231877533366068915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9586006154585022244045943 14379009231877533366068915)
        ·
          refine ⟨21568513847816300049103373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14379009231877533366068915 21568513847816300049103373)
          ·
            refine ⟨8088192692931112518413765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21568513847816300049103373 8088192692931112518413765)
            ·
              refine ⟨1516536129924583597202581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8088192692931112518413765 1516536129924583597202581)
              ·
                refine ⟨71087631090214856118871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1516536129924583597202581 71087631090214856118871)
                ·
                  rfl

theorem cell20_467244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_467244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467244 prefixEnd_467244 := by exact prefixLift 467244
  have htrace : WordTrace (prefixWord ++ tailWord_467244) baseStart_467244 baseEnd_467244 := by
    simpa [prefixWord, tailWord_467244, baseEnd_467244] using wordTrace_append hprefix tailTrace_467244
  have hstable : (prefixWord ++ tailWord_467244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467244).length < 2 ^ (prefixWord ++ tailWord_467244).sum := by decide
  have hdescent : baseEnd_467244 < baseStart_467244 := by decide
  rcases family_descends (prefixWord ++ tailWord_467244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467289 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_467289 : Nat := 118140960795 + 467289 * 2 ^ 59
def prefixEnd_467289 : Nat := 4983230072969 + 3 ^ 40 * 467289 * 2
def baseEnd_467289 : Nat := 213283432496824411856429

theorem tailTrace_467289 : CollatzResearch.WordTrace tailWord_467289 prefixEnd_467289 213283432496824411856429 := by
  unfold tailWord_467289
  simp only [CollatzResearch.WordTrace]
  refine ⟨17043430004099234452580921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11362286669399489635053947 17043430004099234452580921)
  ·
    refine ⟨12782572503074425839435691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17043430004099234452580921 12782572503074425839435691)
    ·
      refine ⟨19173858754611638759153537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12782572503074425839435691 19173858754611638759153537)
      ·
        refine ⟨14380394065958729069365153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19173858754611638759153537 14380394065958729069365153)
        ·
          refine ⟨10785295549469046802023865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14380394065958729069365153 10785295549469046802023865)
          ·
            refine ⟨8088971662101785101517899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10785295549469046802023865 8088971662101785101517899)
            ·
              refine ⟨12133457493152677652276849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088971662101785101517899 12133457493152677652276849)
              ·
                refine ⟨9100093119864508239207637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12133457493152677652276849 9100093119864508239207637)
                ·
                  refine ⟨213283432496824411856429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9100093119864508239207637 213283432496824411856429)
                  ·
                    rfl

theorem cell20_467289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_467289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467289 prefixEnd_467289 := by exact prefixLift 467289
  have htrace : WordTrace (prefixWord ++ tailWord_467289) baseStart_467289 baseEnd_467289 := by
    simpa [prefixWord, tailWord_467289, baseEnd_467289] using wordTrace_append hprefix tailTrace_467289
  have hstable : (prefixWord ++ tailWord_467289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467289).length < 2 ^ (prefixWord ++ tailWord_467289).sum := by decide
  have hdescent : baseEnd_467289 < baseStart_467289 := by decide
  rcases family_descends (prefixWord ++ tailWord_467289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467299 : List Nat := [1, 1, 1, 5, 2, 1, 5, 4]
def baseStart_467299 : Nat := 118140960795 + 467299 * 2 ^ 59
def prefixEnd_467299 : Nat := 4983230072969 + 3 ^ 40 * 467299 * 2
def baseEnd_467299 : Nat := 71095998923102940507685

theorem tailTrace_467299 : CollatzResearch.WordTrace tailWord_467299 prefixEnd_467299 71095998923102940507685 := by
  unfold tailWord_467299
  simp only [CollatzResearch.WordTrace]
  refine ⟨17043794734063006160444951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11362529822708670773629967 17043794734063006160444951)
  ·
    refine ⟨25565692101094509240667427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17043794734063006160444951 25565692101094509240667427)
    ·
      refine ⟨38348538151641763861001141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25565692101094509240667427 38348538151641763861001141)
      ·
        refine ⟨3595175451716415361968857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38348538151641763861001141 3595175451716415361968857)
        ·
          refine ⟨2696381588787311521476643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3595175451716415361968857 2696381588787311521476643)
          ·
            refine ⟨4044572383180967282214965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696381588787311521476643 4044572383180967282214965)
            ·
              refine ⟨379178660923215682707653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4044572383180967282214965 379178660923215682707653)
              ·
                refine ⟨71095998923102940507685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379178660923215682707653 71095998923102940507685)
                ·
                  rfl

theorem cell20_467299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 4].length) (baseStart_467299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467299 prefixEnd_467299 := by exact prefixLift 467299
  have htrace : WordTrace (prefixWord ++ tailWord_467299) baseStart_467299 baseEnd_467299 := by
    simpa [prefixWord, tailWord_467299, baseEnd_467299] using wordTrace_append hprefix tailTrace_467299
  have hstable : (prefixWord ++ tailWord_467299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467299).length < 2 ^ (prefixWord ++ tailWord_467299).sum := by decide
  have hdescent : baseEnd_467299 < baseStart_467299 := by decide
  rcases family_descends (prefixWord ++ tailWord_467299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467309 : List Nat := [1, 5, 1, 1, 1, 2, 4, 3, 2]
def baseStart_467309 : Nat := 118140960795 + 467309 * 2 ^ 59
def prefixEnd_467309 : Nat := 4983230072969 + 3 ^ 40 * 467309 * 2
def baseEnd_467309 : Nat := 213292561041793231189681

theorem tailTrace_467309 : CollatzResearch.WordTrace tailWord_467309 prefixEnd_467309 213292561041793231189681 := by
  unfold tailWord_467309
  simp only [CollatzResearch.WordTrace]
  refine ⟨17044159464026777868308981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11362772976017851912205987 17044159464026777868308981)
  ·
    refine ⟨1597889949752510425153967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17044159464026777868308981 1597889949752510425153967)
    ·
      refine ⟨2396834924628765637730951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597889949752510425153967 2396834924628765637730951)
      ·
        refine ⟨3595252386943148456596427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396834924628765637730951 3595252386943148456596427)
        ·
          refine ⟨5392878580414722684894641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595252386943148456596427 5392878580414722684894641)
          ·
            refine ⟨4044658935311042013670981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5392878580414722684894641 4044658935311042013670981)
            ·
              refine ⟨758373550370820377563309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4044658935311042013670981 758373550370820377563309)
              ·
                refine ⟨284390081389057641586241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 758373550370820377563309 284390081389057641586241)
                ·
                  refine ⟨213292561041793231189681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284390081389057641586241 213292561041793231189681)
                  ·
                    rfl

theorem cell20_467309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_467309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467309 prefixEnd_467309 := by exact prefixLift 467309
  have htrace : WordTrace (prefixWord ++ tailWord_467309) baseStart_467309 baseEnd_467309 := by
    simpa [prefixWord, tailWord_467309, baseEnd_467309] using wordTrace_append hprefix tailTrace_467309
  have hstable : (prefixWord ++ tailWord_467309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467309).length < 2 ^ (prefixWord ++ tailWord_467309).sum := by decide
  have hdescent : baseEnd_467309 < baseStart_467309 := by decide
  rcases family_descends (prefixWord ++ tailWord_467309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467323 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 3]
def baseStart_467323 : Nat := 118140960795 + 467323 * 2 ^ 59
def prefixEnd_467323 : Nat := 4983230072969 + 3 ^ 40 * 467323 * 2
def baseEnd_467323 : Nat := 213298951023271404722957

theorem tailTrace_467323 : CollatzResearch.WordTrace tailWord_467323 prefixEnd_467323 213298951023271404722957 := by
  unfold tailWord_467323
  simp only [CollatzResearch.WordTrace]
  refine ⟨17044670085976058259318623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11363113390650705506212415 17044670085976058259318623)
  ·
    refine ⟨25567005128964087388977935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17044670085976058259318623 25567005128964087388977935)
    ·
      refine ⟨38350507693446131083466903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25567005128964087388977935 38350507693446131083466903)
      ·
        refine ⟨57525761540169196625200355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38350507693446131083466903 57525761540169196625200355)
        ·
          refine ⟨86288642310253794937800533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57525761540169196625200355 86288642310253794937800533)
          ·
            refine ⟨505597513536643329713675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 86288642310253794937800533 505597513536643329713675)
            ·
              refine ⟨758396270304964994570513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505597513536643329713675 758396270304964994570513)
              ·
                refine ⟨568797202728723745927885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758396270304964994570513 568797202728723745927885)
                ·
                  refine ⟨213298951023271404722957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568797202728723745927885 213298951023271404722957)
                  ·
                    rfl

theorem cell20_467323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 3].length) (baseStart_467323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467323 prefixEnd_467323 := by exact prefixLift 467323
  have htrace : WordTrace (prefixWord ++ tailWord_467323) baseStart_467323 baseEnd_467323 := by
    simpa [prefixWord, tailWord_467323, baseEnd_467323] using wordTrace_append hprefix tailTrace_467323
  have hstable : (prefixWord ++ tailWord_467323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467323).length < 2 ^ (prefixWord ++ tailWord_467323).sum := by decide
  have hdescent : baseEnd_467323 < baseStart_467323 := by decide
  rcases family_descends (prefixWord ++ tailWord_467323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467327 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_467327 : Nat := 118140960795 + 467327 * 2 ^ 59
def prefixEnd_467327 : Nat := 4983230072969 + 3 ^ 40 * 467327 * 2
def baseEnd_467327 : Nat := 213300776732265168589607

theorem tailTrace_467327 : CollatzResearch.WordTrace tailWord_467327 prefixEnd_467327 213300776732265168589607 := by
  unfold tailWord_467327
  simp only [CollatzResearch.WordTrace]
  refine ⟨17044815977961566942464235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11363210651974377961642823 17044815977961566942464235)
  ·
    refine ⟨25567223966942350413696353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17044815977961566942464235 25567223966942350413696353)
    ·
      refine ⟨19175417975206762810272265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25567223966942350413696353 19175417975206762810272265)
      ·
        refine ⟨14381563481405072107704199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19175417975206762810272265 14381563481405072107704199)
        ·
          refine ⟨21572345222107608161556299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14381563481405072107704199 21572345222107608161556299)
          ·
            refine ⟨32358517833161412242334449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21572345222107608161556299 32358517833161412242334449)
            ·
              refine ⟨24268888374871059181750837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32358517833161412242334449 24268888374871059181750837)
              ·
                refine ⟨2275208285144161798289141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24268888374871059181750837 2275208285144161798289141)
                ·
                  refine ⟨213300776732265168589607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2275208285144161798289141 213300776732265168589607)
                  ·
                    rfl

theorem cell20_467327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_467327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467327 prefixEnd_467327 := by exact prefixLift 467327
  have htrace : WordTrace (prefixWord ++ tailWord_467327) baseStart_467327 baseEnd_467327 := by
    simpa [prefixWord, tailWord_467327, baseEnd_467327] using wordTrace_append hprefix tailTrace_467327
  have hstable : (prefixWord ++ tailWord_467327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467327).length < 2 ^ (prefixWord ++ tailWord_467327).sum := by decide
  have hdescent : baseEnd_467327 < baseStart_467327 := by decide
  rcases family_descends (prefixWord ++ tailWord_467327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467350 : List Nat := [5, 3, 1, 2, 1, 1, 1, 6]
def baseStart_467350 : Nat := 118140960795 + 467350 * 2 ^ 59
def prefixEnd_467350 : Nat := 4983230072969 + 3 ^ 40 * 467350 * 2
def baseEnd_467350 : Nat := 71103758186326436940949

theorem tailTrace_467350 : CollatzResearch.WordTrace tailWord_467350 prefixEnd_467350 71103758186326436940949 := by
  unfold tailWord_467350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1065353428554890116909469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11363769904585494580367669 1065353428554890116909469)
  ·
    refine ⟨399507535708083793841051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1065353428554890116909469 399507535708083793841051)
    ·
      refine ⟨599261303562125690761577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399507535708083793841051 599261303562125690761577)
      ·
        refine ⟨449445977671594268071183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599261303562125690761577 449445977671594268071183)
        ·
          refine ⟨674168966507391402106775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449445977671594268071183 674168966507391402106775)
          ·
            refine ⟨1011253449761087103160163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674168966507391402106775 1011253449761087103160163)
            ·
              refine ⟨1516880174641630654740245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011253449761087103160163 1516880174641630654740245)
              ·
                refine ⟨71103758186326436940949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1516880174641630654740245 71103758186326436940949)
                ·
                  rfl

theorem cell20_467350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_467350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467350 prefixEnd_467350 := by exact prefixLift 467350
  have htrace : WordTrace (prefixWord ++ tailWord_467350) baseStart_467350 baseEnd_467350 := by
    simpa [prefixWord, tailWord_467350, baseEnd_467350] using wordTrace_append hprefix tailTrace_467350
  have hstable : (prefixWord ++ tailWord_467350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467350).length < 2 ^ (prefixWord ++ tailWord_467350).sum := by decide
  have hdescent : baseEnd_467350 < baseStart_467350 := by decide
  rcases family_descends (prefixWord ++ tailWord_467350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467351 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 4]
def baseStart_467351 : Nat := 118140960795 + 467351 * 2 ^ 59
def prefixEnd_467351 : Nat := 4983230072969 + 3 ^ 40 * 467351 * 2
def baseEnd_467351 : Nat := 213311730986227751789509

theorem tailTrace_467351 : CollatzResearch.WordTrace tailWord_467351 prefixEnd_467351 213311730986227751789509 := by
  unfold tailWord_467351
  simp only [CollatzResearch.WordTrace]
  refine ⟨17045691329874619041337907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11363794219916412694225271 17045691329874619041337907)
  ·
    refine ⟨25568536994811928562006861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17045691329874619041337907 25568536994811928562006861)
    ·
      refine ⟨9588201373054473210752573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25568536994811928562006861 9588201373054473210752573)
      ·
        refine ⟨3595575514895427454032215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9588201373054473210752573 3595575514895427454032215)
        ·
          refine ⟨5393363272343141181048323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595575514895427454032215 5393363272343141181048323)
          ·
            refine ⟨8090044908514711771572485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393363272343141181048323 8090044908514711771572485)
            ·
              refine ⟨1516883420346508457169841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8090044908514711771572485 1516883420346508457169841)
              ·
                refine ⟨1137662565259881342877381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516883420346508457169841 1137662565259881342877381)
                ·
                  refine ⟨213311730986227751789509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137662565259881342877381 213311730986227751789509)
                  ·
                    rfl

theorem cell20_467351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_467351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467351 prefixEnd_467351 := by exact prefixLift 467351
  have htrace : WordTrace (prefixWord ++ tailWord_467351) baseStart_467351 baseEnd_467351 := by
    simpa [prefixWord, tailWord_467351, baseEnd_467351] using wordTrace_append hprefix tailTrace_467351
  have hstable : (prefixWord ++ tailWord_467351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467351).length < 2 ^ (prefixWord ++ tailWord_467351).sum := by decide
  have hdescent : baseEnd_467351 < baseStart_467351 := by decide
  rcases family_descends (prefixWord ++ tailWord_467351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467354 : List Nat := [3, 1, 1, 4, 1, 4, 2, 4]
def baseStart_467354 : Nat := 118140960795 + 467354 * 2 ^ 59
def prefixEnd_467354 : Nat := 4983230072969 + 3 ^ 40 * 467354 * 2
def baseEnd_467354 : Nat := 71104366755991024896499

theorem tailTrace_467354 : CollatzResearch.WordTrace tailWord_467354 prefixEnd_467354 71104366755991024896499 := by
  unfold tailWord_467354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261450187215937638424279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11363867165909167035798077 4261450187215937638424279)
  ·
    refine ⟨6392175280823906457636419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4261450187215937638424279 6392175280823906457636419)
    ·
      refine ⟨9588262921235859686454629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6392175280823906457636419 9588262921235859686454629)
      ·
        refine ⟨1797799297731723691210243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9588262921235859686454629 1797799297731723691210243)
        ·
          refine ⟨2696698946597585536815365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797799297731723691210243 2696698946597585536815365)
          ·
            refine ⟨505631052487047288152881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2696698946597585536815365 505631052487047288152881)
            ·
              refine ⟨379223289365285466114661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505631052487047288152881 379223289365285466114661)
              ·
                refine ⟨71104366755991024896499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379223289365285466114661 71104366755991024896499)
                ·
                  rfl

theorem cell20_467354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_467354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467354 prefixEnd_467354 := by exact prefixLift 467354
  have htrace : WordTrace (prefixWord ++ tailWord_467354) baseStart_467354 baseEnd_467354 := by
    simpa [prefixWord, tailWord_467354, baseEnd_467354] using wordTrace_append hprefix tailTrace_467354
  have hstable : (prefixWord ++ tailWord_467354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467354).length < 2 ^ (prefixWord ++ tailWord_467354).sum := by decide
  have hdescent : baseEnd_467354 < baseStart_467354 := by decide
  rcases family_descends (prefixWord ++ tailWord_467354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467365 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_467365 : Nat := 118140960795 + 467365 * 2 ^ 59
def prefixEnd_467365 : Nat := 4983230072969 + 3 ^ 40 * 467365 * 2
def baseEnd_467365 : Nat := 213318120967705925322785

theorem tailTrace_467365 : CollatzResearch.WordTrace tailWord_467365 prefixEnd_467365 213318120967705925322785 := by
  unfold tailWord_467365
  simp only [CollatzResearch.WordTrace]
  refine ⟨17046201951823899432347549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11364134634549266288231699 17046201951823899432347549)
  ·
    refine ⟨6392325731933962287130331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17046201951823899432347549 6392325731933962287130331)
    ·
      refine ⟨9588488597900943430695497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6392325731933962287130331 9588488597900943430695497)
      ·
        refine ⟨7191366448425707573021623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9588488597900943430695497 7191366448425707573021623)
        ·
          refine ⟨10787049672638561359532435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7191366448425707573021623 10787049672638561359532435)
          ·
            refine ⟨16180574508957842039298653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10787049672638561359532435 16180574508957842039298653)
            ·
              refine ⟨6067715440859190764736995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16180574508957842039298653 6067715440859190764736995)
              ·
                refine ⟨9101573161288786147105493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067715440859190764736995 9101573161288786147105493)
                ·
                  refine ⟨213318120967705925322785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9101573161288786147105493 213318120967705925322785)
                  ·
                    rfl

theorem cell20_467365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_467365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467365 prefixEnd_467365 := by exact prefixLift 467365
  have htrace : WordTrace (prefixWord ++ tailWord_467365) baseStart_467365 baseEnd_467365 := by
    simpa [prefixWord, tailWord_467365, baseEnd_467365] using wordTrace_append hprefix tailTrace_467365
  have hstable : (prefixWord ++ tailWord_467365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467365).length < 2 ^ (prefixWord ++ tailWord_467365).sum := by decide
  have hdescent : baseEnd_467365 < baseStart_467365 := by decide
  rcases family_descends (prefixWord ++ tailWord_467365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467399 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 3]
def baseStart_467399 : Nat := 118140960795 + 467399 * 2 ^ 59
def prefixEnd_467399 : Nat := 4983230072969 + 3 ^ 40 * 467399 * 2
def baseEnd_467399 : Nat := 213333639494152918189313

theorem tailTrace_467399 : CollatzResearch.WordTrace tailWord_467399 prefixEnd_467399 213333639494152918189313 := by
  unfold tailWord_467399
  simp only [CollatzResearch.WordTrace]
  refine ⟨17047442033700723239085251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11364961355800482159390167 17047442033700723239085251)
  ·
    refine ⟨25571163050551084858627877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17047442033700723239085251 25571163050551084858627877)
    ·
      refine ⟨4794593071978328410992727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25571163050551084858627877 4794593071978328410992727)
      ·
        refine ⟨7191889607967492616489091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4794593071978328410992727 7191889607967492616489091)
        ·
          refine ⟨10787834411951238924733637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7191889607967492616489091 10787834411951238924733637)
          ·
            refine ⟨2022718952240857298387557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10787834411951238924733637 2022718952240857298387557)
            ·
              refine ⟨379259803545160743447667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2022718952240857298387557 379259803545160743447667)
              ·
                refine ⟨568889705317741115171501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379259803545160743447667 568889705317741115171501)
                ·
                  refine ⟨213333639494152918189313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568889705317741115171501 213333639494152918189313)
                  ·
                    rfl

theorem cell20_467399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 3].length) (baseStart_467399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467399 prefixEnd_467399 := by exact prefixLift 467399
  have htrace : WordTrace (prefixWord ++ tailWord_467399) baseStart_467399 baseEnd_467399 := by
    simpa [prefixWord, tailWord_467399, baseEnd_467399] using wordTrace_append hprefix tailTrace_467399
  have hstable : (prefixWord ++ tailWord_467399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467399).length < 2 ^ (prefixWord ++ tailWord_467399).sum := by decide
  have hdescent : baseEnd_467399 < baseStart_467399 := by decide
  rcases family_descends (prefixWord ++ tailWord_467399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467434 : List Nat := [3, 1, 3, 1, 3, 9]
def baseStart_467434 : Nat := 118140960795 + 467434 * 2 ^ 59
def prefixEnd_467434 : Nat := 4983230072969 + 3 ^ 40 * 467434 * 2
def baseEnd_467434 : Nat := 7901837572142531556389

theorem tailTrace_467434 : CollatzResearch.WordTrace tailWord_467434 prefixEnd_467434 7901837572142531556389 := by
  unfold tailWord_467434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4262179647143481054152339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11365812392382616144406237 4262179647143481054152339)
  ·
    refine ⟨6393269470715221581228509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4262179647143481054152339 6393269470715221581228509)
    ·
      refine ⟨2397476051518208092960691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6393269470715221581228509 2397476051518208092960691)
      ·
        refine ⟨3596214077277312139441037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397476051518208092960691 3596214077277312139441037)
        ·
          refine ⟨1348580278978992052290389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3596214077277312139441037 1348580278978992052290389)
          ·
            refine ⟨7901837572142531556389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1348580278978992052290389 7901837572142531556389)
            ·
              rfl

theorem cell20_467434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 9].length) (baseStart_467434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467434 prefixEnd_467434 := by exact prefixLift 467434
  have htrace : WordTrace (prefixWord ++ tailWord_467434) baseStart_467434 baseEnd_467434 := by
    simpa [prefixWord, tailWord_467434, baseEnd_467434] using wordTrace_append hprefix tailTrace_467434
  have hstable : (prefixWord ++ tailWord_467434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467434).length < 2 ^ (prefixWord ++ tailWord_467434).sum := by decide
  have hdescent : baseEnd_467434 < baseStart_467434 := by decide
  rcases family_descends (prefixWord ++ tailWord_467434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467437 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 3]
def baseStart_467437 : Nat := 118140960795 + 467437 * 2 ^ 59
def prefixEnd_467437 : Nat := 4983230072969 + 3 ^ 40 * 467437 * 2
def baseEnd_467437 : Nat := 213350983729593674922491

theorem tailTrace_467437 : CollatzResearch.WordTrace tailWord_467437 prefixEnd_467437 213350983729593674922491 := by
  unfold tailWord_467437
  simp only [CollatzResearch.WordTrace]
  refine ⟨17048828007563055728968565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11365885338375370485979043 17048828007563055728968565)
  ·
    refine ⟨1598327625709036474590803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17048828007563055728968565 1598327625709036474590803)
    ·
      refine ⟨2397491438563554711886205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1598327625709036474590803 2397491438563554711886205)
      ·
        refine ⟨899059289461333016957327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2397491438563554711886205 899059289461333016957327)
        ·
          refine ⟨1348588934191999525435991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899059289461333016957327 1348588934191999525435991)
          ·
            refine ⟨2022883401287999288153987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348588934191999525435991 2022883401287999288153987)
            ·
              refine ⟨3034325101931998932230981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2022883401287999288153987 3034325101931998932230981)
              ·
                refine ⟨568935956612249799793309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3034325101931998932230981 568935956612249799793309)
                ·
                  refine ⟨213350983729593674922491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568935956612249799793309 213350983729593674922491)
                  ·
                    rfl

theorem cell20_467437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_467437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467437 prefixEnd_467437 := by exact prefixLift 467437
  have htrace : WordTrace (prefixWord ++ tailWord_467437) baseStart_467437 baseEnd_467437 := by
    simpa [prefixWord, tailWord_467437, baseEnd_467437] using wordTrace_append hprefix tailTrace_467437
  have hstable : (prefixWord ++ tailWord_467437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467437).length < 2 ^ (prefixWord ++ tailWord_467437).sum := by decide
  have hdescent : baseEnd_467437 < baseStart_467437 := by decide
  rcases family_descends (prefixWord ++ tailWord_467437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467482 : List Nat := [3, 1, 1, 3, 1, 1, 3, 5, 2]
def baseStart_467482 : Nat := 118140960795 + 467482 * 2 ^ 59
def prefixEnd_467482 : Nat := 4983230072969 + 3 ^ 40 * 467482 * 2
def baseEnd_467482 : Nat := 213371522955773518422307

theorem tailTrace_467482 : CollatzResearch.WordTrace tailWord_467482 prefixEnd_467482 213371522955773518422307 := by
  unfold tailWord_467482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4262617323100007103589175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11366979528266685609571133 4262617323100007103589175)
  ·
    refine ⟨6393925984650010655383763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4262617323100007103589175 6393925984650010655383763)
    ·
      refine ⟨9590888976975015983075645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6393925984650010655383763 9590888976975015983075645)
      ·
        refine ⟨3596583366365630993653367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9590888976975015983075645 3596583366365630993653367)
        ·
          refine ⟨5394875049548446490480051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3596583366365630993653367 5394875049548446490480051)
          ·
            refine ⟨8092312574322669735720077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394875049548446490480051 8092312574322669735720077)
            ·
              refine ⟨3034617215371001150895029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8092312574322669735720077 3034617215371001150895029)
              ·
                refine ⟨284495363941031357896409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3034617215371001150895029 284495363941031357896409)
                ·
                  refine ⟨213371522955773518422307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284495363941031357896409 213371522955773518422307)
                  ·
                    rfl

theorem cell20_467482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_467482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467482 prefixEnd_467482 := by exact prefixLift 467482
  have htrace : WordTrace (prefixWord ++ tailWord_467482) baseStart_467482 baseEnd_467482 := by
    simpa [prefixWord, tailWord_467482, baseEnd_467482] using wordTrace_append hprefix tailTrace_467482
  have hstable : (prefixWord ++ tailWord_467482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467482).length < 2 ^ (prefixWord ++ tailWord_467482).sum := by decide
  have hdescent : baseEnd_467482 < baseStart_467482 := by decide
  rcases family_descends (prefixWord ++ tailWord_467482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467513 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 3]
def baseStart_467513 : Nat := 118140960795 + 467513 * 2 ^ 59
def prefixEnd_467513 : Nat := 4983230072969 + 3 ^ 40 * 467513 * 2
def baseEnd_467513 : Nat := 213385672200475188388847

theorem tailTrace_467513 : CollatzResearch.WordTrace tailWord_467513 prefixEnd_467513 213385672200475188388847 := by
  unfold tailWord_467513
  simp only [CollatzResearch.WordTrace]
  refine ⟨17051599955287720708735193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11367733303525147139156795 17051599955287720708735193)
  ·
    refine ⟨12788699966465790531551395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17051599955287720708735193 12788699966465790531551395)
    ·
      refine ⟨19183049949698685797327093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12788699966465790531551395 19183049949698685797327093)
      ·
        refine ⟨1798410932784251793499415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19183049949698685797327093 1798410932784251793499415)
        ·
          refine ⟨2697616399176377690249123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798410932784251793499415 2697616399176377690249123)
          ·
            refine ⟨4046424598764566535373685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697616399176377690249123 4046424598764566535373685)
            ·
              refine ⟨379352306134178112691283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4046424598764566535373685 379352306134178112691283)
              ·
                refine ⟨569028459201267169036925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379352306134178112691283 569028459201267169036925)
                ·
                  refine ⟨213385672200475188388847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569028459201267169036925 213385672200475188388847)
                  ·
                    rfl

theorem cell20_467513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_467513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467513 prefixEnd_467513 := by exact prefixLift 467513
  have htrace : WordTrace (prefixWord ++ tailWord_467513) baseStart_467513 baseEnd_467513 := by
    simpa [prefixWord, tailWord_467513, baseEnd_467513] using wordTrace_append hprefix tailTrace_467513
  have hstable : (prefixWord ++ tailWord_467513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467513).length < 2 ^ (prefixWord ++ tailWord_467513).sum := by decide
  have hdescent : baseEnd_467513 < baseStart_467513 := by decide
  rcases family_descends (prefixWord ++ tailWord_467513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467527 : List Nat := [1, 1, 4, 1, 4, 1, 4, 4]
def baseStart_467527 : Nat := 118140960795 + 467527 * 2 ^ 59
def prefixEnd_467527 : Nat := 4983230072969 + 3 ^ 40 * 467527 * 2
def baseEnd_467527 : Nat := 71130687393984453974041

theorem tailTrace_467527 : CollatzResearch.WordTrace tailWord_467527 prefixEnd_467527 71130687393984453974041 := by
  unfold tailWord_467527
  simp only [CollatzResearch.WordTrace]
  refine ⟨17052110577237001099744835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11368073718158000733163223 17052110577237001099744835)
  ·
    refine ⟨25578165865855501649617253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17052110577237001099744835 25578165865855501649617253)
    ·
      refine ⟨4795906099847906559303235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25578165865855501649617253 4795906099847906559303235)
      ·
        refine ⟨7193859149771859838954853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4795906099847906559303235 7193859149771859838954853)
        ·
          refine ⟨1348848590582223719804035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7193859149771859838954853 1348848590582223719804035)
          ·
            refine ⟨2023272885873335579706053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348848590582223719804035 2023272885873335579706053)
            ·
              refine ⟨379363666101250421194885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2023272885873335579706053 379363666101250421194885)
              ·
                refine ⟨71130687393984453974041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379363666101250421194885 71130687393984453974041)
                ·
                  rfl

theorem cell20_467527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 4].length) (baseStart_467527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467527 prefixEnd_467527 := by exact prefixLift 467527
  have htrace : WordTrace (prefixWord ++ tailWord_467527) baseStart_467527 baseEnd_467527 := by
    simpa [prefixWord, tailWord_467527, baseEnd_467527] using wordTrace_append hprefix tailTrace_467527
  have hstable : (prefixWord ++ tailWord_467527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467527).length < 2 ^ (prefixWord ++ tailWord_467527).sum := by decide
  have hdescent : baseEnd_467527 < baseStart_467527 := by decide
  rcases family_descends (prefixWord ++ tailWord_467527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467537 : List Nat := [1, 2, 2, 1, 3, 5, 1, 3, 2]
def baseStart_467537 : Nat := 118140960795 + 467537 * 2 ^ 59
def prefixEnd_467537 : Nat := 4983230072969 + 3 ^ 40 * 467537 * 2
def baseEnd_467537 : Nat := 213396626454437771588749

theorem tailTrace_467537 : CollatzResearch.WordTrace tailWord_467537 prefixEnd_467537 213396626454437771588749 := by
  unfold tailWord_467537
  simp only [CollatzResearch.WordTrace]
  refine ⟨17052475307200772807608865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11368316871467181871739243 17052475307200772807608865)
  ·
    refine ⟨12789356480400579605706649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17052475307200772807608865 12789356480400579605706649)
    ·
      refine ⟨9592017360300434704279987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12789356480400579605706649 9592017360300434704279987)
      ·
        refine ⟨14388026040450652056419981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9592017360300434704279987 14388026040450652056419981)
        ·
          refine ⟨5395509765168994521157493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14388026040450652056419981 5395509765168994521157493)
          ·
            refine ⟨505829040484593236358515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5395509765168994521157493 505829040484593236358515)
            ·
              refine ⟨758743560726889854537773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505829040484593236358515 758743560726889854537773)
              ·
                refine ⟨284528835272583695451665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 758743560726889854537773 284528835272583695451665)
                ·
                  refine ⟨213396626454437771588749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284528835272583695451665 213396626454437771588749)
                  ·
                    rfl

theorem cell20_467537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 2].length) (baseStart_467537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467537 prefixEnd_467537 := by exact prefixLift 467537
  have htrace : WordTrace (prefixWord ++ tailWord_467537) baseStart_467537 baseEnd_467537 := by
    simpa [prefixWord, tailWord_467537, baseEnd_467537] using wordTrace_append hprefix tailTrace_467537
  have hstable : (prefixWord ++ tailWord_467537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467537).length < 2 ^ (prefixWord ++ tailWord_467537).sum := by decide
  have hdescent : baseEnd_467537 < baseStart_467537 := by decide
  rcases family_descends (prefixWord ++ tailWord_467537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467550 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_467550 : Nat := 118140960795 + 467550 * 2 ^ 59
def prefixEnd_467550 : Nat := 4983230072969 + 3 ^ 40 * 467550 * 2
def baseEnd_467550 : Nat := 213402560008667504155363

theorem tailTrace_467550 : CollatzResearch.WordTrace tailWord_467550 prefixEnd_467550 213402560008667504155363 := by
  unfold tailWord_467550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2131618682019209503479013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11368632970769117351888069 2131618682019209503479013)
  ·
    refine ⟨399678502878601781902315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2131618682019209503479013 399678502878601781902315)
    ·
      refine ⟨599517754317902672853473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399678502878601781902315 599517754317902672853473)
      ·
        refine ⟨449638315738427004640105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599517754317902672853473 449638315738427004640105)
        ·
          refine ⟨337228736803820253480079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449638315738427004640105 337228736803820253480079)
          ·
            refine ⟨505843105205730380220119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337228736803820253480079 505843105205730380220119)
            ·
              refine ⟨758764657808595570330179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505843105205730380220119 758764657808595570330179)
              ·
                refine ⟨1138146986712893355495269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758764657808595570330179 1138146986712893355495269)
                ·
                  refine ⟨213402560008667504155363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138146986712893355495269 213402560008667504155363)
                  ·
                    rfl

theorem cell20_467550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_467550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467550 prefixEnd_467550 := by exact prefixLift 467550
  have htrace : WordTrace (prefixWord ++ tailWord_467550) baseStart_467550 baseEnd_467550 := by
    simpa [prefixWord, tailWord_467550, baseEnd_467550] using wordTrace_append hprefix tailTrace_467550
  have hstable : (prefixWord ++ tailWord_467550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467550).length < 2 ^ (prefixWord ++ tailWord_467550).sum := by decide
  have hdescent : baseEnd_467550 < baseStart_467550 := by decide
  rcases family_descends (prefixWord ++ tailWord_467550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467554 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_467554 : Nat := 118140960795 + 467554 * 2 ^ 59
def prefixEnd_467554 : Nat := 4983230072969 + 3 ^ 40 * 467554 * 2
def baseEnd_467554 : Nat := 213404385717661268022013

theorem tailTrace_467554 : CollatzResearch.WordTrace tailWord_467554 prefixEnd_467554 213404385717661268022013 := by
  unfold tailWord_467554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4263273837034796177744429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11368730232092789807318477 4263273837034796177744429)
  ·
    refine ⟨1598727688888048566654161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4263273837034796177744429 1598727688888048566654161)
    ·
      refine ⟨1199045766666036424990621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1598727688888048566654161 1199045766666036424990621)
      ·
        refine ⟨449642162499763659371483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1199045766666036424990621 449642162499763659371483)
        ·
          refine ⟨674463243749645489057225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449642162499763659371483 674463243749645489057225)
          ·
            refine ⟨505847432812234116792919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674463243749645489057225 505847432812234116792919)
            ·
              refine ⟨758771149218351175189379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505847432812234116792919 758771149218351175189379)
              ·
                refine ⟨1138156723827526762784069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758771149218351175189379 1138156723827526762784069)
                ·
                  refine ⟨213404385717661268022013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138156723827526762784069 213404385717661268022013)
                  ·
                    rfl

theorem cell20_467554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_467554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467554 prefixEnd_467554 := by exact prefixLift 467554
  have htrace : WordTrace (prefixWord ++ tailWord_467554) baseStart_467554 baseEnd_467554 := by
    simpa [prefixWord, tailWord_467554, baseEnd_467554] using wordTrace_append hprefix tailTrace_467554
  have hstable : (prefixWord ++ tailWord_467554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467554).length < 2 ^ (prefixWord ++ tailWord_467554).sum := by decide
  have hdescent : baseEnd_467554 < baseStart_467554 := by decide
  rcases family_descends (prefixWord ++ tailWord_467554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467555 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_467555 : Nat := 118140960795 + 467555 * 2 ^ 59
def prefixEnd_467555 : Nat := 4983230072969 + 3 ^ 40 * 467555 * 2
def baseEnd_467555 : Nat := 213404842144909708988675

theorem tailTrace_467555 : CollatzResearch.WordTrace tailWord_467555 prefixEnd_467555 213404842144909708988675 := by
  unfold tailWord_467555
  simp only [CollatzResearch.WordTrace]
  refine ⟨17053131821135561881764119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11368754547423707921176079 17053131821135561881764119)
  ·
    refine ⟨25579697731703342822646179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17053131821135561881764119 25579697731703342822646179)
    ·
      refine ⟨38369546597555014233969269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25579697731703342822646179 38369546597555014233969269)
      ·
        refine ⟨3597144993520782584434619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38369546597555014233969269 3597144993520782584434619)
        ·
          refine ⟨5395717490281173876651929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597144993520782584434619 5395717490281173876651929)
          ·
            refine ⟨4046788117710880407488947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5395717490281173876651929 4046788117710880407488947)
            ·
              refine ⟨6070182176566320611233421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046788117710880407488947 6070182176566320611233421)
              ·
                refine ⟨2276318316212370229212533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6070182176566320611233421 2276318316212370229212533)
                ·
                  refine ⟨213404842144909708988675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2276318316212370229212533 213404842144909708988675)
                  ·
                    rfl

theorem cell20_467555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_467555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467555 prefixEnd_467555 := by exact prefixLift 467555
  have htrace : WordTrace (prefixWord ++ tailWord_467555) baseStart_467555 baseEnd_467555 := by
    simpa [prefixWord, tailWord_467555, baseEnd_467555] using wordTrace_append hprefix tailTrace_467555
  have hstable : (prefixWord ++ tailWord_467555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467555).length < 2 ^ (prefixWord ++ tailWord_467555).sum := by decide
  have hdescent : baseEnd_467555 < baseStart_467555 := by decide
  rcases family_descends (prefixWord ++ tailWord_467555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467565 : List Nat := [1, 5, 1, 1, 3, 2, 2, 5]
def baseStart_467565 : Nat := 118140960795 + 467565 * 2 ^ 59
def prefixEnd_467565 : Nat := 4983230072969 + 3 ^ 40 * 467565 * 2
def baseEnd_467565 : Nat := 71136468805798039551767

theorem tailTrace_467565 : CollatzResearch.WordTrace tailWord_467565 prefixEnd_467565 71136468805798039551767 := by
  unfold tailWord_467565
  simp only [CollatzResearch.WordTrace]
  refine ⟨17053496551099333589628149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11368997700732889059752099 17053496551099333589628149)
  ·
    refine ⟨1598765301665562524027639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17053496551099333589628149 1598765301665562524027639)
    ·
      refine ⟨2398147952498343786041459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1598765301665562524027639 2398147952498343786041459)
      ·
        refine ⟨3597221928747515679062189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2398147952498343786041459 3597221928747515679062189)
        ·
          refine ⟨1348958223280318379648321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3597221928747515679062189 1348958223280318379648321)
          ·
            refine ⟨1011718667460238784736241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1348958223280318379648321 1011718667460238784736241)
            ·
              refine ⟨758789000595179088552181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011718667460238784736241 758789000595179088552181)
              ·
                refine ⟨71136468805798039551767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 758789000595179088552181 71136468805798039551767)
                ·
                  rfl

theorem cell20_467565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_467565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467565 prefixEnd_467565 := by exact prefixLift 467565
  have htrace : WordTrace (prefixWord ++ tailWord_467565) baseStart_467565 baseEnd_467565 := by
    simpa [prefixWord, tailWord_467565, baseEnd_467565] using wordTrace_append hprefix tailTrace_467565
  have hstable : (prefixWord ++ tailWord_467565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467565).length < 2 ^ (prefixWord ++ tailWord_467565).sum := by decide
  have hdescent : baseEnd_467565 < baseStart_467565 := by decide
  rcases family_descends (prefixWord ++ tailWord_467565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467568 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 3]
def baseStart_467568 : Nat := 118140960795 + 467568 * 2 ^ 59
def prefixEnd_467568 : Nat := 4983230072969 + 3 ^ 40 * 467568 * 2
def baseEnd_467568 : Nat := 213410775699139441555289

theorem tailTrace_467568 : CollatzResearch.WordTrace tailWord_467568 prefixEnd_467568 213410775699139441555289 := by
  unfold tailWord_467568
  simp only [CollatzResearch.WordTrace]
  refine ⟨8526802985044232550993679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11369070646725643401324905 8526802985044232550993679)
  ·
    refine ⟨12790204477566348826490519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8526802985044232550993679 12790204477566348826490519)
    ·
      refine ⟨19185306716349523239735779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12790204477566348826490519 19185306716349523239735779)
      ·
        refine ⟨28777960074524284859603669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19185306716349523239735779 28777960074524284859603669)
        ·
          refine ⟨674483439246662926396961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 28777960074524284859603669 674483439246662926396961)
          ·
            refine ⟨505862579434997194797721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674483439246662926396961 505862579434997194797721)
            ·
              refine ⟨379396934576247896098291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505862579434997194797721 379396934576247896098291)
              ·
                refine ⟨569095401864371844147437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379396934576247896098291 569095401864371844147437)
                ·
                  refine ⟨213410775699139441555289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569095401864371844147437 213410775699139441555289)
                  ·
                    rfl

theorem cell20_467568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_467568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467568 prefixEnd_467568 := by exact prefixLift 467568
  have htrace : WordTrace (prefixWord ++ tailWord_467568) baseStart_467568 baseEnd_467568 := by
    simpa [prefixWord, tailWord_467568, baseEnd_467568] using wordTrace_append hprefix tailTrace_467568
  have hstable : (prefixWord ++ tailWord_467568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467568).length < 2 ^ (prefixWord ++ tailWord_467568).sum := by decide
  have hdescent : baseEnd_467568 < baseStart_467568 := by decide
  rcases family_descends (prefixWord ++ tailWord_467568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467613 : List Nat := [1, 4, 2, 1, 1, 1, 6, 2, 2]
def baseStart_467613 : Nat := 118140960795 + 467613 * 2 ^ 59
def prefixEnd_467613 : Nat := 4983230072969 + 3 ^ 40 * 467613 * 2
def baseEnd_467613 : Nat := 213431314925319285055105

theorem tailTrace_467613 : CollatzResearch.WordTrace tailWord_467613 prefixEnd_467613 213431314925319285055105 := by
  unfold tailWord_467613
  simp only [CollatzResearch.WordTrace]
  refine ⟨17055247254925437787375493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11370164836616958524916995 17055247254925437787375493)
  ·
    refine ⟨3197858860298519585132905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17055247254925437787375493 3197858860298519585132905)
    ·
      refine ⟨2398394145223889688849679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3197858860298519585132905 2398394145223889688849679)
      ·
        refine ⟨3597591217835834533274519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2398394145223889688849679 3597591217835834533274519)
        ·
          refine ⟨5396386826753751799911779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597591217835834533274519 5396386826753751799911779)
          ·
            refine ⟨8094580240130627699867669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5396386826753751799911779 8094580240130627699867669)
            ·
              refine ⟨379433448756123173431297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8094580240130627699867669 379433448756123173431297)
              ·
                refine ⟨284575086567092380073473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379433448756123173431297 284575086567092380073473)
                ·
                  refine ⟨213431314925319285055105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284575086567092380073473 213431314925319285055105)
                  ·
                    rfl

theorem cell20_467613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_467613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467613 prefixEnd_467613 := by exact prefixLift 467613
  have htrace : WordTrace (prefixWord ++ tailWord_467613) baseStart_467613 baseEnd_467613 := by
    simpa [prefixWord, tailWord_467613, baseEnd_467613] using wordTrace_append hprefix tailTrace_467613
  have hstable : (prefixWord ++ tailWord_467613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467613).length < 2 ^ (prefixWord ++ tailWord_467613).sum := by decide
  have hdescent : baseEnd_467613 < baseStart_467613 := by decide
  rcases family_descends (prefixWord ++ tailWord_467613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467661 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 3]
def baseStart_467661 : Nat := 118140960795 + 467661 * 2 ^ 59
def prefixEnd_467661 : Nat := 4983230072969 + 3 ^ 40 * 467661 * 2
def baseEnd_467661 : Nat := 213453223433244451454909

theorem tailTrace_467661 : CollatzResearch.WordTrace tailWord_467661 prefixEnd_467661 213453223433244451454909 := by
  unfold tailWord_467661
  simp only [CollatzResearch.WordTrace]
  refine ⟨17056997958751541985122837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11371331972501027990081891 17056997958751541985122837)
  ·
    refine ⟨799546779316478530552633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17056997958751541985122837 799546779316478530552633)
    ·
      refine ⟨599660084487358897914475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 799546779316478530552633 599660084487358897914475)
      ·
        refine ⟨899490126731038346871713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599660084487358897914475 899490126731038346871713)
        ·
          refine ⟨674617595048278760153785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899490126731038346871713 674617595048278760153785)
          ·
            refine ⟨505963196286209070115339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674617595048278760153785 505963196286209070115339)
            ·
              refine ⟨758944794429313605173009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505963196286209070115339 758944794429313605173009)
              ·
                refine ⟨569208595821985203879757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758944794429313605173009 569208595821985203879757)
                ·
                  refine ⟨213453223433244451454909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569208595821985203879757 213453223433244451454909)
                  ·
                    rfl

theorem cell20_467661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_467661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467661 prefixEnd_467661 := by exact prefixLift 467661
  have htrace : WordTrace (prefixWord ++ tailWord_467661) baseStart_467661 baseEnd_467661 := by
    simpa [prefixWord, tailWord_467661, baseEnd_467661] using wordTrace_append hprefix tailTrace_467661
  have hstable : (prefixWord ++ tailWord_467661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467661).length < 2 ^ (prefixWord ++ tailWord_467661).sum := by decide
  have hdescent : baseEnd_467661 < baseStart_467661 := by decide
  rcases family_descends (prefixWord ++ tailWord_467661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467662 : List Nat := [4, 1, 1, 1, 3, 3, 7]
def baseStart_467662 : Nat := 118140960795 + 467662 * 2 ^ 59
def prefixEnd_467662 : Nat := 4983230072969 + 3 ^ 40 * 467662 * 2
def baseEnd_467662 : Nat := 23717075540054765824619

theorem tailTrace_467662 : CollatzResearch.WordTrace tailWord_467662 prefixEnd_467662 23717075540054765824619 := by
  unfold tailWord_467662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132129303968489894488655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11371356287831946103939493 2132129303968489894488655)
  ·
    refine ⟨3198193955952734841732983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2132129303968489894488655 3198193955952734841732983)
    ·
      refine ⟨4797290933929102262599475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3198193955952734841732983 4797290933929102262599475)
      ·
        refine ⟨7195936400893653393899213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4797290933929102262599475 7195936400893653393899213)
        ·
          refine ⟨2698476150335120022712205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7195936400893653393899213 2698476150335120022712205)
          ·
            refine ⟨1011928556375670008517077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2698476150335120022712205 1011928556375670008517077)
            ·
              refine ⟨23717075540054765824619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1011928556375670008517077 23717075540054765824619)
              ·
                rfl

theorem cell20_467662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 7].length) (baseStart_467662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467662 prefixEnd_467662 := by exact prefixLift 467662
  have htrace : WordTrace (prefixWord ++ tailWord_467662) baseStart_467662 baseEnd_467662 := by
    simpa [prefixWord, tailWord_467662, baseEnd_467662] using wordTrace_append hprefix tailTrace_467662
  have hstable : (prefixWord ++ tailWord_467662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467662).length < 2 ^ (prefixWord ++ tailWord_467662).sum := by decide
  have hdescent : baseEnd_467662 < baseStart_467662 := by decide
  rcases family_descends (prefixWord ++ tailWord_467662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467672 : List Nat := [2, 1, 2, 2, 3, 2, 2, 4, 2]
def baseStart_467672 : Nat := 118140960795 + 467672 * 2 ^ 59
def prefixEnd_467672 : Nat := 4983230072969 + 3 ^ 40 * 467672 * 2
def baseEnd_467672 : Nat := 213458244132977302088197

theorem tailTrace_467672 : CollatzResearch.WordTrace tailWord_467672 prefixEnd_467672 213458244132977302088197 := by
  unfold tailWord_467672
  simp only [CollatzResearch.WordTrace]
  refine ⟨8528699580855845431886635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11371599441141127242515513 8528699580855845431886635)
  ·
    refine ⟨12793049371283768147829953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8528699580855845431886635 12793049371283768147829953)
    ·
      refine ⟨9594787028462826110872465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12793049371283768147829953 9594787028462826110872465)
      ·
        refine ⟨7196090271347119583154349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9594787028462826110872465 7196090271347119583154349)
        ·
          refine ⟨2698533851755169843682881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7196090271347119583154349 2698533851755169843682881)
          ·
            refine ⟨2023900388816377382762161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2698533851755169843682881 2023900388816377382762161)
            ·
              refine ⟨1517925291612283037071621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023900388816377382762161 1517925291612283037071621)
              ·
                refine ⟨284610992177303069450929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1517925291612283037071621 284610992177303069450929)
                ·
                  refine ⟨213458244132977302088197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284610992177303069450929 213458244132977302088197)
                  ·
                    rfl

theorem cell20_467672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 2].length) (baseStart_467672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467672 prefixEnd_467672 := by exact prefixLift 467672
  have htrace : WordTrace (prefixWord ++ tailWord_467672) baseStart_467672 baseEnd_467672 := by
    simpa [prefixWord, tailWord_467672, baseEnd_467672] using wordTrace_append hprefix tailTrace_467672
  have hstable : (prefixWord ++ tailWord_467672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467672).length < 2 ^ (prefixWord ++ tailWord_467672).sum := by decide
  have hdescent : baseEnd_467672 < baseStart_467672 := by decide
  rcases family_descends (prefixWord ++ tailWord_467672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467693 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 4]
def baseStart_467693 : Nat := 118140960795 + 467693 * 2 ^ 59
def prefixEnd_467693 : Nat := 4983230072969 + 3 ^ 40 * 467693 * 2
def baseEnd_467693 : Nat := 213467829105194562388111

theorem tailTrace_467693 : CollatzResearch.WordTrace tailWord_467693 prefixEnd_467693 213467829105194562388111 := by
  unfold tailWord_467693
  simp only [CollatzResearch.WordTrace]
  refine ⟨17058165094635611450287733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11372110063090407633525155 17058165094635611450287733)
  ·
    refine ⟨1599202977622088573464475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17058165094635611450287733 1599202977622088573464475)
    ·
      refine ⟨2398804466433132860196713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1599202977622088573464475 2398804466433132860196713)
      ·
        refine ⟨1799103349824849645147535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2398804466433132860196713 1799103349824849645147535)
        ·
          refine ⟨2698655024737274467721303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1799103349824849645147535 2698655024737274467721303)
          ·
            refine ⟨4047982537105911701581955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2698655024737274467721303 4047982537105911701581955)
            ·
              refine ⟨6071973805658867552372933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047982537105911701581955 6071973805658867552372933)
              ·
                refine ⟨1138495088561037666069925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6071973805658867552372933 1138495088561037666069925)
                ·
                  refine ⟨213467829105194562388111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138495088561037666069925 213467829105194562388111)
                  ·
                    rfl

theorem cell20_467693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_467693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467693 prefixEnd_467693 := by exact prefixLift 467693
  have htrace : WordTrace (prefixWord ++ tailWord_467693) baseStart_467693 baseEnd_467693 := by
    simpa [prefixWord, tailWord_467693, baseEnd_467693] using wordTrace_append hprefix tailTrace_467693
  have hstable : (prefixWord ++ tailWord_467693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467693).length < 2 ^ (prefixWord ++ tailWord_467693).sum := by decide
  have hdescent : baseEnd_467693 < baseStart_467693 := by decide
  rcases family_descends (prefixWord ++ tailWord_467693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467721 : List Nat := [1, 2, 1, 1, 3, 2, 10]
def baseStart_467721 : Nat := 118140960795 + 467721 * 2 ^ 59
def prefixEnd_467721 : Nat := 4983230072969 + 3 ^ 40 * 467721 * 2
def baseEnd_467721 : Nat := 23720067674238989939407

theorem tailTrace_467721 : CollatzResearch.WordTrace tailWord_467721 prefixEnd_467721 23720067674238989939407 := by
  unfold tailWord_467721
  simp only [CollatzResearch.WordTrace]
  refine ⟨17059186338534172232307017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11372790892356114821538011 17059186338534172232307017)
  ·
    refine ⟨12794389753900629174230263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17059186338534172232307017 12794389753900629174230263)
    ·
      refine ⟨19191584630850943761345395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12794389753900629174230263 19191584630850943761345395)
      ·
        refine ⟨28787376946276415642018093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19191584630850943761345395 28787376946276415642018093)
        ·
          refine ⟨10795266354853655865756785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28787376946276415642018093 10795266354853655865756785)
          ·
            refine ⟨8096449766140241899317589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10795266354853655865756785 8096449766140241899317589)
            ·
              refine ⟨23720067674238989939407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8096449766140241899317589 23720067674238989939407)
              ·
                rfl

theorem cell20_467721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 10].length) (baseStart_467721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467721 prefixEnd_467721 := by exact prefixLift 467721
  have htrace : WordTrace (prefixWord ++ tailWord_467721) baseStart_467721 baseEnd_467721 := by
    simpa [prefixWord, tailWord_467721, baseEnd_467721] using wordTrace_append hprefix tailTrace_467721
  have hstable : (prefixWord ++ tailWord_467721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467721).length < 2 ^ (prefixWord ++ tailWord_467721).sum := by decide
  have hdescent : baseEnd_467721 < baseStart_467721 := by decide
  rcases family_descends (prefixWord ++ tailWord_467721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467738 : List Nat := [3, 1, 1, 3, 2, 1, 4, 5]
def baseStart_467738 : Nat := 118140960795 + 467738 * 2 ^ 59
def prefixEnd_467738 : Nat := 4983230072969 + 3 ^ 40 * 467738 * 2
def baseEnd_467738 : Nat := 71162789443791468629309

theorem tailTrace_467738 : CollatzResearch.WordTrace tailWord_467738 prefixEnd_467738 71162789443791468629309 := by
  unfold tailWord_467738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4264951594868146033918967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11373204252981722757117245 4264951594868146033918967)
  ·
    refine ⟨6397427392302219050878451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4264951594868146033918967 6397427392302219050878451)
    ·
      refine ⟨9596141088453328576317677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6397427392302219050878451 9596141088453328576317677)
      ·
        refine ⟨3598552908169998216119129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9596141088453328576317677 3598552908169998216119129)
        ·
          refine ⟨2698914681127498662089347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3598552908169998216119129 2698914681127498662089347)
          ·
            refine ⟨4048372021691247993134021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2698914681127498662089347 4048372021691247993134021)
            ·
              refine ⟨759069754067108998712629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4048372021691247993134021 759069754067108998712629)
              ·
                refine ⟨71162789443791468629309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 759069754067108998712629 71162789443791468629309)
                ·
                  rfl

theorem cell20_467738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_467738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467738 prefixEnd_467738 := by exact prefixLift 467738
  have htrace : WordTrace (prefixWord ++ tailWord_467738) baseStart_467738 baseEnd_467738 := by
    simpa [prefixWord, tailWord_467738, baseEnd_467738] using wordTrace_append hprefix tailTrace_467738
  have hstable : (prefixWord ++ tailWord_467738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467738).length < 2 ^ (prefixWord ++ tailWord_467738).sum := by decide
  have hdescent : baseEnd_467738 < baseStart_467738 := by decide
  rcases family_descends (prefixWord ++ tailWord_467738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467789 : List Nat := [1, 6, 1, 2, 3, 1, 1, 5]
def baseStart_467789 : Nat := 118140960795 + 467789 * 2 ^ 59
def prefixEnd_467789 : Nat := 4983230072969 + 3 ^ 40 * 467789 * 2
def baseEnd_467789 : Nat := 71170548707014965062573

theorem tailTrace_467789 : CollatzResearch.WordTrace tailWord_467789 prefixEnd_467789 71170548707014965062573 := by
  unfold tailWord_467789
  simp only [CollatzResearch.WordTrace]
  refine ⟨17061666502287819845782421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11374444334858546563854947 17061666502287819845782421)
  ·
    refine ⟨799765617294741555271051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17061666502287819845782421 799765617294741555271051)
    ·
      refine ⟨1199648425942112332906577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799765617294741555271051 1199648425942112332906577)
      ·
        refine ⟨899736319456584249679933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1199648425942112332906577 899736319456584249679933)
        ·
          refine ⟨337401119796219093629975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 899736319456584249679933 337401119796219093629975)
          ·
            refine ⟨506101679694328640444963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337401119796219093629975 506101679694328640444963)
            ·
              refine ⟨759152519541492960667445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506101679694328640444963 759152519541492960667445)
              ·
                refine ⟨71170548707014965062573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 759152519541492960667445 71170548707014965062573)
                ·
                  rfl

theorem cell20_467789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 5].length) (baseStart_467789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467789 prefixEnd_467789 := by exact prefixLift 467789
  have htrace : WordTrace (prefixWord ++ tailWord_467789) baseStart_467789 baseEnd_467789 := by
    simpa [prefixWord, tailWord_467789, baseEnd_467789] using wordTrace_append hprefix tailTrace_467789
  have hstable : (prefixWord ++ tailWord_467789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467789).length < 2 ^ (prefixWord ++ tailWord_467789).sum := by decide
  have hdescent : baseEnd_467789 < baseStart_467789 := by decide
  rcases family_descends (prefixWord ++ tailWord_467789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467790 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_467790 : Nat := 118140960795 + 467790 * 2 ^ 59
def prefixEnd_467790 : Nat := 4983230072969 + 3 ^ 40 * 467790 * 2
def baseEnd_467790 : Nat := 213512102548293336154381

theorem tailTrace_467790 : CollatzResearch.WordTrace tailWord_467790 prefixEnd_467790 213512102548293336154381 := by
  unfold tailWord_467790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132712871910524627071103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11374468650189464677712549 2132712871910524627071103)
  ·
    refine ⟨3199069307865786940606655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2132712871910524627071103 3199069307865786940606655)
    ·
      refine ⟨4798603961798680410909983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3199069307865786940606655 4798603961798680410909983)
      ·
        refine ⟨7197905942698020616364975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4798603961798680410909983 7197905942698020616364975)
        ·
          refine ⟨10796858914047030924547463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7197905942698020616364975 10796858914047030924547463)
          ·
            refine ⟨16195288371070546386821195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10796858914047030924547463 16195288371070546386821195)
            ·
              refine ⟨24292932556605819580231793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16195288371070546386821195 24292932556605819580231793)
              ·
                refine ⟨18219699417454364685173845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24292932556605819580231793 18219699417454364685173845)
                ·
                  refine ⟨213512102548293336154381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18219699417454364685173845 213512102548293336154381)
                  ·
                    rfl

theorem cell20_467790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_467790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467790 prefixEnd_467790 := by exact prefixLift 467790
  have htrace : WordTrace (prefixWord ++ tailWord_467790) baseStart_467790 baseEnd_467790 := by
    simpa [prefixWord, tailWord_467790, baseEnd_467790] using wordTrace_append hprefix tailTrace_467790
  have hstable : (prefixWord ++ tailWord_467790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467790).length < 2 ^ (prefixWord ++ tailWord_467790).sum := by decide
  have hdescent : baseEnd_467790 < baseStart_467790 := by decide
  rcases family_descends (prefixWord ++ tailWord_467790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467793 : List Nat := [1, 2, 2, 1, 6, 2, 1, 5]
def baseStart_467793 : Nat := 118140960795 + 467793 * 2 ^ 59
def prefixEnd_467793 : Nat := 4983230072969 + 3 ^ 40 * 467793 * 2
def baseEnd_467793 : Nat := 71171157276679553018123

theorem tailTrace_467793 : CollatzResearch.WordTrace tailWord_467793 prefixEnd_467793 71171157276679553018123 := by
  unfold tailWord_467793
  simp only [CollatzResearch.WordTrace]
  refine ⟨17061812394273328528928033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11374541596182219019285355 17061812394273328528928033)
  ·
    refine ⟨12796359295704996396696025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17061812394273328528928033 12796359295704996396696025)
    ·
      refine ⟨9597269471778747297522019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12796359295704996396696025 9597269471778747297522019)
      ·
        refine ⟨14395904207668120946283029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9597269471778747297522019 14395904207668120946283029)
        ·
          refine ⟨674808009734443169357017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14395904207668120946283029 674808009734443169357017)
          ·
            refine ⟨506106007300832377017763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674808009734443169357017 506106007300832377017763)
            ·
              refine ⟨759159010951248565526645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506106007300832377017763 759159010951248565526645)
              ·
                refine ⟨71171157276679553018123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 759159010951248565526645 71171157276679553018123)
                ·
                  rfl

theorem cell20_467793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 5].length) (baseStart_467793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467793 prefixEnd_467793 := by exact prefixLift 467793
  have htrace : WordTrace (prefixWord ++ tailWord_467793) baseStart_467793 baseEnd_467793 := by
    simpa [prefixWord, tailWord_467793, baseEnd_467793] using wordTrace_append hprefix tailTrace_467793
  have hstable : (prefixWord ++ tailWord_467793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467793).length < 2 ^ (prefixWord ++ tailWord_467793).sum := by decide
  have hdescent : baseEnd_467793 < baseStart_467793 := by decide
  rcases family_descends (prefixWord ++ tailWord_467793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467810 : List Nat := [3, 3, 2, 1, 3, 1, 3, 4]
def baseStart_467810 : Nat := 118140960795 + 467810 * 2 ^ 59
def prefixEnd_467810 : Nat := 4983230072969 + 3 ^ 40 * 467810 * 2
def baseEnd_467810 : Nat := 71173743697754051829211

theorem tailTrace_467810 : CollatzResearch.WordTrace tailWord_467810 prefixEnd_467810 71173743697754051829211 := by
  unfold tailWord_467810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4265608108802935108074221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11374954956807826954864589 4265608108802935108074221)
  ·
    refine ⟨1599603040801100665527833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4265608108802935108074221 1599603040801100665527833)
    ·
      refine ⟨1199702280600825499145875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1599603040801100665527833 1199702280600825499145875)
      ·
        refine ⟨1799553420901238248718813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199702280600825499145875 1799553420901238248718813)
        ·
          refine ⟨674832532837964343269555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1799553420901238248718813 674832532837964343269555)
          ·
            refine ⟨1012248799256946514904333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674832532837964343269555 1012248799256946514904333)
            ·
              refine ⟨379593299721354943089125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1012248799256946514904333 379593299721354943089125)
              ·
                refine ⟨71173743697754051829211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379593299721354943089125 71173743697754051829211)
                ·
                  rfl

theorem cell20_467810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_467810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467810 prefixEnd_467810 := by exact prefixLift 467810
  have htrace : WordTrace (prefixWord ++ tailWord_467810) baseStart_467810 baseEnd_467810 := by
    simpa [prefixWord, tailWord_467810, baseEnd_467810] using wordTrace_append hprefix tailTrace_467810
  have hstable : (prefixWord ++ tailWord_467810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467810).length < 2 ^ (prefixWord ++ tailWord_467810).sum := by decide
  have hdescent : baseEnd_467810 < baseStart_467810 := by decide
  rcases family_descends (prefixWord ++ tailWord_467810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467821 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 5]
def baseStart_467821 : Nat := 118140960795 + 467821 * 2 ^ 59
def prefixEnd_467821 : Nat := 4983230072969 + 3 ^ 40 * 467821 * 2
def baseEnd_467821 : Nat := 213526251792995006120921

theorem tailTrace_467821 : CollatzResearch.WordTrace tailWord_467821 prefixEnd_467821 213526251792995006120921 := by
  unfold tailWord_467821
  simp only [CollatzResearch.WordTrace]
  refine ⟨17062833638171889310947317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11375222425447926207298211 17062833638171889310947317)
  ·
    refine ⟨1599640653578614622901311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17062833638171889310947317 1599640653578614622901311)
    ·
      refine ⟨2399460980367921934351967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1599640653578614622901311 2399460980367921934351967)
      ·
        refine ⟨3599191470551882901527951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399460980367921934351967 3599191470551882901527951)
        ·
          refine ⟨5398787205827824352291927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3599191470551882901527951 5398787205827824352291927)
          ·
            refine ⟨8098180808741736528437891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5398787205827824352291927 8098180808741736528437891)
            ·
              refine ⟨12147271213112604792656837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8098180808741736528437891 12147271213112604792656837)
              ·
                refine ⟨2277613352458613398623157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12147271213112604792656837 2277613352458613398623157)
                ·
                  refine ⟨213526251792995006120921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2277613352458613398623157 213526251792995006120921)
                  ·
                    rfl

theorem cell20_467821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_467821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467821 prefixEnd_467821 := by exact prefixLift 467821
  have htrace : WordTrace (prefixWord ++ tailWord_467821) baseStart_467821 baseEnd_467821 := by
    simpa [prefixWord, tailWord_467821, baseEnd_467821] using wordTrace_append hprefix tailTrace_467821
  have hstable : (prefixWord ++ tailWord_467821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467821).length < 2 ^ (prefixWord ++ tailWord_467821).sum := by decide
  have hdescent : baseEnd_467821 < baseStart_467821 := by decide
  rcases family_descends (prefixWord ++ tailWord_467821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467845 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 4]
def baseStart_467845 : Nat := 118140960795 + 467845 * 2 ^ 59
def prefixEnd_467845 : Nat := 4983230072969 + 3 ^ 40 * 467845 * 2
def baseEnd_467845 : Nat := 213537206046957589320823

theorem tailTrace_467845 : CollatzResearch.WordTrace tailWord_467845 prefixEnd_467845 213537206046957589320823 := by
  unfold tailWord_467845
  simp only [CollatzResearch.WordTrace]
  refine ⟨17063708990084941409820989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11375805993389960939880659 17063708990084941409820989)
  ·
    refine ⟨6398890871281853028682871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17063708990084941409820989 6398890871281853028682871)
    ·
      refine ⟨9598336306922779543024307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6398890871281853028682871 9598336306922779543024307)
      ·
        refine ⟨14397504460384169314536461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9598336306922779543024307 14397504460384169314536461)
        ·
          refine ⟨5399064172644063492951173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14397504460384169314536461 5399064172644063492951173)
          ·
            refine ⟨1012324532370761904928345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5399064172644063492951173 1012324532370761904928345)
            ·
              refine ⟨759243399278071428696259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1012324532370761904928345 759243399278071428696259)
              ·
                refine ⟨1138865098917107143044389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759243399278071428696259 1138865098917107143044389)
                ·
                  refine ⟨213537206046957589320823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1138865098917107143044389 213537206046957589320823)
                  ·
                    rfl

theorem cell20_467845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_467845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467845 prefixEnd_467845 := by exact prefixLift 467845
  have htrace : WordTrace (prefixWord ++ tailWord_467845) baseStart_467845 baseEnd_467845 := by
    simpa [prefixWord, tailWord_467845, baseEnd_467845] using wordTrace_append hprefix tailTrace_467845
  have hstable : (prefixWord ++ tailWord_467845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467845).length < 2 ^ (prefixWord ++ tailWord_467845).sum := by decide
  have hdescent : baseEnd_467845 < baseStart_467845 := by decide
  rcases family_descends (prefixWord ++ tailWord_467845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467897 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 5]
def baseStart_467897 : Nat := 118140960795 + 467897 * 2 ^ 59
def prefixEnd_467897 : Nat := 4983230072969 + 3 ^ 40 * 467897 * 2
def baseEnd_467897 : Nat := 213560940263876519587277

theorem tailTrace_467897 : CollatzResearch.WordTrace tailWord_467897 prefixEnd_467897 213560940263876519587277 := by
  unfold tailWord_467897
  simp only [CollatzResearch.WordTrace]
  refine ⟨17065605585896554290713945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11377070390597702860475963 17065605585896554290713945)
  ·
    refine ⟨12799204189422415718035459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17065605585896554290713945 12799204189422415718035459)
    ·
      refine ⟨19198806284133623577053189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12799204189422415718035459 19198806284133623577053189)
      ·
        refine ⟨3599776178275054420697473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19198806284133623577053189 3599776178275054420697473)
        ·
          refine ⟨2699832133706290815523105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3599776178275054420697473 2699832133706290815523105)
          ·
            refine ⟨2024874100279718111642329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2699832133706290815523105 2024874100279718111642329)
            ·
              refine ⟨1518655575209788583731747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2024874100279718111642329 1518655575209788583731747)
              ·
                refine ⟨2277983362814682875597621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518655575209788583731747 2277983362814682875597621)
                ·
                  refine ⟨213560940263876519587277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2277983362814682875597621 213560940263876519587277)
                  ·
                    rfl

theorem cell20_467897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_467897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467897 prefixEnd_467897 := by exact prefixLift 467897
  have htrace : WordTrace (prefixWord ++ tailWord_467897) baseStart_467897 baseEnd_467897 := by
    simpa [prefixWord, tailWord_467897, baseEnd_467897] using wordTrace_append hprefix tailTrace_467897
  have hstable : (prefixWord ++ tailWord_467897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467897).length < 2 ^ (prefixWord ++ tailWord_467897).sum := by decide
  have hdescent : baseEnd_467897 < baseStart_467897 := by decide
  rcases family_descends (prefixWord ++ tailWord_467897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467911 : List Nat := [1, 1, 4, 1, 1, 2, 3, 7]
def baseStart_467911 : Nat := 118140960795 + 467911 * 2 ^ 59
def prefixEnd_467911 : Nat := 4983230072969 + 3 ^ 40 * 467911 * 2
def baseEnd_467911 : Nat := 71189110081784897706851

theorem tailTrace_467911 : CollatzResearch.WordTrace tailWord_467911 prefixEnd_467911 71189110081784897706851 := by
  unfold tailWord_467911
  simp only [CollatzResearch.WordTrace]
  refine ⟨17066116207845834681723587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11377410805230556454482391 17066116207845834681723587)
  ·
    refine ⟨25599174311768752022585381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17066116207845834681723587 25599174311768752022585381)
    ·
      refine ⟨4799845183456641004234759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25599174311768752022585381 4799845183456641004234759)
      ·
        refine ⟨7199767775184961506352139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4799845183456641004234759 7199767775184961506352139)
        ·
          refine ⟨10799651662777442259528209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7199767775184961506352139 10799651662777442259528209)
          ·
            refine ⟨8099738747083081694646157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10799651662777442259528209 8099738747083081694646157)
            ·
              refine ⟨3037402030156155635492309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8099738747083081694646157 3037402030156155635492309)
              ·
                refine ⟨71189110081784897706851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3037402030156155635492309 71189110081784897706851)
                ·
                  rfl

theorem cell20_467911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_467911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467911 prefixEnd_467911 := by exact prefixLift 467911
  have htrace : WordTrace (prefixWord ++ tailWord_467911) baseStart_467911 baseEnd_467911 := by
    simpa [prefixWord, tailWord_467911, baseEnd_467911] using wordTrace_append hprefix tailTrace_467911
  have hstable : (prefixWord ++ tailWord_467911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467911).length < 2 ^ (prefixWord ++ tailWord_467911).sum := by decide
  have hdescent : baseEnd_467911 < baseStart_467911 := by decide
  rcases family_descends (prefixWord ++ tailWord_467911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467949 : List Nat := [1, 5, 1, 13]
def baseStart_467949 : Nat := 118140960795 + 467949 * 2 ^ 59
def prefixEnd_467949 : Nat := 4983230072969 + 3 ^ 40 * 467949 * 2
def baseEnd_467949 : Nat := 878949277698746707217

theorem tailTrace_467949 : CollatzResearch.WordTrace tailWord_467949 prefixEnd_467949 878949277698746707217 := by
  unfold tailWord_467949
  simp only [CollatzResearch.WordTrace]
  refine ⟨17067502181708167171606901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11378334787805444781071267 17067502181708167171606901)
  ·
    refine ⟨1600078329535140672338147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17067502181708167171606901 1600078329535140672338147)
    ·
      refine ⟨2400117494302711008507221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600078329535140672338147 2400117494302711008507221)
      ·
        refine ⟨878949277698746707217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2400117494302711008507221 878949277698746707217)
        ·
          rfl

theorem cell20_467949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 13].length) (baseStart_467949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467949 prefixEnd_467949 := by exact prefixLift 467949
  have htrace : WordTrace (prefixWord ++ tailWord_467949) baseStart_467949 baseEnd_467949 := by
    simpa [prefixWord, tailWord_467949, baseEnd_467949] using wordTrace_append hprefix tailTrace_467949
  have hstable : (prefixWord ++ tailWord_467949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467949).length < 2 ^ (prefixWord ++ tailWord_467949).sum := by decide
  have hdescent : baseEnd_467949 < baseStart_467949 := by decide
  rcases family_descends (prefixWord ++ tailWord_467949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467973 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 3]
def baseStart_467973 : Nat := 118140960795 + 467973 * 2 ^ 59
def prefixEnd_467973 : Nat := 4983230072969 + 3 ^ 40 * 467973 * 2
def baseEnd_467973 : Nat := 213595628734758033053633

theorem tailTrace_467973 : CollatzResearch.WordTrace tailWord_467973 prefixEnd_467973 213595628734758033053633 := by
  unfold tailWord_467973
  simp only [CollatzResearch.WordTrace]
  refine ⟨17068377533621219270480573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11378918355747479513653715 17068377533621219270480573)
  ·
    refine ⟨6400641575107957226430215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17068377533621219270480573 6400641575107957226430215)
    ·
      refine ⟨9600962362661935839645323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6400641575107957226430215 9600962362661935839645323)
      ·
        refine ⟨14401443543992903759467985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9600962362661935839645323 14401443543992903759467985)
        ·
          refine ⟨10801082657994677819600989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14401443543992903759467985 10801082657994677819600989)
          ·
            refine ⟨4050405996748004182350371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10801082657994677819600989 4050405996748004182350371)
            ·
              refine ⟨6075608995122006273525557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050405996748004182350371 6075608995122006273525557)
              ·
                refine ⟨569588343292688088143021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6075608995122006273525557 569588343292688088143021)
                ·
                  refine ⟨213595628734758033053633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569588343292688088143021 213595628734758033053633)
                  ·
                    rfl

theorem cell20_467973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_467973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467973 prefixEnd_467973 := by exact prefixLift 467973
  have htrace : WordTrace (prefixWord ++ tailWord_467973) baseStart_467973 baseEnd_467973 := by
    simpa [prefixWord, tailWord_467973, baseEnd_467973] using wordTrace_append hprefix tailTrace_467973
  have hstable : (prefixWord ++ tailWord_467973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467973).length < 2 ^ (prefixWord ++ tailWord_467973).sum := by decide
  have hdescent : baseEnd_467973 < baseStart_467973 := by decide
  rcases family_descends (prefixWord ++ tailWord_467973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467980 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_467980 : Nat := 118140960795 + 467980 * 2 ^ 59
def prefixEnd_467980 : Nat := 4983230072969 + 3 ^ 40 * 467980 * 2
def baseEnd_467980 : Nat := 213598823725497119820271

theorem tailTrace_467980 : CollatzResearch.WordTrace tailWord_467980 prefixEnd_467980 213598823725497119820271 := by
  unfold tailWord_467980
  simp only [CollatzResearch.WordTrace]
  refine ⟨8534316422297929732992697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11379088563063906310656929 8534316422297929732992697)
  ·
    refine ⟨6400737316723447299744523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8534316422297929732992697 6400737316723447299744523)
    ·
      refine ⟨9601105975085170949616785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6400737316723447299744523 9601105975085170949616785)
      ·
        refine ⟨7200829481313878212212589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9601105975085170949616785 7200829481313878212212589)
        ·
          refine ⟨2700311055492704329579721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7200829481313878212212589 2700311055492704329579721)
          ·
            refine ⟨2025233291619528247184791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2700311055492704329579721 2025233291619528247184791)
            ·
              refine ⟨3037849937429292370777187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025233291619528247184791 3037849937429292370777187)
              ·
                refine ⟨4556774906143938556165781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037849937429292370777187 4556774906143938556165781)
                ·
                  refine ⟨213598823725497119820271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4556774906143938556165781 213598823725497119820271)
                  ·
                    rfl

theorem cell20_467980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_467980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_467980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_467980 prefixEnd_467980 := by exact prefixLift 467980
  have htrace : WordTrace (prefixWord ++ tailWord_467980) baseStart_467980 baseEnd_467980 := by
    simpa [prefixWord, tailWord_467980, baseEnd_467980] using wordTrace_append hprefix tailTrace_467980
  have hstable : (prefixWord ++ tailWord_467980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467980).length < 2 ^ (prefixWord ++ tailWord_467980).sum := by decide
  have hdescent : baseEnd_467980 < baseStart_467980 := by decide
  rcases family_descends (prefixWord ++ tailWord_467980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468004 : List Nat := [2, 3, 1, 4, 1, 2, 7]
def baseStart_468004 : Nat := 118140960795 + 468004 * 2 ^ 59
def prefixEnd_468004 : Nat := 4983230072969 + 3 ^ 40 * 468004 * 2
def baseEnd_468004 : Nat := 23734419775495522557797

theorem tailTrace_468004 : CollatzResearch.WordTrace tailWord_468004 prefixEnd_468004 23734419775495522557797 := by
  unfold tailWord_468004
  simp only [CollatzResearch.WordTrace]
  refine ⟨8534754098254455782429533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11379672131005941043239377 8534754098254455782429533)
  ·
    refine ⟨3200532786845420918411075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8534754098254455782429533 3200532786845420918411075)
    ·
      refine ⟨4800799180268131377616613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200532786845420918411075 4800799180268131377616613)
      ·
        refine ⟨900149846300274633303115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4800799180268131377616613 900149846300274633303115)
        ·
          refine ⟨1350224769450411949954673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900149846300274633303115 1350224769450411949954673)
          ·
            refine ⟨1012668577087808962466005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350224769450411949954673 1012668577087808962466005)
            ·
              refine ⟨23734419775495522557797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1012668577087808962466005 23734419775495522557797)
              ·
                rfl

theorem cell20_468004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 7].length) (baseStart_468004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468004 prefixEnd_468004 := by exact prefixLift 468004
  have htrace : WordTrace (prefixWord ++ tailWord_468004) baseStart_468004 baseEnd_468004 := by
    simpa [prefixWord, tailWord_468004, baseEnd_468004] using wordTrace_append hprefix tailTrace_468004
  have hstable : (prefixWord ++ tailWord_468004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468004).length < 2 ^ (prefixWord ++ tailWord_468004).sum := by decide
  have hdescent : baseEnd_468004 < baseStart_468004 := by decide
  rcases family_descends (prefixWord ++ tailWord_468004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468007 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 3]
def baseStart_468007 : Nat := 118140960795 + 468007 * 2 ^ 59
def prefixEnd_468007 : Nat := 4983230072969 + 3 ^ 40 * 468007 * 2
def baseEnd_468007 : Nat := 213611147261205025920161

theorem tailTrace_468007 : CollatzResearch.WordTrace tailWord_468007 prefixEnd_468007 213611147261205025920161 := by
  unfold tailWord_468007
  simp only [CollatzResearch.WordTrace]
  refine ⟨17069617615498043077218275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11379745076998695384812183 17069617615498043077218275)
  ·
    refine ⟨25604426423247064615827413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17069617615498043077218275 25604426423247064615827413)
    ·
      refine ⟨600103744294853076933455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 25604426423247064615827413 600103744294853076933455)
      ·
        refine ⟨900155616442279615400183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600103744294853076933455 900155616442279615400183)
        ·
          refine ⟨1350233424663419423100275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900155616442279615400183 1350233424663419423100275)
          ·
            refine ⟨2025350136995129134650413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350233424663419423100275 2025350136995129134650413)
            ·
              refine ⟨759506301373173425493905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2025350136995129134650413 759506301373173425493905)
              ·
                refine ⟨569629726029880069120429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759506301373173425493905 569629726029880069120429)
                ·
                  refine ⟨213611147261205025920161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569629726029880069120429 213611147261205025920161)
                  ·
                    rfl

theorem cell20_468007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 3].length) (baseStart_468007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468007 prefixEnd_468007 := by exact prefixLift 468007
  have htrace : WordTrace (prefixWord ++ tailWord_468007) baseStart_468007 baseEnd_468007 := by
    simpa [prefixWord, tailWord_468007, baseEnd_468007] using wordTrace_append hprefix tailTrace_468007
  have hstable : (prefixWord ++ tailWord_468007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468007).length < 2 ^ (prefixWord ++ tailWord_468007).sum := by decide
  have hdescent : baseEnd_468007 < baseStart_468007 := by decide
  rcases family_descends (prefixWord ++ tailWord_468007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468014 : List Nat := [4, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_468014 : Nat := 118140960795 + 468014 * 2 ^ 59
def prefixEnd_468014 : Nat := 4983230072969 + 3 ^ 40 * 468014 * 2
def baseEnd_468014 : Nat := 213614342251944112686799

theorem tailTrace_468014 : CollatzResearch.WordTrace tailWord_468014 prefixEnd_468014 213614342251944112686799 := by
  unfold tailWord_468014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133734115809085409090387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11379915284315122181815397 2133734115809085409090387)
  ·
    refine ⟨3200601173713628113635581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2133734115809085409090387 3200601173713628113635581)
    ·
      refine ⟨1200225440142610542613343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3200601173713628113635581 1200225440142610542613343)
      ·
        refine ⟨1800338160213915813920015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200225440142610542613343 1800338160213915813920015)
        ·
          refine ⟨2700507240320873720880023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800338160213915813920015 2700507240320873720880023)
          ·
            refine ⟨4050760860481310581320035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700507240320873720880023 4050760860481310581320035)
            ·
              refine ⟨6076141290721965871980053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050760860481310581320035 6076141290721965871980053)
              ·
                refine ⟨284819123002592150249065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6076141290721965871980053 284819123002592150249065)
                ·
                  refine ⟨213614342251944112686799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284819123002592150249065 213614342251944112686799)
                  ·
                    rfl

theorem cell20_468014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_468014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468014 prefixEnd_468014 := by exact prefixLift 468014
  have htrace : WordTrace (prefixWord ++ tailWord_468014) baseStart_468014 baseEnd_468014 := by
    simpa [prefixWord, tailWord_468014, baseEnd_468014] using wordTrace_append hprefix tailTrace_468014
  have hstable : (prefixWord ++ tailWord_468014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468014).length < 2 ^ (prefixWord ++ tailWord_468014).sum := by decide
  have hdescent : baseEnd_468014 < baseStart_468014 := by decide
  rcases family_descends (prefixWord ++ tailWord_468014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468038 : List Nat := [6, 1, 1, 1, 1, 2, 4, 4]
def baseStart_468038 : Nat := 118140960795 + 468038 * 2 ^ 59
def prefixEnd_468038 : Nat := 4983230072969 + 3 ^ 40 * 468038 * 2
def baseEnd_468038 : Nat := 71208432168635565295567

theorem tailTrace_468038 : CollatzResearch.WordTrace tailWord_468038 prefixEnd_468038 71208432168635565295567 := by
  unfold tailWord_468038
  simp only [CollatzResearch.WordTrace]
  refine ⟨533460883699554230362399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11380498852257156914397845 533460883699554230362399)
  ·
    refine ⟨800191325549331345543599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 533460883699554230362399 800191325549331345543599)
    ·
      refine ⟨1200286988323997018315399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 800191325549331345543599 1200286988323997018315399)
      ·
        refine ⟨1800430482485995527473099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200286988323997018315399 1800430482485995527473099)
        ·
          refine ⟨2700645723728993291209649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800430482485995527473099 2700645723728993291209649)
          ·
            refine ⟨2025484292796744968407237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2700645723728993291209649 2025484292796744968407237)
            ·
              refine ⟨379778304899389681576357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2025484292796744968407237 379778304899389681576357)
              ·
                refine ⟨71208432168635565295567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379778304899389681576357 71208432168635565295567)
                ·
                  rfl

theorem cell20_468038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_468038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468038 prefixEnd_468038 := by exact prefixLift 468038
  have htrace : WordTrace (prefixWord ++ tailWord_468038) baseStart_468038 baseEnd_468038 := by
    simpa [prefixWord, tailWord_468038, baseEnd_468038] using wordTrace_append hprefix tailTrace_468038
  have hstable : (prefixWord ++ tailWord_468038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468038).length < 2 ^ (prefixWord ++ tailWord_468038).sum := by decide
  have hdescent : baseEnd_468038 < baseStart_468038 := by decide
  rcases family_descends (prefixWord ++ tailWord_468038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468042 : List Nat := [3, 1, 2, 1, 1, 2, 6, 4]
def baseStart_468042 : Nat := 118140960795 + 468042 * 2 ^ 59
def prefixEnd_468042 : Nat := 4983230072969 + 3 ^ 40 * 468042 * 2
def baseEnd_468042 : Nat := 71209040738300153251117

theorem tailTrace_468042 : CollatzResearch.WordTrace tailWord_468042 prefixEnd_468042 71209040738300153251117 := by
  unfold tailWord_468042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4267723542592811013685595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11380596113580829369828253 4267723542592811013685595)
  ·
    refine ⟨6401585313889216520528393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4267723542592811013685595 6401585313889216520528393)
    ·
      refine ⟨4801188985416912390396295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6401585313889216520528393 4801188985416912390396295)
      ·
        refine ⟨7201783478125368585594443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4801188985416912390396295 7201783478125368585594443)
        ·
          refine ⟨10802675217188052878391665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201783478125368585594443 10802675217188052878391665)
          ·
            refine ⟨8102006412891039658793749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10802675217188052878391665 8102006412891039658793749)
            ·
              refine ⟨379781550604267484005957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8102006412891039658793749 379781550604267484005957)
              ·
                refine ⟨71209040738300153251117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379781550604267484005957 71209040738300153251117)
                ·
                  rfl

theorem cell20_468042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_468042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468042 prefixEnd_468042 := by exact prefixLift 468042
  have htrace : WordTrace (prefixWord ++ tailWord_468042) baseStart_468042 baseEnd_468042 := by
    simpa [prefixWord, tailWord_468042, baseEnd_468042] using wordTrace_append hprefix tailTrace_468042
  have hstable : (prefixWord ++ tailWord_468042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468042).length < 2 ^ (prefixWord ++ tailWord_468042).sum := by decide
  have hdescent : baseEnd_468042 < baseStart_468042 := by decide
  rcases family_descends (prefixWord ++ tailWord_468042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468052 : List Nat := [2, 4, 1, 1, 1, 1, 5, 3, 2]
def baseStart_468052 : Nat := 118140960795 + 468052 * 2 ^ 59
def prefixEnd_468052 : Nat := 4983230072969 + 3 ^ 40 * 468052 * 2
def baseEnd_468052 : Nat := 213631686487384869419977

theorem tailTrace_468052 : CollatzResearch.WordTrace tailWord_468052 prefixEnd_468052 213631686487384869419977 := by
  unfold tailWord_468052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535629450167507881303205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11380839266890010508404273 8535629450167507881303205)
  ·
    refine ⟨1600430521906407727744351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8535629450167507881303205 1600430521906407727744351)
    ·
      refine ⟨2400645782859611591616527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600430521906407727744351 2400645782859611591616527)
      ·
        refine ⟨3600968674289417387424791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400645782859611591616527 3600968674289417387424791)
        ·
          refine ⟨5401453011434126081137187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600968674289417387424791 5401453011434126081137187)
          ·
            refine ⟨8102179517151189121705781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401453011434126081137187 8102179517151189121705781)
            ·
              refine ⟨759579329732923980159917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8102179517151189121705781 759579329732923980159917)
              ·
                refine ⟨284842248649846492559969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 759579329732923980159917 284842248649846492559969)
                ·
                  refine ⟨213631686487384869419977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284842248649846492559969 213631686487384869419977)
                  ·
                    rfl

theorem cell20_468052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_468052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468052 prefixEnd_468052 := by exact prefixLift 468052
  have htrace : WordTrace (prefixWord ++ tailWord_468052) baseStart_468052 baseEnd_468052 := by
    simpa [prefixWord, tailWord_468052, baseEnd_468052] using wordTrace_append hprefix tailTrace_468052
  have hstable : (prefixWord ++ tailWord_468052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468052).length < 2 ^ (prefixWord ++ tailWord_468052).sum := by decide
  have hdescent : baseEnd_468052 < baseStart_468052 := by decide
  rcases family_descends (prefixWord ++ tailWord_468052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468066 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_468066 : Nat := 118140960795 + 468066 * 2 ^ 59
def prefixEnd_468066 : Nat := 4983230072969 + 3 ^ 40 * 468066 * 2
def baseEnd_468066 : Nat := 213638076468863042953253

theorem tailTrace_468066 : CollatzResearch.WordTrace tailWord_468066 prefixEnd_468066 213638076468863042953253 := by
  unfold tailWord_468066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4267942380571074038404013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11381179681522864102410701 4267942380571074038404013)
  ·
    refine ⟨1600478392714152764401505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4267942380571074038404013 1600478392714152764401505)
    ·
      refine ⟨1200358794535614573301129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1600478392714152764401505 1200358794535614573301129)
      ·
        refine ⟨900269095901710929975847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1200358794535614573301129 900269095901710929975847)
        ·
          refine ⟨1350403643852566394963771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900269095901710929975847 1350403643852566394963771)
          ·
            refine ⟨2025605465778849592445657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350403643852566394963771 2025605465778849592445657)
            ·
              refine ⟨1519204099334137194334243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2025605465778849592445657 1519204099334137194334243)
              ·
                refine ⟨2278806149001205791501365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519204099334137194334243 2278806149001205791501365)
                ·
                  refine ⟨213638076468863042953253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2278806149001205791501365 213638076468863042953253)
                  ·
                    rfl

theorem cell20_468066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_468066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468066 prefixEnd_468066 := by exact prefixLift 468066
  have htrace : WordTrace (prefixWord ++ tailWord_468066) baseStart_468066 baseEnd_468066 := by
    simpa [prefixWord, tailWord_468066, baseEnd_468066] using wordTrace_append hprefix tailTrace_468066
  have hstable : (prefixWord ++ tailWord_468066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468066).length < 2 ^ (prefixWord ++ tailWord_468066).sum := by decide
  have hdescent : baseEnd_468066 < baseStart_468066 := by decide
  rcases family_descends (prefixWord ++ tailWord_468066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468073 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 4]
def baseStart_468073 : Nat := 118140960795 + 468073 * 2 ^ 59
def prefixEnd_468073 : Nat := 4983230072969 + 3 ^ 40 * 468073 * 2
def baseEnd_468073 : Nat := 213641271459602129719891

theorem tailTrace_468073 : CollatzResearch.WordTrace tailWord_468073 prefixEnd_468073 213641271459602129719891 := by
  unfold tailWord_468073
  simp only [CollatzResearch.WordTrace]
  refine ⟨17072024833258936349120873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11381349888839290899413915 17072024833258936349120873)
  ·
    refine ⟨12804018624944202261840655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17072024833258936349120873 12804018624944202261840655)
    ·
      refine ⟨19206027937416303392760983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12804018624944202261840655 19206027937416303392760983)
      ·
        refine ⟨28809041906124455089141475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19206027937416303392760983 28809041906124455089141475)
        ·
          refine ⟨43213562859186682633712213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28809041906124455089141475 43213562859186682633712213)
          ·
            refine ⟨506408939756093937113815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 43213562859186682633712213 506408939756093937113815)
            ·
              refine ⟨759613409634140905670723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506408939756093937113815 759613409634140905670723)
              ·
                refine ⟨1139420114451211358506085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759613409634140905670723 1139420114451211358506085)
                ·
                  refine ⟨213641271459602129719891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1139420114451211358506085 213641271459602129719891)
                  ·
                    rfl

theorem cell20_468073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_468073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468073 prefixEnd_468073 := by exact prefixLift 468073
  have htrace : WordTrace (prefixWord ++ tailWord_468073) baseStart_468073 baseEnd_468073 := by
    simpa [prefixWord, tailWord_468073, baseEnd_468073] using wordTrace_append hprefix tailTrace_468073
  have hstable : (prefixWord ++ tailWord_468073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468073).length < 2 ^ (prefixWord ++ tailWord_468073).sum := by decide
  have hdescent : baseEnd_468073 < baseStart_468073 := by decide
  rcases family_descends (prefixWord ++ tailWord_468073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468087 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 3]
def baseStart_468087 : Nat := 118140960795 + 468087 * 2 ^ 59
def prefixEnd_468087 : Nat := 4983230072969 + 3 ^ 40 * 468087 * 2
def baseEnd_468087 : Nat := 213647661441080303253167

theorem tailTrace_468087 : CollatzResearch.WordTrace tailWord_468087 prefixEnd_468087 213647661441080303253167 := by
  unfold tailWord_468087
  simp only [CollatzResearch.WordTrace]
  refine ⟨17072535455208216740130515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11381690303472144493420343 17072535455208216740130515)
  ·
    refine ⟨25608803182812325110195773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17072535455208216740130515 25608803182812325110195773)
    ·
      refine ⟨9603301193554621916323415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25608803182812325110195773 9603301193554621916323415)
      ·
        refine ⟨14404951790331932874485123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9603301193554621916323415 14404951790331932874485123)
        ·
          refine ⟨21607427685497899311727685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14404951790331932874485123 21607427685497899311727685)
          ·
            refine ⟨4051392691030856120948941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21607427685497899311727685 4051392691030856120948941)
            ·
              refine ⟨1519272259136571045355853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4051392691030856120948941 1519272259136571045355853)
              ·
                refine ⟨569727097176214142008445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1519272259136571045355853 569727097176214142008445)
                ·
                  refine ⟨213647661441080303253167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569727097176214142008445 213647661441080303253167)
                  ·
                    rfl

theorem cell20_468087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 3].length) (baseStart_468087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468087 prefixEnd_468087 := by exact prefixLift 468087
  have htrace : WordTrace (prefixWord ++ tailWord_468087) baseStart_468087 baseEnd_468087 := by
    simpa [prefixWord, tailWord_468087, baseEnd_468087] using wordTrace_append hprefix tailTrace_468087
  have hstable : (prefixWord ++ tailWord_468087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468087).length < 2 ^ (prefixWord ++ tailWord_468087).sum := by decide
  have hdescent : baseEnd_468087 < baseStart_468087 := by decide
  rcases family_descends (prefixWord ++ tailWord_468087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468108 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_468108 : Nat := 118140960795 + 468108 * 2 ^ 59
def prefixEnd_468108 : Nat := 4983230072969 + 3 ^ 40 * 468108 * 2
def baseEnd_468108 : Nat := 213657246413297563553081

theorem tailTrace_468108 : CollatzResearch.WordTrace tailWord_468108 prefixEnd_468108 213657246413297563553081 := by
  unfold tailWord_468108
  simp only [CollatzResearch.WordTrace]
  refine ⟨8536650694066068663322489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11382200925421424884429985 8536650694066068663322489)
  ·
    refine ⟨6402488020549551497491867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8536650694066068663322489 6402488020549551497491867)
    ·
      refine ⟨9603732030824327246237801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6402488020549551497491867 9603732030824327246237801)
      ·
        refine ⟨7202799023118245434678351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9603732030824327246237801 7202799023118245434678351)
        ·
          refine ⟨10804198534677368152017527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7202799023118245434678351 10804198534677368152017527)
          ·
            refine ⟨16206297802016052228026291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10804198534677368152017527 16206297802016052228026291)
            ·
              refine ⟨24309446703024078342039437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16206297802016052228026291 24309446703024078342039437)
              ·
                refine ⟨9116042513634029378264789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24309446703024078342039437 9116042513634029378264789)
                ·
                  refine ⟨213657246413297563553081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9116042513634029378264789 213657246413297563553081)
                  ·
                    rfl

theorem cell20_468108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_468108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468108 prefixEnd_468108 := by exact prefixLift 468108
  have htrace : WordTrace (prefixWord ++ tailWord_468108) baseStart_468108 baseEnd_468108 := by
    simpa [prefixWord, tailWord_468108, baseEnd_468108] using wordTrace_append hprefix tailTrace_468108
  have hstable : (prefixWord ++ tailWord_468108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468108).length < 2 ^ (prefixWord ++ tailWord_468108).sum := by decide
  have hdescent : baseEnd_468108 < baseStart_468108 := by decide
  rcases family_descends (prefixWord ++ tailWord_468108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468135 : List Nat := [1, 1, 6, 2, 1, 3, 1, 5]
def baseStart_468135 : Nat := 118140960795 + 468135 * 2 ^ 59
def prefixEnd_468135 : Nat := 4983230072969 + 3 ^ 40 * 468135 * 2
def baseEnd_468135 : Nat := 71223189983001823217657

theorem tailTrace_468135 : CollatzResearch.WordTrace tailWord_468135 prefixEnd_468135 71223189983001823217657 := by
  unfold tailWord_468135
  simp only [CollatzResearch.WordTrace]
  refine ⟨17074286159034320937877859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11382857439356213958585239 17074286159034320937877859)
  ·
    refine ⟨25611429238551481406816789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17074286159034320937877859 25611429238551481406816789)
    ·
      refine ⟨1200535745557100690944537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25611429238551481406816789 1200535745557100690944537)
      ·
        refine ⟨900401809167825518208403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1200535745557100690944537 900401809167825518208403)
        ·
          refine ⟨1350602713751738277312605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900401809167825518208403 1350602713751738277312605)
          ·
            refine ⟨506476017656901853992227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1350602713751738277312605 506476017656901853992227)
            ·
              refine ⟨759714026485352780988341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506476017656901853992227 759714026485352780988341)
              ·
                refine ⟨71223189983001823217657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 759714026485352780988341 71223189983001823217657)
                ·
                  rfl

theorem cell20_468135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 5].length) (baseStart_468135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468135 prefixEnd_468135 := by exact prefixLift 468135
  have htrace : WordTrace (prefixWord ++ tailWord_468135) baseStart_468135 baseEnd_468135 := by
    simpa [prefixWord, tailWord_468135, baseEnd_468135] using wordTrace_append hprefix tailTrace_468135
  have hstable : (prefixWord ++ tailWord_468135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468135).length < 2 ^ (prefixWord ++ tailWord_468135).sum := by decide
  have hdescent : baseEnd_468135 < baseStart_468135 := by decide
  rcases family_descends (prefixWord ++ tailWord_468135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468197 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 3]
def baseStart_468197 : Nat := 118140960795 + 468197 * 2 ^ 59
def prefixEnd_468197 : Nat := 4983230072969 + 3 ^ 40 * 468197 * 2
def baseEnd_468197 : Nat := 213697868438408809586051

theorem tailTrace_468197 : CollatzResearch.WordTrace tailWord_468197 prefixEnd_468197 213697868438408809586051 := by
  unfold tailWord_468197
  simp only [CollatzResearch.WordTrace]
  refine ⟨17076547484809705526634845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11384364989873137017756563 17076547484809705526634845)
  ·
    refine ⟨6403705306803639572488067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17076547484809705526634845 6403705306803639572488067)
    ·
      refine ⟨9605557960205459358732101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6403705306803639572488067 9605557960205459358732101)
      ·
        refine ⟨1801042117538523629762269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9605557960205459358732101 1801042117538523629762269)
        ·
          refine ⟨675390794076946361160851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1801042117538523629762269 675390794076946361160851)
          ·
            refine ⟨1013086191115419541741277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675390794076946361160851 1013086191115419541741277)
            ·
              refine ⟨379907321668282328152979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1013086191115419541741277 379907321668282328152979)
              ·
                refine ⟨569860982502423492229469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379907321668282328152979 569860982502423492229469)
                ·
                  refine ⟨213697868438408809586051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569860982502423492229469 213697868438408809586051)
                  ·
                    rfl

theorem cell20_468197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_468197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468197 prefixEnd_468197 := by exact prefixLift 468197
  have htrace : WordTrace (prefixWord ++ tailWord_468197) baseStart_468197 baseEnd_468197 := by
    simpa [prefixWord, tailWord_468197, baseEnd_468197] using wordTrace_append hprefix tailTrace_468197
  have hstable : (prefixWord ++ tailWord_468197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468197).length < 2 ^ (prefixWord ++ tailWord_468197).sum := by decide
  have hdescent : baseEnd_468197 < baseStart_468197 := by decide
  rcases family_descends (prefixWord ++ tailWord_468197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468232 : List Nat := [2, 1, 3, 2, 4, 2, 6]
def baseStart_468232 : Nat := 118140960795 + 468232 * 2 ^ 59
def prefixEnd_468232 : Nat := 4983230072969 + 3 ^ 40 * 468232 * 2
def baseEnd_468232 : Nat := 23745982599122693713249

theorem tailTrace_468232 : CollatzResearch.WordTrace tailWord_468232 prefixEnd_468232 23745982599122693713249 := by
  unfold tailWord_468232
  simp only [CollatzResearch.WordTrace]
  refine ⟨8538912019841453252079475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11385216026455271002772633 8538912019841453252079475)
  ·
    refine ⟨12808368029762179878119213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8538912019841453252079475 12808368029762179878119213)
    ·
      refine ⟨4803138011160817454294705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12808368029762179878119213 4803138011160817454294705)
      ·
        refine ⟨3602353508370613090721029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4803138011160817454294705 3602353508370613090721029)
        ·
          refine ⟨675441282819489954510193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3602353508370613090721029 675441282819489954510193)
          ·
            refine ⟨506580962114617465882645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675441282819489954510193 506580962114617465882645)
            ·
              refine ⟨23745982599122693713249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 506580962114617465882645 23745982599122693713249)
              ·
                rfl

theorem cell20_468232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 6].length) (baseStart_468232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468232 prefixEnd_468232 := by exact prefixLift 468232
  have htrace : WordTrace (prefixWord ++ tailWord_468232) baseStart_468232 baseEnd_468232 := by
    simpa [prefixWord, tailWord_468232, baseEnd_468232] using wordTrace_append hprefix tailTrace_468232
  have hstable : (prefixWord ++ tailWord_468232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468232).length < 2 ^ (prefixWord ++ tailWord_468232).sum := by decide
  have hdescent : baseEnd_468232 < baseStart_468232 := by decide
  rcases family_descends (prefixWord ++ tailWord_468232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468256 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 3]
def baseStart_468256 : Nat := 118140960795 + 468256 * 2 ^ 59
def prefixEnd_468256 : Nat := 4983230072969 + 3 ^ 40 * 468256 * 2
def baseEnd_468256 : Nat := 213724797646066826619143

theorem tailTrace_468256 : CollatzResearch.WordTrace tailWord_468256 prefixEnd_468256 213724797646066826619143 := by
  unfold tailWord_468256
  simp only [CollatzResearch.WordTrace]
  refine ⟨8539349695797979301516311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11385799594397305735355081 8539349695797979301516311)
  ·
    refine ⟨12809024543696968952274467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8539349695797979301516311 12809024543696968952274467)
    ·
      refine ⟨19213536815545453428411701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12809024543696968952274467 19213536815545453428411701)
      ·
        refine ⟨1801269076457386258913597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19213536815545453428411701 1801269076457386258913597)
        ·
          refine ⟨675475903671519847092599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1801269076457386258913597 675475903671519847092599)
          ·
            refine ⟨1013213855507279770638899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675475903671519847092599 1013213855507279770638899)
            ·
              refine ⟨1519820783260919655958349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013213855507279770638899 1519820783260919655958349)
              ·
                refine ⟨569932793722844870984381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1519820783260919655958349 569932793722844870984381)
                ·
                  refine ⟨213724797646066826619143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 569932793722844870984381 213724797646066826619143)
                  ·
                    rfl

theorem cell20_468256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_468256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468256 prefixEnd_468256 := by exact prefixLift 468256
  have htrace : WordTrace (prefixWord ++ tailWord_468256) baseStart_468256 baseEnd_468256 := by
    simpa [prefixWord, tailWord_468256, baseEnd_468256] using wordTrace_append hprefix tailTrace_468256
  have hstable : (prefixWord ++ tailWord_468256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468256).length < 2 ^ (prefixWord ++ tailWord_468256).sum := by decide
  have hdescent : baseEnd_468256 < baseStart_468256 := by decide
  rcases family_descends (prefixWord ++ tailWord_468256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468298 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_468298 : Nat := 118140960795 + 468298 * 2 ^ 59
def prefixEnd_468298 : Nat := 4983230072969 + 3 ^ 40 * 468298 * 2
def baseEnd_468298 : Nat := 213743967590501347218971

theorem tailTrace_468298 : CollatzResearch.WordTrace tailWord_468298 prefixEnd_468298 213743967590501347218971 := by
  unfold tailWord_468298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4270057814360949944015387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11386820838295866517374365 4270057814360949944015387)
  ·
    refine ⟨6405086721541424916023081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4270057814360949944015387 6405086721541424916023081)
    ·
      refine ⟨4803815041156068687017311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6405086721541424916023081 4803815041156068687017311)
      ·
        refine ⟨7205722561734103030525967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4803815041156068687017311 7205722561734103030525967)
        ·
          refine ⟨10808583842601154545788951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7205722561734103030525967 10808583842601154545788951)
          ·
            refine ⟨16212875763901731818683427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10808583842601154545788951 16212875763901731818683427)
            ·
              refine ⟨24319313645852597728025141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16212875763901731818683427 24319313645852597728025141)
              ·
                refine ⟨2279935654298681037002357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24319313645852597728025141 2279935654298681037002357)
                ·
                  refine ⟨213743967590501347218971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2279935654298681037002357 213743967590501347218971)
                  ·
                    rfl

theorem cell20_468298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_468298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468298 prefixEnd_468298 := by exact prefixLift 468298
  have htrace : WordTrace (prefixWord ++ tailWord_468298) baseStart_468298 baseEnd_468298 := by
    simpa [prefixWord, tailWord_468298, baseEnd_468298] using wordTrace_append hprefix tailTrace_468298
  have hstable : (prefixWord ++ tailWord_468298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468298).length < 2 ^ (prefixWord ++ tailWord_468298).sum := by decide
  have hdescent : baseEnd_468298 < baseStart_468298 := by decide
  rcases family_descends (prefixWord ++ tailWord_468298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468336 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_468336 : Nat := 118140960795 + 468336 * 2 ^ 59
def prefixEnd_468336 : Nat := 4983230072969 + 3 ^ 40 * 468336 * 2
def baseEnd_468336 : Nat := 213761311825942103952149

theorem tailTrace_468336 : CollatzResearch.WordTrace tailWord_468336 prefixEnd_468336 213761311825942103952149 := by
  unfold tailWord_468336
  simp only [CollatzResearch.WordTrace]
  refine ⟨8540808615653066132972431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11387744820870754843963241 8540808615653066132972431)
  ·
    refine ⟨12811212923479599199458647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8540808615653066132972431 12811212923479599199458647)
    ·
      refine ⟨19216819385219398799187971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12811212923479599199458647 19216819385219398799187971)
      ·
        refine ⟨28825229077829098198781957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19216819385219398799187971 28825229077829098198781957)
        ·
          refine ⟨5404730452092955912271617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28825229077829098198781957 5404730452092955912271617)
          ·
            refine ⟨4053547839069716934203713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5404730452092955912271617 4053547839069716934203713)
            ·
              refine ⟨3040160879302287700652785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4053547839069716934203713 3040160879302287700652785)
              ·
                refine ⟨2280120659476715775489589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3040160879302287700652785 2280120659476715775489589)
                ·
                  refine ⟨213761311825942103952149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2280120659476715775489589 213761311825942103952149)
                  ·
                    rfl

theorem cell20_468336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_468336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468336 prefixEnd_468336 := by exact prefixLift 468336
  have htrace : WordTrace (prefixWord ++ tailWord_468336) baseStart_468336 baseEnd_468336 := by
    simpa [prefixWord, tailWord_468336, baseEnd_468336] using wordTrace_append hprefix tailTrace_468336
  have hstable : (prefixWord ++ tailWord_468336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468336).length < 2 ^ (prefixWord ++ tailWord_468336).sum := by decide
  have hdescent : baseEnd_468336 < baseStart_468336 := by decide
  rcases family_descends (prefixWord ++ tailWord_468336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468343 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_468343 : Nat := 118140960795 + 468343 * 2 ^ 59
def prefixEnd_468343 : Nat := 4983230072969 + 3 ^ 40 * 468343 * 2
def baseEnd_468343 : Nat := 213764506816681190718787

theorem tailTrace_468343 : CollatzResearch.WordTrace tailWord_468343 prefixEnd_468343 213764506816681190718787 := by
  unfold tailWord_468343
  simp only [CollatzResearch.WordTrace]
  refine ⟨17081872542280772461449683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11387915028187181640966455 17081872542280772461449683)
  ·
    refine ⟨25622808813421158692174525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17081872542280772461449683 25622808813421158692174525)
    ·
      refine ⟨9608553305032934509565447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25622808813421158692174525 9608553305032934509565447)
      ·
        refine ⟨14412829957549401764348171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9608553305032934509565447 14412829957549401764348171)
        ·
          refine ⟨21619244936324102646522257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14412829957549401764348171 21619244936324102646522257)
          ·
            refine ⟨16214433702243076984891693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21619244936324102646522257 16214433702243076984891693)
            ·
              refine ⟨6080412638341153869334385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16214433702243076984891693 6080412638341153869334385)
              ·
                refine ⟨4560309478755865402000789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6080412638341153869334385 4560309478755865402000789)
                ·
                  refine ⟨213764506816681190718787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4560309478755865402000789 213764506816681190718787)
                  ·
                    rfl

theorem cell20_468343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_468343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468343 prefixEnd_468343 := by exact prefixLift 468343
  have htrace : WordTrace (prefixWord ++ tailWord_468343) baseStart_468343 baseEnd_468343 := by
    simpa [prefixWord, tailWord_468343, baseEnd_468343] using wordTrace_append hprefix tailTrace_468343
  have hstable : (prefixWord ++ tailWord_468343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468343).length < 2 ^ (prefixWord ++ tailWord_468343).sum := by decide
  have hdescent : baseEnd_468343 < baseStart_468343 := by decide
  rcases family_descends (prefixWord ++ tailWord_468343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468360 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_468360 : Nat := 118140960795 + 468360 * 2 ^ 59
def prefixEnd_468360 : Nat := 4983230072969 + 3 ^ 40 * 468360 * 2
def baseEnd_468360 : Nat := 213772266079904687152051

theorem tailTrace_468360 : CollatzResearch.WordTrace tailWord_468360 prefixEnd_468360 213772266079904687152051 := by
  unfold tailWord_468360
  simp only [CollatzResearch.WordTrace]
  refine ⟨8541246291609592182409267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11388328388812789576545689 8541246291609592182409267)
  ·
    refine ⟨12811869437414388273613901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8541246291609592182409267 12811869437414388273613901)
    ·
      refine ⟨4804451039030395602605213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12811869437414388273613901 4804451039030395602605213)
      ·
        refine ⟨1801669139636398350976955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4804451039030395602605213 1801669139636398350976955)
        ·
          refine ⟨2702503709454597526465433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801669139636398350976955 2702503709454597526465433)
          ·
            refine ⟨2026877782090948144849075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2702503709454597526465433 2026877782090948144849075)
            ·
              refine ⟨3040316673136422217273613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026877782090948144849075 3040316673136422217273613)
              ·
                refine ⟨1140118752426158331477605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3040316673136422217273613 1140118752426158331477605)
                ·
                  refine ⟨213772266079904687152051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1140118752426158331477605 213772266079904687152051)
                  ·
                    rfl

theorem cell20_468360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_468360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468360 prefixEnd_468360 := by exact prefixLift 468360
  have htrace : WordTrace (prefixWord ++ tailWord_468360) baseStart_468360 baseEnd_468360 := by
    simpa [prefixWord, tailWord_468360, baseEnd_468360] using wordTrace_append hprefix tailTrace_468360
  have hstable : (prefixWord ++ tailWord_468360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468360).length < 2 ^ (prefixWord ++ tailWord_468360).sum := by decide
  have hdescent : baseEnd_468360 < baseStart_468360 := by decide
  rcases family_descends (prefixWord ++ tailWord_468360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468380 : List Nat := [2, 2, 3, 4, 1, 2, 2, 4]
def baseStart_468380 : Nat := 118140960795 + 468380 * 2 ^ 59
def prefixEnd_468380 : Nat := 4983230072969 + 3 ^ 40 * 468380 * 2
def baseEnd_468380 : Nat := 71260464874957835495101

theorem tailTrace_468380 : CollatzResearch.WordTrace tailWord_468380 prefixEnd_468380 71260464874957835495101 := by
  unfold tailWord_468380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8541611021573363890273297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11388814695431151853697729 8541611021573363890273297)
  ·
    refine ⟨6406208266180022917704973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8541611021573363890273297 6406208266180022917704973)
    ·
      refine ⟨2402328099817508594139365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6406208266180022917704973 2402328099817508594139365)
      ·
        refine ⟨450436518715782861401131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2402328099817508594139365 450436518715782861401131)
        ·
          refine ⟨675654778073674292101697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450436518715782861401131 675654778073674292101697)
          ·
            refine ⟨506741083555255719076273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675654778073674292101697 506741083555255719076273)
            ·
              refine ⟨380055812666441789307205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506741083555255719076273 380055812666441789307205)
              ·
                refine ⟨71260464874957835495101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 380055812666441789307205 71260464874957835495101)
                ·
                  rfl

theorem cell20_468380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_468380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468380 prefixEnd_468380 := by exact prefixLift 468380
  have htrace : WordTrace (prefixWord ++ tailWord_468380) baseStart_468380 baseEnd_468380 := by
    simpa [prefixWord, tailWord_468380, baseEnd_468380] using wordTrace_append hprefix tailTrace_468380
  have hstable : (prefixWord ++ tailWord_468380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468380).length < 2 ^ (prefixWord ++ tailWord_468380).sum := by decide
  have hdescent : baseEnd_468380 < baseStart_468380 := by decide
  rcases family_descends (prefixWord ++ tailWord_468380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468405 : List Nat := [1, 3, 3, 2, 2, 1, 8]
def baseStart_468405 : Nat := 118140960795 + 468405 * 2 ^ 59
def prefixEnd_468405 : Nat := 4983230072969 + 3 ^ 40 * 468405 * 2
def baseEnd_468405 : Nat := 23754756145120503405763

theorem tailTrace_468405 : CollatzResearch.WordTrace tailWord_468405 prefixEnd_468405 23754756145120503405763 := by
  unfold tailWord_468405
  simp only [CollatzResearch.WordTrace]
  refine ⟨17084133868056157050206669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11389422578704104700137779 17084133868056157050206669)
  ·
    refine ⟨6406550200521058893827501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17084133868056157050206669 6406550200521058893827501)
    ·
      refine ⟨2402456325195397085185313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6406550200521058893827501 2402456325195397085185313)
      ·
        refine ⟨1801842243896547813888985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2402456325195397085185313 1801842243896547813888985)
        ·
          refine ⟨1351381682922410860416739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1801842243896547813888985 1351381682922410860416739)
          ·
            refine ⟨2027072524383616290625109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351381682922410860416739 2027072524383616290625109)
            ·
              refine ⟨23754756145120503405763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2027072524383616290625109 23754756145120503405763)
              ·
                rfl

theorem cell20_468405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 8].length) (baseStart_468405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468405 prefixEnd_468405 := by exact prefixLift 468405
  have htrace : WordTrace (prefixWord ++ tailWord_468405) baseStart_468405 baseEnd_468405 := by
    simpa [prefixWord, tailWord_468405, baseEnd_468405] using wordTrace_append hprefix tailTrace_468405
  have hstable : (prefixWord ++ tailWord_468405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468405).length < 2 ^ (prefixWord ++ tailWord_468405).sum := by decide
  have hdescent : baseEnd_468405 < baseStart_468405 := by decide
  rcases family_descends (prefixWord ++ tailWord_468405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468464 : List Nat := [2, 1, 1, 1, 3, 12]
def baseStart_468464 : Nat := 118140960795 + 468464 * 2 ^ 59
def prefixEnd_468464 : Nat := 4983230072969 + 3 ^ 40 * 468464 * 2
def baseEnd_468464 : Nat := 7919249426434909173517

theorem tailTrace_468464 : CollatzResearch.WordTrace tailWord_468464 prefixEnd_468464 7919249426434909173517 := by
  unfold tailWord_468464
  simp only [CollatzResearch.WordTrace]
  refine ⟨8543142887421205063302223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11390857183228273417736297 8543142887421205063302223)
  ·
    refine ⟨12814714331131807594953335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8543142887421205063302223 12814714331131807594953335)
    ·
      refine ⟨19222071496697711392430003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12814714331131807594953335 19222071496697711392430003)
      ·
        refine ⟨28833107245046567088645005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19222071496697711392430003 28833107245046567088645005)
        ·
          refine ⟨10812415216892462658241877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28833107245046567088645005 10812415216892462658241877)
          ·
            refine ⟨7919249426434909173517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10812415216892462658241877 7919249426434909173517)
            ·
              rfl

theorem cell20_468464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 12].length) (baseStart_468464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468464 prefixEnd_468464 := by exact prefixLift 468464
  have htrace : WordTrace (prefixWord ++ tailWord_468464) baseStart_468464 baseEnd_468464 := by
    simpa [prefixWord, tailWord_468464, baseEnd_468464] using wordTrace_append hprefix tailTrace_468464
  have hstable : (prefixWord ++ tailWord_468464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468464).length < 2 ^ (prefixWord ++ tailWord_468464).sum := by decide
  have hdescent : baseEnd_468464 < baseStart_468464 := by decide
  rcases family_descends (prefixWord ++ tailWord_468464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468470 : List Nat := [5, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_468470 : Nat := 118140960795 + 468470 * 2 ^ 59
def prefixEnd_468470 : Nat := 4983230072969 + 3 ^ 40 * 468470 * 2
def baseEnd_468470 : Nat := 213822473077233193484935

theorem tailTrace_468470 : CollatzResearch.WordTrace tailWord_468470 prefixEnd_468470 213822473077233193484935 := by
  unfold tailWord_468470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1067906538301292071957679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11391003075213782100881909 1067906538301292071957679)
  ·
    refine ⟨1601859807451938107936519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1067906538301292071957679 1601859807451938107936519)
    ·
      refine ⟨2402789711177907161904779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1601859807451938107936519 2402789711177907161904779)
      ·
        refine ⟨3604184566766860742857169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402789711177907161904779 3604184566766860742857169)
        ·
          refine ⟨2703138425075145557142877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3604184566766860742857169 2703138425075145557142877)
          ·
            refine ⟨1013676909403179583928579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2703138425075145557142877 1013676909403179583928579)
            ·
              refine ⟨1520515364104769375892869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013676909403179583928579 1520515364104769375892869)
              ·
                refine ⟨285096630769644257979913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1520515364104769375892869 285096630769644257979913)
                ·
                  refine ⟨213822473077233193484935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285096630769644257979913 213822473077233193484935)
                  ·
                    rfl

theorem cell20_468470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_468470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468470 prefixEnd_468470 := by exact prefixLift 468470
  have htrace : WordTrace (prefixWord ++ tailWord_468470) baseStart_468470 baseEnd_468470 := by
    simpa [prefixWord, tailWord_468470, baseEnd_468470] using wordTrace_append hprefix tailTrace_468470
  have hstable : (prefixWord ++ tailWord_468470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468470).length < 2 ^ (prefixWord ++ tailWord_468470).sum := by decide
  have hdescent : baseEnd_468470 < baseStart_468470 := by decide
  rcases family_descends (prefixWord ++ tailWord_468470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468564 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_468564 : Nat := 118140960795 + 468564 * 2 ^ 59
def prefixEnd_468564 : Nat := 4983230072969 + 3 ^ 40 * 468564 * 2
def baseEnd_468564 : Nat := 213865377238586644351217

theorem tailTrace_468564 : CollatzResearch.WordTrace tailWord_468564 prefixEnd_468564 213865377238586644351217 := by
  unfold tailWord_468564
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544966537240063602622373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11393288716320084803496497 8544966537240063602622373)
  ·
    refine ⟨1602181225732511925491695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8544966537240063602622373 1602181225732511925491695)
    ·
      refine ⟨2403271838598767888237543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602181225732511925491695 2403271838598767888237543)
      ·
        refine ⟨3604907757898151832356315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2403271838598767888237543 3604907757898151832356315)
        ·
          refine ⟨5407361636847227748534473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3604907757898151832356315 5407361636847227748534473)
          ·
            refine ⟨4055521227635420811400855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5407361636847227748534473 4055521227635420811400855)
            ·
              refine ⟨6083281841453131217101283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055521227635420811400855 6083281841453131217101283)
              ·
                refine ⟨9124922762179696825651925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083281841453131217101283 9124922762179696825651925)
                ·
                  refine ⟨213865377238586644351217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9124922762179696825651925 213865377238586644351217)
                  ·
                    rfl

theorem cell20_468564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_468564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468564 prefixEnd_468564 := by exact prefixLift 468564
  have htrace : WordTrace (prefixWord ++ tailWord_468564) baseStart_468564 baseEnd_468564 := by
    simpa [prefixWord, tailWord_468564, baseEnd_468564] using wordTrace_append hprefix tailTrace_468564
  have hstable : (prefixWord ++ tailWord_468564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468564).length < 2 ^ (prefixWord ++ tailWord_468564).sum := by decide
  have hdescent : baseEnd_468564 < baseStart_468564 := by decide
  rcases family_descends (prefixWord ++ tailWord_468564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468567 : List Nat := [1, 1, 3, 2, 2, 3, 3, 3, 2]
def baseStart_468567 : Nat := 118140960795 + 468567 * 2 ^ 59
def prefixEnd_468567 : Nat := 4983230072969 + 3 ^ 40 * 468567 * 2
def baseEnd_468567 : Nat := 213866746520331967251205

theorem tailTrace_468567 : CollatzResearch.WordTrace tailWord_468567 prefixEnd_468567 213866746520331967251205 := by
  unfold tailWord_468567
  simp only [CollatzResearch.WordTrace]
  refine ⟨17090042493469258717603955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11393361662312839145069303 17090042493469258717603955)
  ·
    refine ⟨25635063740203888076405933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17090042493469258717603955 25635063740203888076405933)
    ·
      refine ⟨9613148902576458028652225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25635063740203888076405933 9613148902576458028652225)
      ·
        refine ⟨7209861676932343521489169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9613148902576458028652225 7209861676932343521489169)
        ·
          refine ⟨5407396257699257641116877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7209861676932343521489169 5407396257699257641116877)
          ·
            refine ⟨2027773596637221615418829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5407396257699257641116877 2027773596637221615418829)
            ·
              refine ⟨760415098738958105782061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2027773596637221615418829 760415098738958105782061)
              ·
                refine ⟨285155662027109289668273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 760415098738958105782061 285155662027109289668273)
                ·
                  refine ⟨213866746520331967251205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285155662027109289668273 213866746520331967251205)
                  ·
                    rfl

theorem cell20_468567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 2].length) (baseStart_468567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468567 prefixEnd_468567 := by exact prefixLift 468567
  have htrace : WordTrace (prefixWord ++ tailWord_468567) baseStart_468567 baseEnd_468567 := by
    simpa [prefixWord, tailWord_468567, baseEnd_468567] using wordTrace_append hprefix tailTrace_468567
  have hstable : (prefixWord ++ tailWord_468567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468567).length < 2 ^ (prefixWord ++ tailWord_468567).sum := by decide
  have hdescent : baseEnd_468567 < baseStart_468567 := by decide
  rcases family_descends (prefixWord ++ tailWord_468567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468598 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_468598 : Nat := 118140960795 + 468598 * 2 ^ 59
def prefixEnd_468598 : Nat := 4983230072969 + 3 ^ 40 * 468598 * 2
def baseEnd_468598 : Nat := 213880895765033637217745

theorem tailTrace_468598 : CollatzResearch.WordTrace tailWord_468598 prefixEnd_468598 213880895765033637217745 := by
  unfold tailWord_468598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068198322272309438248903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11394115437571300674654965 1068198322272309438248903)
  ·
    refine ⟨1602297483408464157373355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1068198322272309438248903 1602297483408464157373355)
    ·
      refine ⟨2403446225112696236060033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602297483408464157373355 2403446225112696236060033)
      ·
        refine ⟨1802584668834522177045025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2403446225112696236060033 1802584668834522177045025)
        ·
          refine ⟨1351938501625891632783769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802584668834522177045025 1351938501625891632783769)
          ·
            refine ⟨1013953876219418724587827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351938501625891632783769 1013953876219418724587827)
            ·
              refine ⟨1520930814329128086881741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1013953876219418724587827 1520930814329128086881741)
              ·
                refine ⟨570349055373423032580653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1520930814329128086881741 570349055373423032580653)
                ·
                  refine ⟨213880895765033637217745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570349055373423032580653 213880895765033637217745)
                  ·
                    rfl

theorem cell20_468598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_468598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468598 prefixEnd_468598 := by exact prefixLift 468598
  have htrace : WordTrace (prefixWord ++ tailWord_468598) baseStart_468598 baseEnd_468598 := by
    simpa [prefixWord, tailWord_468598, baseEnd_468598] using wordTrace_append hprefix tailTrace_468598
  have hstable : (prefixWord ++ tailWord_468598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468598).length < 2 ^ (prefixWord ++ tailWord_468598).sum := by decide
  have hdescent : baseEnd_468598 < baseStart_468598 := by decide
  rcases family_descends (prefixWord ++ tailWord_468598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468636 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 3]
def baseStart_468636 : Nat := 118140960795 + 468636 * 2 ^ 59
def prefixEnd_468636 : Nat := 4983230072969 + 3 ^ 40 * 468636 * 2
def baseEnd_468636 : Nat := 213898240000474393950923

theorem tailTrace_468636 : CollatzResearch.WordTrace tailWord_468636 prefixEnd_468636 213898240000474393950923 := by
  unfold tailWord_468636
  simp only [CollatzResearch.WordTrace]
  refine ⟨8546279565109641750932881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11395039420146189001243841 8546279565109641750932881)
  ·
    refine ⟨6409709673832231313199661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8546279565109641750932881 6409709673832231313199661)
    ·
      refine ⟨2403641127687086742449873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6409709673832231313199661 2403641127687086742449873)
      ·
        refine ⟨1802730845765315056837405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2403641127687086742449873 1802730845765315056837405)
        ·
          refine ⟨676024067161993146314027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1802730845765315056837405 676024067161993146314027)
          ·
            refine ⟨1014036100742989719471041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676024067161993146314027 1014036100742989719471041)
            ·
              refine ⟨760527075557242289603281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1014036100742989719471041 760527075557242289603281)
              ·
                refine ⟨570395306667931717202461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 760527075557242289603281 570395306667931717202461)
                ·
                  refine ⟨213898240000474393950923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570395306667931717202461 213898240000474393950923)
                  ·
                    rfl

theorem cell20_468636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_468636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468636 prefixEnd_468636 := by exact prefixLift 468636
  have htrace : WordTrace (prefixWord ++ tailWord_468636) baseStart_468636 baseEnd_468636 := by
    simpa [prefixWord, tailWord_468636, baseEnd_468636] using wordTrace_append hprefix tailTrace_468636
  have hstable : (prefixWord ++ tailWord_468636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468636).length < 2 ^ (prefixWord ++ tailWord_468636).sum := by decide
  have hdescent : baseEnd_468636 < baseStart_468636 := by decide
  rcases family_descends (prefixWord ++ tailWord_468636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468671 : List Nat := [1, 1, 2, 2, 2, 3, 5, 4]
def baseStart_468671 : Nat := 118140960795 + 468671 * 2 ^ 59
def prefixEnd_468671 : Nat := 4983230072969 + 3 ^ 40 * 468671 * 2
def baseEnd_468671 : Nat := 71304738318056609261371

theorem tailTrace_468671 : CollatzResearch.WordTrace tailWord_468671 prefixEnd_468671 71304738318056609261371 := by
  unfold tailWord_468671
  simp only [CollatzResearch.WordTrace]
  refine ⟨17093835685092484479389867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11395890456728322986259911 17093835685092484479389867)
  ·
    refine ⟨25640753527638726719084801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17093835685092484479389867 25640753527638726719084801)
    ·
      refine ⟨19230565145729045039313601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25640753527638726719084801 19230565145729045039313601)
      ·
        refine ⟨14422923859296783779485201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19230565145729045039313601 14422923859296783779485201)
        ·
          refine ⟨10817192894472587834613901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14422923859296783779485201 10817192894472587834613901)
          ·
            refine ⟨4056447335427220437980213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10817192894472587834613901 4056447335427220437980213)
            ·
              refine ⟨380291937696301916060645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4056447335427220437980213 380291937696301916060645)
              ·
                refine ⟨71304738318056609261371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 380291937696301916060645 71304738318056609261371)
                ·
                  rfl

theorem cell20_468671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 4].length) (baseStart_468671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468671 prefixEnd_468671 := by exact prefixLift 468671
  have htrace : WordTrace (prefixWord ++ tailWord_468671) baseStart_468671 baseEnd_468671 := by
    simpa [prefixWord, tailWord_468671, baseEnd_468671] using wordTrace_append hprefix tailTrace_468671
  have hstable : (prefixWord ++ tailWord_468671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468671).length < 2 ^ (prefixWord ++ tailWord_468671).sum := by decide
  have hdescent : baseEnd_468671 < baseStart_468671 := by decide
  rcases family_descends (prefixWord ++ tailWord_468671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468712 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 3]
def baseStart_468712 : Nat := 118140960795 + 468712 * 2 ^ 59
def prefixEnd_468712 : Nat := 4983230072969 + 3 ^ 40 * 468712 * 2
def baseEnd_468712 : Nat := 213932928471355907417279

theorem tailTrace_468712 : CollatzResearch.WordTrace tailWord_468712 prefixEnd_468712 213932928471355907417279 := by
  unfold tailWord_468712
  simp only [CollatzResearch.WordTrace]
  refine ⟨8547665538971974240816195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11396887385295965654421593 8547665538971974240816195)
  ·
    refine ⟨12821498308457961361224293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8547665538971974240816195 12821498308457961361224293)
    ·
      refine ⟨2404030932835867755229555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12821498308457961361224293 2404030932835867755229555)
      ·
        refine ⟨3606046399253801632844333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404030932835867755229555 3606046399253801632844333)
        ·
          refine ⟨1352267399720175612316625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3606046399253801632844333 1352267399720175612316625)
          ·
            refine ⟨1014200549790131709237469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1352267399720175612316625 1014200549790131709237469)
            ·
              refine ⟨380325206171299390964051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1014200549790131709237469 380325206171299390964051)
              ·
                refine ⟨570487809256949086446077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380325206171299390964051 570487809256949086446077)
                ·
                  refine ⟨213932928471355907417279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570487809256949086446077 213932928471355907417279)
                  ·
                    rfl

theorem cell20_468712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_468712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468712 prefixEnd_468712 := by exact prefixLift 468712
  have htrace : WordTrace (prefixWord ++ tailWord_468712) baseStart_468712 baseEnd_468712 := by
    simpa [prefixWord, tailWord_468712, baseEnd_468712] using wordTrace_append hprefix tailTrace_468712
  have hstable : (prefixWord ++ tailWord_468712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468712).length < 2 ^ (prefixWord ++ tailWord_468712).sum := by decide
  have hdescent : baseEnd_468712 < baseStart_468712 := by decide
  rcases family_descends (prefixWord ++ tailWord_468712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468716 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 3]
def baseStart_468716 : Nat := 118140960795 + 468716 * 2 ^ 59
def prefixEnd_468716 : Nat := 4983230072969 + 3 ^ 40 * 468716 * 2
def baseEnd_468716 : Nat := 213934754180349671283929

theorem tailTrace_468716 : CollatzResearch.WordTrace tailWord_468716 prefixEnd_468716 213934754180349671283929 := by
  unfold tailWord_468716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8547738484964728582389001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11396984646619638109852001 8547738484964728582389001)
  ·
    refine ⟨6410803863723546436791751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8547738484964728582389001 6410803863723546436791751)
    ·
      refine ⟨9616205795585319655187627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6410803863723546436791751 9616205795585319655187627)
      ·
        refine ⟨14424308693377979482781441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9616205795585319655187627 14424308693377979482781441)
        ·
          refine ⟨10818231520033484612086081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14424308693377979482781441 10818231520033484612086081)
          ·
            refine ⟨8113673640025113459064561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10818231520033484612086081 8113673640025113459064561)
            ·
              refine ⟨6085255230018835094298421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8113673640025113459064561 6085255230018835094298421)
              ·
                refine ⟨570492677814265790090477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6085255230018835094298421 570492677814265790090477)
                ·
                  refine ⟨213934754180349671283929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570492677814265790090477 213934754180349671283929)
                  ·
                    rfl

theorem cell20_468716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_468716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468716 prefixEnd_468716 := by exact prefixLift 468716
  have htrace : WordTrace (prefixWord ++ tailWord_468716) baseStart_468716 baseEnd_468716 := by
    simpa [prefixWord, tailWord_468716, baseEnd_468716] using wordTrace_append hprefix tailTrace_468716
  have hstable : (prefixWord ++ tailWord_468716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468716).length < 2 ^ (prefixWord ++ tailWord_468716).sum := by decide
  have hdescent : baseEnd_468716 < baseStart_468716 := by decide
  rcases family_descends (prefixWord ++ tailWord_468716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468723 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 4]
def baseStart_468723 : Nat := 118140960795 + 468723 * 2 ^ 59
def prefixEnd_468723 : Nat := 4983230072969 + 3 ^ 40 * 468723 * 2
def baseEnd_468723 : Nat := 213937949171088758050567

theorem tailTrace_468723 : CollatzResearch.WordTrace tailWord_468723 prefixEnd_468723 213937949171088758050567 := by
  unfold tailWord_468723
  simp only [CollatzResearch.WordTrace]
  refine ⟨17095732280904097360282823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11397154853936064906855215 17095732280904097360282823)
  ·
    refine ⟨25643598421356146040424235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17095732280904097360282823 25643598421356146040424235)
    ·
      refine ⟨38465397632034219060636353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25643598421356146040424235 38465397632034219060636353)
      ·
        refine ⟨28849048224025664295477265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38465397632034219060636353 28849048224025664295477265)
        ·
          refine ⟨21636786168019248221607949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28849048224025664295477265 21636786168019248221607949)
          ·
            refine ⟨8113794813007218083102981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21636786168019248221607949 8113794813007218083102981)
            ·
              refine ⟨1521336527438853390581809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8113794813007218083102981 1521336527438853390581809)
              ·
                refine ⟨1141002395579140042936357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1521336527438853390581809 1141002395579140042936357)
                ·
                  refine ⟨213937949171088758050567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1141002395579140042936357 213937949171088758050567)
                  ·
                    rfl

theorem cell20_468723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_468723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468723 prefixEnd_468723 := by exact prefixLift 468723
  have htrace : WordTrace (prefixWord ++ tailWord_468723) baseStart_468723 baseEnd_468723 := by
    simpa [prefixWord, tailWord_468723, baseEnd_468723] using wordTrace_append hprefix tailTrace_468723
  have hstable : (prefixWord ++ tailWord_468723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468723).length < 2 ^ (prefixWord ++ tailWord_468723).sum := by decide
  have hdescent : baseEnd_468723 < baseStart_468723 := by decide
  rcases family_descends (prefixWord ++ tailWord_468723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468726 : List Nat := [5, 1, 1, 1, 1, 3, 4, 4]
def baseStart_468726 : Nat := 118140960795 + 468726 * 2 ^ 59
def prefixEnd_468726 : Nat := 4983230072969 + 3 ^ 40 * 468726 * 2
def baseEnd_468726 : Nat := 71313106150944693650185

theorem tailTrace_468726 : CollatzResearch.WordTrace tailWord_468726 prefixEnd_468726 71313106150944693650185 := by
  unfold tailWord_468726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068490106243326804540127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11397227799928819248428021 1068490106243326804540127)
  ·
    refine ⟨1602735159364990206810191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1068490106243326804540127 1602735159364990206810191)
    ·
      refine ⟨2404102739047485310215287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602735159364990206810191 2404102739047485310215287)
      ·
        refine ⟨3606154108571227965322931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404102739047485310215287 3606154108571227965322931)
        ·
          refine ⟨5409231162856841947984397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606154108571227965322931 5409231162856841947984397)
          ·
            refine ⟨2028461686071315730494149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5409231162856841947984397 2028461686071315730494149)
            ·
              refine ⟨380336566138371699467653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2028461686071315730494149 380336566138371699467653)
              ·
                refine ⟨71313106150944693650185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 380336566138371699467653 71313106150944693650185)
                ·
                  rfl

theorem cell20_468726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_468726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468726 prefixEnd_468726 := by exact prefixLift 468726
  have htrace : WordTrace (prefixWord ++ tailWord_468726) baseStart_468726 baseEnd_468726 := by
    simpa [prefixWord, tailWord_468726, baseEnd_468726] using wordTrace_append hprefix tailTrace_468726
  have hstable : (prefixWord ++ tailWord_468726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468726).length < 2 ^ (prefixWord ++ tailWord_468726).sum := by decide
  have hdescent : baseEnd_468726 < baseStart_468726 := by decide
  rcases family_descends (prefixWord ++ tailWord_468726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468749 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 4]
def baseStart_468749 : Nat := 118140960795 + 468749 * 2 ^ 59
def prefixEnd_468749 : Nat := 4983230072969 + 3 ^ 40 * 468749 * 2
def baseEnd_468749 : Nat := 213949816279548223183795

theorem tailTrace_468749 : CollatzResearch.WordTrace tailWord_468749 prefixEnd_468749 213949816279548223183795 := by
  unfold tailWord_468749
  simp only [CollatzResearch.WordTrace]
  refine ⟨17096680578809903800729301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11397787052539935867152867 17096680578809903800729301)
  ·
    refine ⟨400703451065857120329593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17096680578809903800729301 400703451065857120329593)
    ·
      refine ⟨300527588299392840247195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400703451065857120329593 300527588299392840247195)
      ·
        refine ⟨450791382449089260370793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300527588299392840247195 450791382449089260370793)
        ·
          refine ⟨338093536836816945278095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450791382449089260370793 338093536836816945278095)
          ·
            refine ⟨507140305255225417917143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338093536836816945278095 507140305255225417917143)
            ·
              refine ⟨760710457882838126875715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507140305255225417917143 760710457882838126875715)
              ·
                refine ⟨1141065686824257190313573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760710457882838126875715 1141065686824257190313573)
                ·
                  refine ⟨213949816279548223183795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1141065686824257190313573 213949816279548223183795)
                  ·
                    rfl

theorem cell20_468749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_468749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468749 prefixEnd_468749 := by exact prefixLift 468749
  have htrace : WordTrace (prefixWord ++ tailWord_468749) baseStart_468749 baseEnd_468749 := by
    simpa [prefixWord, tailWord_468749, baseEnd_468749] using wordTrace_append hprefix tailTrace_468749
  have hstable : (prefixWord ++ tailWord_468749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468749).length < 2 ^ (prefixWord ++ tailWord_468749).sum := by decide
  have hdescent : baseEnd_468749 < baseStart_468749 := by decide
  rcases family_descends (prefixWord ++ tailWord_468749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468771 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 3]
def baseStart_468771 : Nat := 118140960795 + 468771 * 2 ^ 59
def prefixEnd_468771 : Nat := 4983230072969 + 3 ^ 40 * 468771 * 2
def baseEnd_468771 : Nat := 213959857679013924450371

theorem tailTrace_468771 : CollatzResearch.WordTrace tailWord_468771 prefixEnd_468771 213959857679013924450371 := by
  unfold tailWord_468771
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097482984730201558030167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11398321989820134372020111 17097482984730201558030167)
  ·
    refine ⟨25646224477095302337045251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17097482984730201558030167 25646224477095302337045251)
    ·
      refine ⟨38469336715642953505567877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25646224477095302337045251 38469336715642953505567877)
      ·
        refine ⟨7213000634183053782293977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38469336715642953505567877 7213000634183053782293977)
        ·
          refine ⟨5409750475637290336720483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7213000634183053782293977 5409750475637290336720483)
          ·
            refine ⟨8114625713455935505080725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5409750475637290336720483 8114625713455935505080725)
            ·
              refine ⟨380373080318246976800659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8114625713455935505080725 380373080318246976800659)
              ·
                refine ⟨570559620477370465200989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380373080318246976800659 570559620477370465200989)
                ·
                  refine ⟨213959857679013924450371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570559620477370465200989 213959857679013924450371)
                  ·
                    rfl

theorem cell20_468771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 3].length) (baseStart_468771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468771 prefixEnd_468771 := by exact prefixLift 468771
  have htrace : WordTrace (prefixWord ++ tailWord_468771) baseStart_468771 baseEnd_468771 := by
    simpa [prefixWord, tailWord_468771, baseEnd_468771] using wordTrace_append hprefix tailTrace_468771
  have hstable : (prefixWord ++ tailWord_468771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468771).length < 2 ^ (prefixWord ++ tailWord_468771).sum := by decide
  have hdescent : baseEnd_468771 < baseStart_468771 := by decide
  rcases family_descends (prefixWord ++ tailWord_468771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468851 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_468851 : Nat := 118140960795 + 468851 * 2 ^ 59
def prefixEnd_468851 : Nat := 4983230072969 + 3 ^ 40 * 468851 * 2
def baseEnd_468851 : Nat := 213996371858889201783377

theorem tailTrace_468851 : CollatzResearch.WordTrace tailWord_468851 prefixEnd_468851 213996371858889201783377 := by
  unfold tailWord_468851
  simp only [CollatzResearch.WordTrace]
  refine ⟨17100400824440375220942407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11400267216293583480628271 17100400824440375220942407)
  ·
    refine ⟨25650601236660562831413611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17100400824440375220942407 25650601236660562831413611)
    ·
      refine ⟨38475901854990844247120417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25650601236660562831413611 38475901854990844247120417)
      ·
        refine ⟨28856926391243133185340313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38475901854990844247120417 28856926391243133185340313)
        ·
          refine ⟨21642694793432349889005235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28856926391243133185340313 21642694793432349889005235)
          ·
            refine ⟨32464042190148524833507853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21642694793432349889005235 32464042190148524833507853)
            ·
              refine ⟨12174015821305696812565445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32464042190148524833507853 12174015821305696812565445)
              ·
                refine ⟨2282627966494818152356021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12174015821305696812565445 2282627966494818152356021)
                ·
                  refine ⟨213996371858889201783377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2282627966494818152356021 213996371858889201783377)
                  ·
                    rfl

theorem cell20_468851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_468851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468851 prefixEnd_468851 := by exact prefixLift 468851
  have htrace : WordTrace (prefixWord ++ tailWord_468851) baseStart_468851 baseEnd_468851 := by
    simpa [prefixWord, tailWord_468851, baseEnd_468851] using wordTrace_append hprefix tailTrace_468851
  have hstable : (prefixWord ++ tailWord_468851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468851).length < 2 ^ (prefixWord ++ tailWord_468851).sum := by decide
  have hdescent : baseEnd_468851 < baseStart_468851 := by decide
  rcases family_descends (prefixWord ++ tailWord_468851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468885 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 3]
def baseStart_468885 : Nat := 118140960795 + 468885 * 2 ^ 59
def prefixEnd_468885 : Nat := 4983230072969 + 3 ^ 40 * 468885 * 2
def baseEnd_468885 : Nat := 214011890385336194649905

theorem tailTrace_468885 : CollatzResearch.WordTrace tailWord_468885 prefixEnd_468885 214011890385336194649905 := by
  unfold tailWord_468885
  simp only [CollatzResearch.WordTrace]
  refine ⟨17101640906317199027680109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11401093937544799351786739 17101640906317199027680109)
  ·
    refine ⟨6413115339868949635380041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17101640906317199027680109 6413115339868949635380041)
    ·
      refine ⟨4809836504901712226535031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6413115339868949635380041 4809836504901712226535031)
      ·
        refine ⟨7214754757352568339802547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4809836504901712226535031 7214754757352568339802547)
        ·
          refine ⟨10822132136028852509703821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7214754757352568339802547 10822132136028852509703821)
          ·
            refine ⟨4058299551010819691138933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10822132136028852509703821 4058299551010819691138933)
            ·
              refine ⟨380465582907264346044275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4058299551010819691138933 380465582907264346044275)
              ·
                refine ⟨570698374360896519066413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380465582907264346044275 570698374360896519066413)
                ·
                  refine ⟨214011890385336194649905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570698374360896519066413 214011890385336194649905)
                  ·
                    rfl

theorem cell20_468885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_468885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468885 prefixEnd_468885 := by exact prefixLift 468885
  have htrace : WordTrace (prefixWord ++ tailWord_468885) baseStart_468885 baseEnd_468885 := by
    simpa [prefixWord, tailWord_468885, baseEnd_468885] using wordTrace_append hprefix tailTrace_468885
  have hstable : (prefixWord ++ tailWord_468885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468885).length < 2 ^ (prefixWord ++ tailWord_468885).sum := by decide
  have hdescent : baseEnd_468885 < baseStart_468885 := by decide
  rcases family_descends (prefixWord ++ tailWord_468885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468892 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_468892 : Nat := 118140960795 + 468892 * 2 ^ 59
def prefixEnd_468892 : Nat := 4983230072969 + 3 ^ 40 * 468892 * 2
def baseEnd_468892 : Nat := 214015085376075281416543

theorem tailTrace_468892 : CollatzResearch.WordTrace tailWord_468892 prefixEnd_468892 214015085376075281416543 := by
  unfold tailWord_468892
  simp only [CollatzResearch.WordTrace]
  refine ⟨8550948108645919611592465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11401264144861226148789953 8550948108645919611592465)
  ·
    refine ⟨6413211081484439708694349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8550948108645919611592465 6413211081484439708694349)
    ·
      refine ⟨2404954155556664890760381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6413211081484439708694349 2404954155556664890760381)
      ·
        refine ⟨901857808333749334035143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2404954155556664890760381 901857808333749334035143)
        ·
          refine ⟨1352786712500624001052715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901857808333749334035143 1352786712500624001052715)
          ·
            refine ⟨2029180068750936001579073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352786712500624001052715 2029180068750936001579073)
            ·
              refine ⟨1521885051563202001184305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029180068750936001579073 1521885051563202001184305)
              ·
                refine ⟨1141413788672401500888229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1521885051563202001184305 1141413788672401500888229)
                ·
                  refine ⟨214015085376075281416543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1141413788672401500888229 214015085376075281416543)
                  ·
                    rfl

theorem cell20_468892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_468892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468892 prefixEnd_468892 := by exact prefixLift 468892
  have htrace : WordTrace (prefixWord ++ tailWord_468892) baseStart_468892 baseEnd_468892 := by
    simpa [prefixWord, tailWord_468892, baseEnd_468892] using wordTrace_append hprefix tailTrace_468892
  have hstable : (prefixWord ++ tailWord_468892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468892).length < 2 ^ (prefixWord ++ tailWord_468892).sum := by decide
  have hdescent : baseEnd_468892 < baseStart_468892 := by decide
  rcases family_descends (prefixWord ++ tailWord_468892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468895 : List Nat := [1, 1, 2, 5, 4, 1, 2, 4]
def baseStart_468895 : Nat := 118140960795 + 468895 * 2 ^ 59
def prefixEnd_468895 : Nat := 4983230072969 + 3 ^ 40 * 468895 * 2
def baseEnd_468895 : Nat := 71338818219273534772177

theorem tailTrace_468895 : CollatzResearch.WordTrace tailWord_468895 prefixEnd_468895 71338818219273534772177 := by
  unfold tailWord_468895
  simp only [CollatzResearch.WordTrace]
  refine ⟨17102005636280970735544139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11401337090853980490362759 17102005636280970735544139)
  ·
    refine ⟨25653008454421456103316209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17102005636280970735544139 25653008454421456103316209)
    ·
      refine ⟨19239756340816092077487157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25653008454421456103316209 19239756340816092077487157)
      ·
        refine ⟨1803727156951508632264421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19239756340816092077487157 1803727156951508632264421)
        ·
          refine ⟨338198841928407868549579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1803727156951508632264421 338198841928407868549579)
          ·
            refine ⟨507298262892611802824369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338198841928407868549579 507298262892611802824369)
            ·
              refine ⟨380473697169458852118277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507298262892611802824369 380473697169458852118277)
              ·
                refine ⟨71338818219273534772177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 380473697169458852118277 71338818219273534772177)
                ·
                  rfl

theorem cell20_468895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 4].length) (baseStart_468895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468895 prefixEnd_468895 := by exact prefixLift 468895
  have htrace : WordTrace (prefixWord ++ tailWord_468895) baseStart_468895 baseEnd_468895 := by
    simpa [prefixWord, tailWord_468895, baseEnd_468895] using wordTrace_append hprefix tailTrace_468895
  have hstable : (prefixWord ++ tailWord_468895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468895).length < 2 ^ (prefixWord ++ tailWord_468895).sum := by decide
  have hdescent : baseEnd_468895 < baseStart_468895 := by decide
  rcases family_descends (prefixWord ++ tailWord_468895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468926 : List Nat := [4, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_468926 : Nat := 118140960795 + 468926 * 2 ^ 59
def prefixEnd_468926 : Nat := 4983230072969 + 3 ^ 40 * 468926 * 2
def baseEnd_468926 : Nat := 214030603902522274283071

theorem tailTrace_468926 : CollatzResearch.WordTrace tailWord_468926 prefixEnd_468926 214030603902522274283071 := by
  unfold tailWord_468926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2137892037396082878740329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11402090866112442019948421 2137892037396082878740329)
  ·
    refine ⟨1603419028047062159055247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2137892037396082878740329 1603419028047062159055247)
    ·
      refine ⟨2405128542070593238582871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603419028047062159055247 2405128542070593238582871)
      ·
        refine ⟨3607692813105889857874307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405128542070593238582871 3607692813105889857874307)
        ·
          refine ⟨5411539219658834786811461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3607692813105889857874307 5411539219658834786811461)
          ·
            refine ⟨1014663603686031522527149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5411539219658834786811461 1014663603686031522527149)
            ·
              refine ⟨380498851382261820947681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1014663603686031522527149 380498851382261820947681)
              ·
                refine ⟨285374138536696365710761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380498851382261820947681 285374138536696365710761)
                ·
                  refine ⟨214030603902522274283071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285374138536696365710761 214030603902522274283071)
                  ·
                    rfl

theorem cell20_468926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_468926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468926 prefixEnd_468926 := by exact prefixLift 468926
  have htrace : WordTrace (prefixWord ++ tailWord_468926) baseStart_468926 baseEnd_468926 := by
    simpa [prefixWord, tailWord_468926, baseEnd_468926] using wordTrace_append hprefix tailTrace_468926
  have hstable : (prefixWord ++ tailWord_468926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468926).length < 2 ^ (prefixWord ++ tailWord_468926).sum := by decide
  have hdescent : baseEnd_468926 < baseStart_468926 := by decide
  rcases family_descends (prefixWord ++ tailWord_468926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468927 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 5]
def baseStart_468927 : Nat := 118140960795 + 468927 * 2 ^ 59
def prefixEnd_468927 : Nat := 4983230072969 + 3 ^ 40 * 468927 * 2
def baseEnd_468927 : Nat := 214031060329770715249733

theorem tailTrace_468927 : CollatzResearch.WordTrace tailWord_468927 prefixEnd_468927 214031060329770715249733 := by
  unfold tailWord_468927
  simp only [CollatzResearch.WordTrace]
  refine ⟨17103172772165040200709035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11402115181443360133806023 17103172772165040200709035)
  ·
    refine ⟨25654759158247560301063553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17103172772165040200709035 25654759158247560301063553)
    ·
      refine ⟨19241069368685670225797665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25654759158247560301063553 19241069368685670225797665)
      ·
        refine ⟨14430802026514252669348249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19241069368685670225797665 14430802026514252669348249)
        ·
          refine ⟨10823101519885689502011187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14430802026514252669348249 10823101519885689502011187)
          ·
            refine ⟨16234652279828534253016781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10823101519885689502011187 16234652279828534253016781)
            ·
              refine ⟨6087994604935700344881293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16234652279828534253016781 6087994604935700344881293)
              ·
                refine ⟨2282997976850887629330485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6087994604935700344881293 2282997976850887629330485)
                ·
                  refine ⟨214031060329770715249733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2282997976850887629330485 214031060329770715249733)
                  ·
                    rfl

theorem cell20_468927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_468927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468927 prefixEnd_468927 := by exact prefixLift 468927
  have htrace : WordTrace (prefixWord ++ tailWord_468927) baseStart_468927 baseEnd_468927 := by
    simpa [prefixWord, tailWord_468927, baseEnd_468927] using wordTrace_append hprefix tailTrace_468927
  have hstable : (prefixWord ++ tailWord_468927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468927).length < 2 ^ (prefixWord ++ tailWord_468927).sum := by decide
  have hdescent : baseEnd_468927 < baseStart_468927 := by decide
  rcases family_descends (prefixWord ++ tailWord_468927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468940 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 3]
def baseStart_468940 : Nat := 118140960795 + 468940 * 2 ^ 59
def prefixEnd_468940 : Nat := 4983230072969 + 3 ^ 40 * 468940 * 2
def baseEnd_468940 : Nat := 214036993884000447816347

theorem tailTrace_468940 : CollatzResearch.WordTrace tailWord_468940 prefixEnd_468940 214036993884000447816347 := by
  unfold tailWord_468940
  simp only [CollatzResearch.WordTrace]
  refine ⟨8551823460558971710466137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11402431280745295613954849 8551823460558971710466137)
  ·
    refine ⟨6413867595419228782849603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8551823460558971710466137 6413867595419228782849603)
    ·
      refine ⟨9620801393128843174274405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6413867595419228782849603 9620801393128843174274405)
      ·
        refine ⟨1803900261211658095176451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9620801393128843174274405 1803900261211658095176451)
        ·
          refine ⟨2705850391817487142764677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803900261211658095176451 2705850391817487142764677)
          ·
            refine ⟨507346948465778839268377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2705850391817487142764677 507346948465778839268377)
            ·
              refine ⟨380510211349334129451283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507346948465778839268377 380510211349334129451283)
              ·
                refine ⟨570765317024001194176925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380510211349334129451283 570765317024001194176925)
                ·
                  refine ⟨214036993884000447816347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570765317024001194176925 214036993884000447816347)
                  ·
                    rfl

theorem cell20_468940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_468940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468940 prefixEnd_468940 := by exact prefixLift 468940
  have htrace : WordTrace (prefixWord ++ tailWord_468940) baseStart_468940 baseEnd_468940 := by
    simpa [prefixWord, tailWord_468940, baseEnd_468940] using wordTrace_append hprefix tailTrace_468940
  have hstable : (prefixWord ++ tailWord_468940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468940).length < 2 ^ (prefixWord ++ tailWord_468940).sum := by decide
  have hdescent : baseEnd_468940 < baseStart_468940 := by decide
  rcases family_descends (prefixWord ++ tailWord_468940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468968 : List Nat := [2, 1, 4, 1, 1, 1, 1, 7, 2]
def baseStart_468968 : Nat := 118140960795 + 468968 * 2 ^ 59
def prefixEnd_468968 : Nat := 4983230072969 + 3 ^ 40 * 468968 * 2
def baseEnd_468968 : Nat := 214049773846956794882899

theorem tailTrace_468968 : CollatzResearch.WordTrace tailWord_468968 prefixEnd_468968 214049773846956794882899 := by
  unfold tailWord_468968
  simp only [CollatzResearch.WordTrace]
  refine ⟨8552334082508252101475779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11403112110011002801967705 8552334082508252101475779)
  ·
    refine ⟨12828501123762378152213669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8552334082508252101475779 12828501123762378152213669)
    ·
      refine ⟨2405343960705445903540063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12828501123762378152213669 2405343960705445903540063)
      ·
        refine ⟨3608015941058168855310095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405343960705445903540063 3608015941058168855310095)
        ·
          refine ⟨5412023911587253282965143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3608015941058168855310095 5412023911587253282965143)
          ·
            refine ⟨8118035867380879924447715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412023911587253282965143 8118035867380879924447715)
            ·
              refine ⟨12177053801071319886671573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8118035867380879924447715 12177053801071319886671573)
              ·
                refine ⟨285399698462609059843865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12177053801071319886671573 285399698462609059843865)
                ·
                  refine ⟨214049773846956794882899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285399698462609059843865 214049773846956794882899)
                  ·
                    rfl

theorem cell20_468968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 2].length) (baseStart_468968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468968 prefixEnd_468968 := by exact prefixLift 468968
  have htrace : WordTrace (prefixWord ++ tailWord_468968) baseStart_468968 baseEnd_468968 := by
    simpa [prefixWord, tailWord_468968, baseEnd_468968] using wordTrace_append hprefix tailTrace_468968
  have hstable : (prefixWord ++ tailWord_468968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468968).length < 2 ^ (prefixWord ++ tailWord_468968).sum := by decide
  have hdescent : baseEnd_468968 < baseStart_468968 := by decide
  rcases family_descends (prefixWord ++ tailWord_468968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468985 : List Nat := [1, 2, 1, 3, 1, 4, 4, 2, 2]
def baseStart_468985 : Nat := 118140960795 + 468985 * 2 ^ 59
def prefixEnd_468985 : Nat := 4983230072969 + 3 ^ 40 * 468985 * 2
def baseEnd_468985 : Nat := 214057533110180291316163

theorem tailTrace_468985 : CollatzResearch.WordTrace tailWord_468985 prefixEnd_468985 214057533110180291316163 := by
  unfold tailWord_468985
  simp only [CollatzResearch.WordTrace]
  refine ⟨17105288205954916106320409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11403525470636610737546939 17105288205954916106320409)
  ·
    refine ⟨12828966154466187079740307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17105288205954916106320409 12828966154466187079740307)
    ·
      refine ⟨19243449231699280619610461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12828966154466187079740307 19243449231699280619610461)
      ·
        refine ⟨7216293461887230232353923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19243449231699280619610461 7216293461887230232353923)
        ·
          refine ⟨10824440192830845348530885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7216293461887230232353923 10824440192830845348530885)
          ·
            refine ⟨2029582536155783502849541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10824440192830845348530885 2029582536155783502849541)
            ·
              refine ⟨380546725529209406784289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2029582536155783502849541 380546725529209406784289)
              ·
                refine ⟨285410044146907055088217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380546725529209406784289 285410044146907055088217)
                ·
                  refine ⟨214057533110180291316163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285410044146907055088217 214057533110180291316163)
                  ·
                    rfl

theorem cell20_468985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 2].length) (baseStart_468985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_468985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_468985 prefixEnd_468985 := by exact prefixLift 468985
  have htrace : WordTrace (prefixWord ++ tailWord_468985) baseStart_468985 baseEnd_468985 := by
    simpa [prefixWord, tailWord_468985, baseEnd_468985] using wordTrace_append hprefix tailTrace_468985
  have hstable : (prefixWord ++ tailWord_468985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468985).length < 2 ^ (prefixWord ++ tailWord_468985).sum := by decide
  have hdescent : baseEnd_468985 < baseStart_468985 := by decide
  rcases family_descends (prefixWord ++ tailWord_468985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
