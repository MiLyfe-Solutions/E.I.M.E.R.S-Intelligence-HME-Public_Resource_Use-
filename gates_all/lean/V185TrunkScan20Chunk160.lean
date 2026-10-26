import V185TrunkScan20Chunk159

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_973773 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 3]
def baseStart_973773 : Nat := 118140960795 + 973773 * 2 ^ 59
def prefixEnd_973773 : Nat := 4983230072969 + 3 ^ 40 * 973773 * 2
def baseEnd_973773 : Nat := 444456530996198970985961

theorem tailTrace_973773 : CollatzResearch.WordTrace tailWord_973773 prefixEnd_973773 444456530996198970985961 := by
  unfold tailWord_973773
  simp only [CollatzResearch.WordTrace]
  refine ⟨35516419101194203033117973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23677612734129468688745315 35516419101194203033117973)
  ·
    refine ⟨1664832145368478267177405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35516419101194203033117973 1664832145368478267177405)
    ·
      refine ⟨624312054513179350191527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1664832145368478267177405 624312054513179350191527)
      ·
        refine ⟨936468081769769025287291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624312054513179350191527 936468081769769025287291)
        ·
          refine ⟨1404702122654653537930937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936468081769769025287291 1404702122654653537930937)
          ·
            refine ⟨1053526591990990153448203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1404702122654653537930937 1053526591990990153448203)
            ·
              refine ⟨1580289887986485230172305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053526591990990153448203 1580289887986485230172305)
              ·
                refine ⟨1185217415989863922629229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580289887986485230172305 1185217415989863922629229)
                ·
                  refine ⟨444456530996198970985961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185217415989863922629229 444456530996198970985961)
                  ·
                    rfl

theorem cell20_973773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_973773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973773 prefixEnd_973773 := by exact prefixLift 973773
  have htrace : WordTrace (prefixWord ++ tailWord_973773) baseStart_973773 baseEnd_973773 := by
    simpa [prefixWord, tailWord_973773, baseEnd_973773] using wordTrace_append hprefix tailTrace_973773
  have hstable : (prefixWord ++ tailWord_973773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973773).length < 2 ^ (prefixWord ++ tailWord_973773).sum := by decide
  have hdescent : baseEnd_973773 < baseStart_973773 := by decide
  rcases family_descends (prefixWord ++ tailWord_973773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973781 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 5]
def baseStart_973781 : Nat := 118140960795 + 973781 * 2 ^ 59
def prefixEnd_973781 : Nat := 4983230072969 + 3 ^ 40 * 973781 * 2
def baseEnd_973781 : Nat := 444460182414186498719261

theorem tailTrace_973781 : CollatzResearch.WordTrace tailWord_973781 prefixEnd_973781 444460182414186498719261 := by
  unfold tailWord_973781
  simp only [CollatzResearch.WordTrace]
  refine ⟨35516710885165220399409197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23677807256776813599606131 35516710885165220399409197)
  ·
    refine ⟨13318766581936957649778449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35516710885165220399409197 13318766581936957649778449)
    ·
      refine ⟨9989074936452718237333837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13318766581936957649778449 9989074936452718237333837)
      ·
        refine ⟨3745903101169769339000189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9989074936452718237333837 3745903101169769339000189)
        ·
          refine ⟨1404713662938663502125071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3745903101169769339000189 1404713662938663502125071)
          ·
            refine ⟨2107070494407995253187607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404713662938663502125071 2107070494407995253187607)
            ·
              refine ⟨3160605741611992879781411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107070494407995253187607 3160605741611992879781411)
              ·
                refine ⟨4740908612417989319672117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160605741611992879781411 4740908612417989319672117)
                ·
                  refine ⟨444460182414186498719261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4740908612417989319672117 444460182414186498719261)
                  ·
                    rfl

theorem cell20_973781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_973781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973781 prefixEnd_973781 := by exact prefixLift 973781
  have htrace : WordTrace (prefixWord ++ tailWord_973781) baseStart_973781 baseEnd_973781 := by
    simpa [prefixWord, tailWord_973781, baseEnd_973781] using wordTrace_append hprefix tailTrace_973781
  have hstable : (prefixWord ++ tailWord_973781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973781).length < 2 ^ (prefixWord ++ tailWord_973781).sum := by decide
  have hdescent : baseEnd_973781 < baseStart_973781 := by decide
  rcases family_descends (prefixWord ++ tailWord_973781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973853 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 3]
def baseStart_973853 : Nat := 118140960795 + 973853 * 2 ^ 59
def prefixEnd_973853 : Nat := 4983230072969 + 3 ^ 40 * 973853 * 2
def baseEnd_973853 : Nat := 444493045176074248318967

theorem tailTrace_973853 : CollatzResearch.WordTrace tailWord_973853 prefixEnd_973853 444493045176074248318967 := by
  unfold tailWord_973853
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519336940904376696030213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23679557960602917797353475 35519336940904376696030213)
  ·
    refine ⟨6659875676419570630505665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35519336940904376696030213 6659875676419570630505665)
    ·
      refine ⟨4994906757314677972879249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6659875676419570630505665 4994906757314677972879249)
      ·
        refine ⟨3746180067986008479659437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4994906757314677972879249 3746180067986008479659437)
        ·
          refine ⟨1404817525494753179872289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3746180067986008479659437 1404817525494753179872289)
          ·
            refine ⟨1053613144121064884904217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1404817525494753179872289 1053613144121064884904217)
            ·
              refine ⟨790209858090798663678163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053613144121064884904217 790209858090798663678163)
              ·
                refine ⟨1185314787136197995517245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790209858090798663678163 1185314787136197995517245)
                ·
                  refine ⟨444493045176074248318967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185314787136197995517245 444493045176074248318967)
                  ·
                    rfl

theorem cell20_973853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_973853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973853 prefixEnd_973853 := by exact prefixLift 973853
  have htrace : WordTrace (prefixWord ++ tailWord_973853) baseStart_973853 baseEnd_973853 := by
    simpa [prefixWord, tailWord_973853, baseEnd_973853] using wordTrace_append hprefix tailTrace_973853
  have hstable : (prefixWord ++ tailWord_973853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973853).length < 2 ^ (prefixWord ++ tailWord_973853).sum := by decide
  have hdescent : baseEnd_973853 < baseStart_973853 := by decide
  rcases family_descends (prefixWord ++ tailWord_973853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973857 : List Nat := [1, 2, 3, 2, 3, 2, 1, 3, 3]
def baseStart_973857 : Nat := 118140960795 + 973857 * 2 ^ 59
def prefixEnd_973857 : Nat := 4983230072969 + 3 ^ 40 * 973857 * 2
def baseEnd_973857 : Nat := 444494870885068012185617

theorem tailTrace_973857 : CollatzResearch.WordTrace tailWord_973857 prefixEnd_973857 444494870885068012185617 := by
  unfold tailWord_973857
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519482832889885379175825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23679655221926590252783883 35519482832889885379175825)
  ·
    refine ⟨26639612124667414034381869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35519482832889885379175825 26639612124667414034381869)
    ·
      refine ⟨9989854546750280262893201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26639612124667414034381869 9989854546750280262893201)
      ·
        refine ⟨7492390910062710197169901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9989854546750280262893201 7492390910062710197169901)
        ·
          refine ⟨2809646591273516323938713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7492390910062710197169901 2809646591273516323938713)
          ·
            refine ⟨2107234943455137242954035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2809646591273516323938713 2107234943455137242954035)
            ·
              refine ⟨3160852415182705864431053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107234943455137242954035 3160852415182705864431053)
              ·
                refine ⟨1185319655693514699161645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3160852415182705864431053 1185319655693514699161645)
                ·
                  refine ⟨444494870885068012185617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185319655693514699161645 444494870885068012185617)
                  ·
                    rfl

theorem cell20_973857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_973857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973857 prefixEnd_973857 := by exact prefixLift 973857
  have htrace : WordTrace (prefixWord ++ tailWord_973857) baseStart_973857 baseEnd_973857 := by
    simpa [prefixWord, tailWord_973857, baseEnd_973857] using wordTrace_append hprefix tailTrace_973857
  have hstable : (prefixWord ++ tailWord_973857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973857).length < 2 ^ (prefixWord ++ tailWord_973857).sum := by decide
  have hdescent : baseEnd_973857 < baseStart_973857 := by decide
  rcases family_descends (prefixWord ++ tailWord_973857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973894 : List Nat := [6, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_973894 : Nat := 118140960795 + 973894 * 2 ^ 59
def prefixEnd_973894 : Nat := 4983230072969 + 3 ^ 40 * 973894 * 2
def baseEnd_973894 : Nat := 444511758693260327952133

theorem tailTrace_973894 : CollatzResearch.WordTrace tailWord_973894 prefixEnd_973894 444511758693260327952133 := by
  unfold tailWord_973894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110026010429870021821023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23680554889170560465515157 1110026010429870021821023)
  ·
    refine ⟨1665039015644805032731535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1110026010429870021821023 1665039015644805032731535)
    ·
      refine ⟨2497558523467207549097303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1665039015644805032731535 2497558523467207549097303)
      ·
        refine ⟨3746337785200811323645955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2497558523467207549097303 3746337785200811323645955)
        ·
          refine ⟨5619506677801216985468933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3746337785200811323645955 5619506677801216985468933)
          ·
            refine ⟨1053657502087728184775425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5619506677801216985468933 1053657502087728184775425)
            ·
              refine ⟨790243126565796138581569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053657502087728184775425 790243126565796138581569)
              ·
                refine ⟨592682344924347103936177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790243126565796138581569 592682344924347103936177)
                ·
                  refine ⟨444511758693260327952133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592682344924347103936177 444511758693260327952133)
                  ·
                    rfl

theorem cell20_973894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_973894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973894 prefixEnd_973894 := by exact prefixLift 973894
  have htrace : WordTrace (prefixWord ++ tailWord_973894) baseStart_973894 baseEnd_973894 := by
    simpa [prefixWord, tailWord_973894, baseEnd_973894] using wordTrace_append hprefix tailTrace_973894
  have hstable : (prefixWord ++ tailWord_973894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973894).length < 2 ^ (prefixWord ++ tailWord_973894).sum := by decide
  have hdescent : baseEnd_973894 < baseStart_973894 := by decide
  rcases family_descends (prefixWord ++ tailWord_973894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973895 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 3]
def baseStart_973895 : Nat := 118140960795 + 973895 * 2 ^ 59
def prefixEnd_973895 : Nat := 4983230072969 + 3 ^ 40 * 973895 * 2
def baseEnd_973895 : Nat := 444512215120508768918795

theorem tailTrace_973895 : CollatzResearch.WordTrace tailWord_973895 prefixEnd_973895 444512215120508768918795 := by
  unfold tailWord_973895
  simp only [CollatzResearch.WordTrace]
  refine ⟨35520868806752217869059139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23680579204501478579372759 35520868806752217869059139)
  ·
    refine ⟨53281303210128326803588709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35520868806752217869059139 53281303210128326803588709)
    ·
      refine ⟨9990244351899061275672883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53281303210128326803588709 9990244351899061275672883)
      ·
        refine ⟨14985366527848591913509325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9990244351899061275672883 14985366527848591913509325)
        ·
          refine ⟨5619512447943221967565997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14985366527848591913509325 5619512447943221967565997)
          ·
            refine ⟨2107317167978708237837249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5619512447943221967565997 2107317167978708237837249)
            ·
              refine ⟨1580487875984031178377937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2107317167978708237837249 1580487875984031178377937)
              ·
                refine ⟨1185365906988023383783453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1580487875984031178377937 1185365906988023383783453)
                ·
                  refine ⟨444512215120508768918795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185365906988023383783453 444512215120508768918795)
                  ·
                    rfl

theorem cell20_973895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 3].length) (baseStart_973895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973895 prefixEnd_973895 := by exact prefixLift 973895
  have htrace : WordTrace (prefixWord ++ tailWord_973895) baseStart_973895 baseEnd_973895 := by
    simpa [prefixWord, tailWord_973895, baseEnd_973895] using wordTrace_append hprefix tailTrace_973895
  have hstable : (prefixWord ++ tailWord_973895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973895).length < 2 ^ (prefixWord ++ tailWord_973895).sum := by decide
  have hdescent : baseEnd_973895 < baseStart_973895 := by decide
  rcases family_descends (prefixWord ++ tailWord_973895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973961 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 4]
def baseStart_973961 : Nat := 118140960795 + 973961 * 2 ^ 59
def prefixEnd_973961 : Nat := 4983230072969 + 3 ^ 40 * 973961 * 2
def baseEnd_973961 : Nat := 444542339318905872718525

theorem tailTrace_973961 : CollatzResearch.WordTrace tailWord_973961 prefixEnd_973961 444542339318905872718525 := by
  unfold tailWord_973961
  simp only [CollatzResearch.WordTrace]
  refine ⟨35523276024513111140961737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23682184016342074093974491 35523276024513111140961737)
  ·
    refine ⟨26642457018384833355721303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35523276024513111140961737 26642457018384833355721303)
    ·
      refine ⟨39963685527577250033581955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26642457018384833355721303 39963685527577250033581955)
      ·
        refine ⟨59945528291365875050372933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39963685527577250033581955 59945528291365875050372933)
        ·
          refine ⟨11239786554631101571944925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59945528291365875050372933 11239786554631101571944925)
          ·
            refine ⟨4214919957986663089479347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11239786554631101571944925 4214919957986663089479347)
            ·
              refine ⟨6322379936979994634219021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214919957986663089479347 6322379936979994634219021)
              ·
                refine ⟨2370892476367497987832133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6322379936979994634219021 2370892476367497987832133)
                ·
                  refine ⟨444542339318905872718525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2370892476367497987832133 444542339318905872718525)
                  ·
                    rfl

theorem cell20_973961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_973961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973961 prefixEnd_973961 := by exact prefixLift 973961
  have htrace : WordTrace (prefixWord ++ tailWord_973961) baseStart_973961 baseEnd_973961 := by
    simpa [prefixWord, tailWord_973961, baseEnd_973961] using wordTrace_append hprefix tailTrace_973961
  have hstable : (prefixWord ++ tailWord_973961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973961).length < 2 ^ (prefixWord ++ tailWord_973961).sum := by decide
  have hdescent : baseEnd_973961 < baseStart_973961 := by decide
  rcases family_descends (prefixWord ++ tailWord_973961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_973978 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_973978 : Nat := 118140960795 + 973978 * 2 ^ 59
def prefixEnd_973978 : Nat := 4983230072969 + 3 ^ 40 * 973978 * 2
def baseEnd_973978 : Nat := 444550098582129369151789

theorem tailTrace_973978 : CollatzResearch.WordTrace tailWord_973978 prefixEnd_973978 444550098582129369151789 := by
  unfold tailWord_973978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880974016362880761082647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23682597376967682029553725 8880974016362880761082647)
  ·
    refine ⟨13321461024544321141623971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8880974016362880761082647 13321461024544321141623971)
    ·
      refine ⟨19982191536816481712435957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13321461024544321141623971 19982191536816481712435957)
      ·
        refine ⟨1873330456576545160540871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19982191536816481712435957 1873330456576545160540871)
        ·
          refine ⟨2809995684864817740811307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873330456576545160540871 2809995684864817740811307)
          ·
            refine ⟨4214993527297226611216961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809995684864817740811307 4214993527297226611216961)
            ·
              refine ⟨3161245145472919958412721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4214993527297226611216961 3161245145472919958412721)
              ·
                refine ⟨2370933859104689968809541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161245145472919958412721 2370933859104689968809541)
                ·
                  refine ⟨444550098582129369151789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2370933859104689968809541 444550098582129369151789)
                  ·
                    rfl

theorem cell20_973978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_973978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_973978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_973978 prefixEnd_973978 := by exact prefixLift 973978
  have htrace : WordTrace (prefixWord ++ tailWord_973978) baseStart_973978 baseEnd_973978 := by
    simpa [prefixWord, tailWord_973978, baseEnd_973978] using wordTrace_append hprefix tailTrace_973978
  have hstable : (prefixWord ++ tailWord_973978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_973978).length < 2 ^ (prefixWord ++ tailWord_973978).sum := by decide
  have hdescent : baseEnd_973978 < baseStart_973978 := by decide
  rcases family_descends (prefixWord ++ tailWord_973978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974012 : List Nat := [2, 2, 2, 3, 2, 2, 3, 2, 2]
def baseStart_974012 : Nat := 118140960795 + 974012 * 2 ^ 59
def prefixEnd_974012 : Nat := 4983230072969 + 3 ^ 40 * 974012 * 2
def baseEnd_974012 : Nat := 444565617108576362018317

theorem tailTrace_974012 : CollatzResearch.WordTrace tailWord_974012 prefixEnd_974012 444565617108576362018317 := by
  unfold tailWord_974012
  simp only [CollatzResearch.WordTrace]
  refine ⟨17762568073664173425534145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23683424098218897900712193 17762568073664173425534145)
  ·
    refine ⟨13321926055248130069150609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17762568073664173425534145 13321926055248130069150609)
    ·
      refine ⟨9991444541436097551862957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13321926055248130069150609 9991444541436097551862957)
      ·
        refine ⟨3746791703038536581948609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9991444541436097551862957 3746791703038536581948609)
        ·
          refine ⟨2810093777278902436461457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3746791703038536581948609 2810093777278902436461457)
          ·
            refine ⟨2107570332959176827346093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2810093777278902436461457 2107570332959176827346093)
            ·
              refine ⟨790338874859691310254785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2107570332959176827346093 790338874859691310254785)
              ·
                refine ⟨592754156144768482691089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790338874859691310254785 592754156144768482691089)
                ·
                  refine ⟨444565617108576362018317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592754156144768482691089 444565617108576362018317)
                  ·
                    rfl

theorem cell20_974012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_974012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974012 prefixEnd_974012 := by exact prefixLift 974012
  have htrace : WordTrace (prefixWord ++ tailWord_974012) baseStart_974012 baseEnd_974012 := by
    simpa [prefixWord, tailWord_974012, baseEnd_974012] using wordTrace_append hprefix tailTrace_974012
  have hstable : (prefixWord ++ tailWord_974012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974012).length < 2 ^ (prefixWord ++ tailWord_974012).sum := by decide
  have hdescent : baseEnd_974012 < baseStart_974012 := by decide
  rcases family_descends (prefixWord ++ tailWord_974012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974022 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_974022 : Nat := 118140960795 + 974022 * 2 ^ 59
def prefixEnd_974022 : Nat := 4983230072969 + 3 ^ 40 * 974022 * 2
def baseEnd_974022 : Nat := 444570181381060771684943

theorem tailTrace_974022 : CollatzResearch.WordTrace tailWord_974022 prefixEnd_974022 444570181381060771684943 := by
  unfold tailWord_974022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110171902415378704966635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23683667251528079039288213 1110171902415378704966635)
  ·
    refine ⟨1665257853623068057449953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1110171902415378704966635 1665257853623068057449953)
    ·
      refine ⟨1248943390217301043087465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1665257853623068057449953 1248943390217301043087465)
      ·
        refine ⟨936707542662975782315599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1248943390217301043087465 936707542662975782315599)
        ·
          refine ⟨1405061313994463673473399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936707542662975782315599 1405061313994463673473399)
          ·
            refine ⟨2107591970991695510210099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405061313994463673473399 2107591970991695510210099)
            ·
              refine ⟨3161387956487543265315149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2107591970991695510210099 3161387956487543265315149)
              ·
                refine ⟨1185520483682828724493181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3161387956487543265315149 1185520483682828724493181)
                ·
                  refine ⟨444570181381060771684943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185520483682828724493181 444570181381060771684943)
                  ·
                    rfl

theorem cell20_974022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_974022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974022 prefixEnd_974022 := by exact prefixLift 974022
  have htrace : WordTrace (prefixWord ++ tailWord_974022) baseStart_974022 baseEnd_974022 := by
    simpa [prefixWord, tailWord_974022, baseEnd_974022] using wordTrace_append hprefix tailTrace_974022
  have hstable : (prefixWord ++ tailWord_974022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974022).length < 2 ^ (prefixWord ++ tailWord_974022).sum := by decide
  have hdescent : baseEnd_974022 < baseStart_974022 := by decide
  rcases family_descends (prefixWord ++ tailWord_974022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974026 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_974026 : Nat := 118140960795 + 974026 * 2 ^ 59
def prefixEnd_974026 : Nat := 4983230072969 + 3 ^ 40 * 974026 * 2
def baseEnd_974026 : Nat := 444572007090054535551593

theorem tailTrace_974026 : CollatzResearch.WordTrace tailWord_974026 prefixEnd_974026 444572007090054535551593 := by
  unfold tailWord_974026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8881411692319406810519483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23683764512851751494718621 8881411692319406810519483)
  ·
    refine ⟨13322117538479110215779225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8881411692319406810519483 13322117538479110215779225)
    ·
      refine ⟨9991588153859332661834419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13322117538479110215779225 9991588153859332661834419)
      ·
        refine ⟨14987382230788998992751629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9991588153859332661834419 14987382230788998992751629)
        ·
          refine ⟨5620268336545874622281861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14987382230788998992751629 5620268336545874622281861)
          ·
            refine ⟨1053800313102351491677849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5620268336545874622281861 1053800313102351491677849)
            ·
              refine ⟨790350234826763618758387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053800313102351491677849 790350234826763618758387)
              ·
                refine ⟨1185525352240145428137581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790350234826763618758387 1185525352240145428137581)
                ·
                  refine ⟨444572007090054535551593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185525352240145428137581 444572007090054535551593)
                  ·
                    rfl

theorem cell20_974026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_974026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974026 prefixEnd_974026 := by exact prefixLift 974026
  have htrace : WordTrace (prefixWord ++ tailWord_974026) baseStart_974026 baseEnd_974026 := by
    simpa [prefixWord, tailWord_974026, baseEnd_974026] using wordTrace_append hprefix tailTrace_974026
  have hstable : (prefixWord ++ tailWord_974026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974026).length < 2 ^ (prefixWord ++ tailWord_974026).sum := by decide
  have hdescent : baseEnd_974026 < baseStart_974026 := by decide
  rcases family_descends (prefixWord ++ tailWord_974026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974078 : List Nat := [4, 2, 2, 1, 1, 4, 1, 5]
def baseStart_974078 : Nat := 118140960795 + 974078 * 2 ^ 59
def prefixEnd_974078 : Nat := 4983230072969 + 3 ^ 40 * 974078 * 2
def baseEnd_974078 : Nat := 148198580435657821939349

theorem tailTrace_974078 : CollatzResearch.WordTrace tailWord_974078 prefixEnd_974078 148198580435657821939349 := by
  unfold tailWord_974078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4440942920636155015371361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23685028910059493415313925 4440942920636155015371361)
  ·
    refine ⟨3330707190477116261528521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4440942920636155015371361 3330707190477116261528521)
    ·
      refine ⟨2498030392857837196146391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3330707190477116261528521 2498030392857837196146391)
      ·
        refine ⟨3747045589286755794219587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2498030392857837196146391 3747045589286755794219587)
        ·
          refine ⟨5620568383930133691329381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3747045589286755794219587 5620568383930133691329381)
          ·
            refine ⟨1053856571986900067124259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5620568383930133691329381 1053856571986900067124259)
            ·
              refine ⟨1580784857980350100686389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053856571986900067124259 1580784857980350100686389)
              ·
                refine ⟨148198580435657821939349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1580784857980350100686389 148198580435657821939349)
                ·
                  rfl

theorem cell20_974078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_974078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974078 prefixEnd_974078 := by exact prefixLift 974078
  have htrace : WordTrace (prefixWord ++ tailWord_974078) baseStart_974078 baseEnd_974078 := by
    simpa [prefixWord, tailWord_974078, baseEnd_974078] using wordTrace_append hprefix tailTrace_974078
  have hstable : (prefixWord ++ tailWord_974078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974078).length < 2 ^ (prefixWord ++ tailWord_974078).sum := by decide
  have hdescent : baseEnd_974078 < baseStart_974078 := by decide
  rcases family_descends (prefixWord ++ tailWord_974078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974109 : List Nat := [1, 4, 2, 3, 1, 1, 1, 5, 2]
def baseStart_974109 : Nat := 118140960795 + 974109 * 2 ^ 59
def prefixEnd_974109 : Nat := 4983230072969 + 3 ^ 40 * 974109 * 2
def baseEnd_974109 : Nat := 444609890551675135784587

theorem tailTrace_974109 : CollatzResearch.WordTrace tailWord_974109 prefixEnd_974109 444609890551675135784587 := by
  unfold tailWord_974109
  simp only [CollatzResearch.WordTrace]
  refine ⟨35528674027976932417349381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23685782685317954944899587 35528674027976932417349381)
  ·
    refine ⟨6661626380245674828253009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35528674027976932417349381 6661626380245674828253009)
    ·
      refine ⟨4996219785184256121189757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6661626380245674828253009 4996219785184256121189757)
      ·
        refine ⟨1873582419444096045446159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4996219785184256121189757 1873582419444096045446159)
        ·
          refine ⟨2810373629166144068169239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873582419444096045446159 2810373629166144068169239)
          ·
            refine ⟨4215560443749216102253859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2810373629166144068169239 4215560443749216102253859)
            ·
              refine ⟨6323340665623824153380789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4215560443749216102253859 6323340665623824153380789)
              ·
                refine ⟨592813187402233514379449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6323340665623824153380789 592813187402233514379449)
                ·
                  refine ⟨444609890551675135784587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592813187402233514379449 444609890551675135784587)
                  ·
                    rfl

theorem cell20_974109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_974109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974109 prefixEnd_974109 := by exact prefixLift 974109
  have htrace : WordTrace (prefixWord ++ tailWord_974109) baseStart_974109 baseEnd_974109 := by
    simpa [prefixWord, tailWord_974109, baseEnd_974109] using wordTrace_append hprefix tailTrace_974109
  have hstable : (prefixWord ++ tailWord_974109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974109).length < 2 ^ (prefixWord ++ tailWord_974109).sum := by decide
  have hdescent : baseEnd_974109 < baseStart_974109 := by decide
  rcases family_descends (prefixWord ++ tailWord_974109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974130 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_974130 : Nat := 118140960795 + 974130 * 2 ^ 59
def prefixEnd_974130 : Nat := 4983230072969 + 3 ^ 40 * 974130 * 2
def baseEnd_974130 : Nat := 444619475523892396084501

theorem tailTrace_974130 : CollatzResearch.WordTrace tailWord_974130 prefixEnd_974130 444619475523892396084501 := by
  unfold tailWord_974130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8882359990225213250965961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23686293307267235335909229 8882359990225213250965961)
  ·
    refine ⟨6661769992668909938224471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8882359990225213250965961 6661769992668909938224471)
    ·
      refine ⟨9992654989003364907336707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6661769992668909938224471 9992654989003364907336707)
      ·
        refine ⟨14988982483505047361005061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9992654989003364907336707 14988982483505047361005061)
        ·
          refine ⟨2810434215657196380188449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14988982483505047361005061 2810434215657196380188449)
          ·
            refine ⟨2107825661742897285141337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2810434215657196380188449 2107825661742897285141337)
            ·
              refine ⟨1580869246307172963856003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2107825661742897285141337 1580869246307172963856003)
              ·
                refine ⟨2371303869460759445784005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1580869246307172963856003 2371303869460759445784005)
                ·
                  refine ⟨444619475523892396084501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371303869460759445784005 444619475523892396084501)
                  ·
                    rfl

theorem cell20_974130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_974130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974130 prefixEnd_974130 := by exact prefixLift 974130
  have htrace : WordTrace (prefixWord ++ tailWord_974130) baseStart_974130 baseEnd_974130 := by
    simpa [prefixWord, tailWord_974130, baseEnd_974130] using wordTrace_append hprefix tailTrace_974130
  have hstable : (prefixWord ++ tailWord_974130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974130).length < 2 ^ (prefixWord ++ tailWord_974130).sum := by decide
  have hdescent : baseEnd_974130 < baseStart_974130 := by decide
  rcases family_descends (prefixWord ++ tailWord_974130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974151 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 4]
def baseStart_974151 : Nat := 118140960795 + 974151 * 2 ^ 59
def prefixEnd_974151 : Nat := 4983230072969 + 3 ^ 40 * 974151 * 2
def baseEnd_974151 : Nat := 444629060496109656384415

theorem tailTrace_974151 : CollatzResearch.WordTrace tailWord_974151 prefixEnd_974151 444629060496109656384415 := by
  unfold tailWord_974151
  simp only [CollatzResearch.WordTrace]
  refine ⟨35530205893824773590378307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23686803929216515726918871 35530205893824773590378307)
  ·
    refine ⟨53295308840737160385567461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35530205893824773590378307 53295308840737160385567461)
    ·
      refine ⟨9992870407638217572293899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53295308840737160385567461 9992870407638217572293899)
      ·
        refine ⟨14989305611457326358440849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9992870407638217572293899 14989305611457326358440849)
        ·
          refine ⟨11241979208592994768830637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14989305611457326358440849 11241979208592994768830637)
          ·
            refine ⟨4215742203222373038311489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11241979208592994768830637 4215742203222373038311489)
            ·
              refine ⟨3161806652416779778733617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4215742203222373038311489 3161806652416779778733617)
              ·
                refine ⟨2371354989312584834050213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3161806652416779778733617 2371354989312584834050213)
                ·
                  refine ⟨444629060496109656384415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371354989312584834050213 444629060496109656384415)
                  ·
                    rfl

theorem cell20_974151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_974151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974151 prefixEnd_974151 := by exact prefixLift 974151
  have htrace : WordTrace (prefixWord ++ tailWord_974151) baseStart_974151 baseEnd_974151 := by
    simpa [prefixWord, tailWord_974151, baseEnd_974151] using wordTrace_append hprefix tailTrace_974151
  have hstable : (prefixWord ++ tailWord_974151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974151).length < 2 ^ (prefixWord ++ tailWord_974151).sum := by decide
  have hdescent : baseEnd_974151 < baseStart_974151 := by decide
  rcases family_descends (prefixWord ++ tailWord_974151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974158 : List Nat := [4, 1, 1, 1, 1, 1, 5, 6]
def baseStart_974158 : Nat := 118140960795 + 974158 * 2 ^ 59
def prefixEnd_974158 : Nat := 4983230072969 + 3 ^ 40 * 974158 * 2
def baseEnd_974158 : Nat := 148210751828949581050351

theorem tailTrace_974158 : CollatzResearch.WordTrace tailWord_974158 prefixEnd_974158 148210751828949581050351 := by
  unfold tailWord_974158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4441307650599926723235391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23686974136532942523922085 4441307650599926723235391)
  ·
    refine ⟨6661961475899890084853087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4441307650599926723235391 6661961475899890084853087)
    ·
      refine ⟨9992942213849835127279631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6661961475899890084853087 9992942213849835127279631)
      ·
        refine ⟨14989413320774752690919447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9992942213849835127279631 14989413320774752690919447)
        ·
          refine ⟨22484119981162129036379171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14989413320774752690919447 22484119981162129036379171)
          ·
            refine ⟨33726179971743193554568757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22484119981162129036379171 33726179971743193554568757)
            ·
              refine ⟨3161829372350924395740821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33726179971743193554568757 3161829372350924395740821)
              ·
                refine ⟨148210751828949581050351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3161829372350924395740821 148210751828949581050351)
                ·
                  rfl

theorem cell20_974158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_974158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974158 prefixEnd_974158 := by exact prefixLift 974158
  have htrace : WordTrace (prefixWord ++ tailWord_974158) baseStart_974158 baseEnd_974158 := by
    simpa [prefixWord, tailWord_974158, baseEnd_974158] using wordTrace_append hprefix tailTrace_974158
  have hstable : (prefixWord ++ tailWord_974158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974158).length < 2 ^ (prefixWord ++ tailWord_974158).sum := by decide
  have hdescent : baseEnd_974158 < baseStart_974158 := by decide
  rcases family_descends (prefixWord ++ tailWord_974158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974236 : List Nat := [2, 2, 3, 4, 2, 1, 2, 2, 2]
def baseStart_974236 : Nat := 118140960795 + 974236 * 2 ^ 59
def prefixEnd_974236 : Nat := 4983230072969 + 3 ^ 40 * 974236 * 2
def baseEnd_974236 : Nat := 444667856812227138550735

theorem tailTrace_974236 : CollatzResearch.WordTrace tailWord_974236 prefixEnd_974236 444667856812227138550735 := by
  unfold tailWord_974236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17766653049258416553611281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23688870732344555404815041 17766653049258416553611281)
  ·
    refine ⟨13324989786943812415208461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17766653049258416553611281 13324989786943812415208461)
    ·
      refine ⟨4996871170103929655703173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13324989786943812415208461 4996871170103929655703173)
      ·
        refine ⟨936913344394486810444345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4996871170103929655703173 936913344394486810444345)
        ·
          refine ⟨702685008295865107833259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 936913344394486810444345 702685008295865107833259)
          ·
            refine ⟨1054027512443797661749889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702685008295865107833259 1054027512443797661749889)
            ·
              refine ⟨790520634332848246312417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054027512443797661749889 790520634332848246312417)
              ·
                refine ⟨592890475749636184734313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790520634332848246312417 592890475749636184734313)
                ·
                  refine ⟨444667856812227138550735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592890475749636184734313 444667856812227138550735)
                  ·
                    rfl

theorem cell20_974236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_974236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974236 prefixEnd_974236 := by exact prefixLift 974236
  have htrace : WordTrace (prefixWord ++ tailWord_974236) baseStart_974236 baseEnd_974236 := by
    simpa [prefixWord, tailWord_974236, baseEnd_974236] using wordTrace_append hprefix tailTrace_974236
  have hstable : (prefixWord ++ tailWord_974236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974236).length < 2 ^ (prefixWord ++ tailWord_974236).sum := by decide
  have hdescent : baseEnd_974236 < baseStart_974236 := by decide
  rcases family_descends (prefixWord ++ tailWord_974236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974237 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 3]
def baseStart_974237 : Nat := 118140960795 + 974237 * 2 ^ 59
def prefixEnd_974237 : Nat := 4983230072969 + 3 ^ 40 * 974237 * 2
def baseEnd_974237 : Nat := 444668313239475579517397

theorem tailTrace_974237 : CollatzResearch.WordTrace tailWord_974237 prefixEnd_974237 444668313239475579517397 := by
  unfold tailWord_974237
  simp only [CollatzResearch.WordTrace]
  refine ⟨35533342571513210278008965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23688895047675473518672643 35533342571513210278008965)
  ·
    refine ⟨6662501732158726927126681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35533342571513210278008965 6662501732158726927126681)
    ·
      refine ⟨4996876299119045195345011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6662501732158726927126681 4996876299119045195345011)
      ·
        refine ⟨7495314448678567793017517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4996876299119045195345011 7495314448678567793017517)
        ·
          refine ⟨2810742918254462922381569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7495314448678567793017517 2810742918254462922381569)
          ·
            refine ⟨2108057188690847191786177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2810742918254462922381569 2108057188690847191786177)
            ·
              refine ⟨1581042891518135393839633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2108057188690847191786177 1581042891518135393839633)
              ·
                refine ⟨1185782168638601545379725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581042891518135393839633 1185782168638601545379725)
                ·
                  refine ⟨444668313239475579517397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185782168638601545379725 444668313239475579517397)
                  ·
                    rfl

theorem cell20_974237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_974237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974237 prefixEnd_974237 := by exact prefixLift 974237
  have htrace : WordTrace (prefixWord ++ tailWord_974237) baseStart_974237 baseEnd_974237 := by
    simpa [prefixWord, tailWord_974237, baseEnd_974237] using wordTrace_append hprefix tailTrace_974237
  have hstable : (prefixWord ++ tailWord_974237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974237).length < 2 ^ (prefixWord ++ tailWord_974237).sum := by decide
  have hdescent : baseEnd_974237 < baseStart_974237 := by decide
  rcases family_descends (prefixWord ++ tailWord_974237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974268 : List Nat := [2, 2, 2, 4, 2, 1, 3, 4]
def baseStart_974268 : Nat := 118140960795 + 974268 * 2 ^ 59
def prefixEnd_974268 : Nat := 4983230072969 + 3 ^ 40 * 974268 * 2
def baseEnd_974268 : Nat := 148227487494725749827979

theorem tailTrace_974268 : CollatzResearch.WordTrace tailWord_974268 prefixEnd_974268 148227487494725749827979 := by
  unfold tailWord_974268
  simp only [CollatzResearch.WordTrace]
  refine ⟨17767236617200451286193729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23689648822933935048258305 17767236617200451286193729)
  ·
    refine ⟨13325427462900338464645297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17767236617200451286193729 13325427462900338464645297)
    ·
      refine ⟨9994070597175253848483973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13325427462900338464645297 9994070597175253848483973)
      ·
        refine ⟨1873888236970360096590745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9994070597175253848483973 1873888236970360096590745)
        ·
          refine ⟨1405416177727770072443059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1873888236970360096590745 1405416177727770072443059)
          ·
            refine ⟨2108124266591655108664589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405416177727770072443059 2108124266591655108664589)
            ·
              refine ⟨790546599971870665749221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2108124266591655108664589 790546599971870665749221)
              ·
                refine ⟨148227487494725749827979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 790546599971870665749221 148227487494725749827979)
                ·
                  rfl

theorem cell20_974268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_974268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974268 prefixEnd_974268 := by exact prefixLift 974268
  have htrace : WordTrace (prefixWord ++ tailWord_974268) baseStart_974268 baseEnd_974268 := by
    simpa [prefixWord, tailWord_974268, baseEnd_974268] using wordTrace_append hprefix tailTrace_974268
  have hstable : (prefixWord ++ tailWord_974268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974268).length < 2 ^ (prefixWord ++ tailWord_974268).sum := by decide
  have hdescent : baseEnd_974268 < baseStart_974268 := by decide
  rcases family_descends (prefixWord ++ tailWord_974268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974279 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_974279 : Nat := 118140960795 + 974279 * 2 ^ 59
def prefixEnd_974279 : Nat := 4983230072969 + 3 ^ 40 * 974279 * 2
def baseEnd_974279 : Nat := 444687483183910100117225

theorem tailTrace_974279 : CollatzResearch.WordTrace tailWord_974279 prefixEnd_974279 444687483183910100117225 := by
  unfold tailWord_974279
  simp only [CollatzResearch.WordTrace]
  refine ⟨35534874437361051451037891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23689916291574034300691927 35534874437361051451037891)
  ·
    refine ⟨53302311656041577176556837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35534874437361051451037891 53302311656041577176556837)
    ·
      refine ⟨9994183435507795720604407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53302311656041577176556837 9994183435507795720604407)
      ·
        refine ⟨14991275153261693580906611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9994183435507795720604407 14991275153261693580906611)
        ·
          refine ⟨22486912729892540371359917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14991275153261693580906611 22486912729892540371359917)
          ·
            refine ⟨8432592273709702639259969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22486912729892540371359917 8432592273709702639259969)
            ·
              refine ⟨6324444205282276979444977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8432592273709702639259969 6324444205282276979444977)
              ·
                refine ⟨4743333153961707734583733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6324444205282276979444977 4743333153961707734583733)
                ·
                  refine ⟨444687483183910100117225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4743333153961707734583733 444687483183910100117225)
                  ·
                    rfl

theorem cell20_974279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_974279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974279 prefixEnd_974279 := by exact prefixLift 974279
  have htrace : WordTrace (prefixWord ++ tailWord_974279) baseStart_974279 baseEnd_974279 := by
    simpa [prefixWord, tailWord_974279, baseEnd_974279] using wordTrace_append hprefix tailTrace_974279
  have hstable : (prefixWord ++ tailWord_974279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974279).length < 2 ^ (prefixWord ++ tailWord_974279).sum := by decide
  have hdescent : baseEnd_974279 < baseStart_974279 := by decide
  rcases family_descends (prefixWord ++ tailWord_974279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974282 : List Nat := [3, 1, 2, 1, 2, 3, 1, 5, 2]
def baseStart_974282 : Nat := 118140960795 + 974282 * 2 ^ 59
def prefixEnd_974282 : Nat := 4983230072969 + 3 ^ 40 * 974282 * 2
def baseEnd_974282 : Nat := 444688852465655423017213

theorem tailTrace_974282 : CollatzResearch.WordTrace tailWord_974282 prefixEnd_974282 444688852465655423017213 := by
  unfold tailWord_974282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8883745964087545740849275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23689989237566788642264733 8883745964087545740849275)
  ·
    refine ⟨13325618946131318611273913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8883745964087545740849275 13325618946131318611273913)
    ·
      refine ⟨9994214209598488958455435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13325618946131318611273913 9994214209598488958455435)
      ·
        refine ⟨14991321314397733437683153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9994214209598488958455435 14991321314397733437683153)
        ·
          refine ⟨11243490985798300078262365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14991321314397733437683153 11243490985798300078262365)
          ·
            refine ⟨4216309119674362529348387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11243490985798300078262365 4216309119674362529348387)
            ·
              refine ⟨6324463679511543794022581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4216309119674362529348387 6324463679511543794022581)
              ·
                refine ⟨592918469954207230689617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6324463679511543794022581 592918469954207230689617)
                ·
                  refine ⟨444688852465655423017213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 592918469954207230689617 444688852465655423017213)
                  ·
                    rfl

theorem cell20_974282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_974282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974282 prefixEnd_974282 := by exact prefixLift 974282
  have htrace : WordTrace (prefixWord ++ tailWord_974282) baseStart_974282 baseEnd_974282 := by
    simpa [prefixWord, tailWord_974282, baseEnd_974282] using wordTrace_append hprefix tailTrace_974282
  have hstable : (prefixWord ++ tailWord_974282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974282).length < 2 ^ (prefixWord ++ tailWord_974282).sum := by decide
  have hdescent : baseEnd_974282 < baseStart_974282 := by decide
  rcases family_descends (prefixWord ++ tailWord_974282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974292 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 3]
def baseStart_974292 : Nat := 118140960795 + 974292 * 2 ^ 59
def prefixEnd_974292 : Nat := 4983230072969 + 3 ^ 40 * 974292 * 2
def baseEnd_974292 : Nat := 444693416738139832683839

theorem tailTrace_974292 : CollatzResearch.WordTrace tailWord_974292 prefixEnd_974292 444693416738139832683839 := by
  unfold tailWord_974292
  simp only [CollatzResearch.WordTrace]
  refine ⟨17767674293156977335630565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23690232390875969780840753 17767674293156977335630565)
  ·
    refine ⟨3331438929966933250430731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17767674293156977335630565 3331438929966933250430731)
    ·
      refine ⟨4997158394950399875646097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3331438929966933250430731 4997158394950399875646097)
      ·
        refine ⟨3747868796212799906734573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4997158394950399875646097 3747868796212799906734573)
        ·
          refine ⟨1405450798579799965025465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3747868796212799906734573 1405450798579799965025465)
          ·
            refine ⟨1054088098934849973769099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1405450798579799965025465 1054088098934849973769099)
            ·
              refine ⟨1581132148402274960653649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054088098934849973769099 1581132148402274960653649)
              ·
                refine ⟨1185849111301706220490237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581132148402274960653649 1185849111301706220490237)
                ·
                  refine ⟨444693416738139832683839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185849111301706220490237 444693416738139832683839)
                  ·
                    rfl

theorem cell20_974292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_974292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974292 prefixEnd_974292 := by exact prefixLift 974292
  have htrace : WordTrace (prefixWord ++ tailWord_974292) baseStart_974292 baseEnd_974292 := by
    simpa [prefixWord, tailWord_974292, baseEnd_974292] using wordTrace_append hprefix tailTrace_974292
  have hstable : (prefixWord ++ tailWord_974292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974292).length < 2 ^ (prefixWord ++ tailWord_974292).sum := by decide
  have hdescent : baseEnd_974292 < baseStart_974292 := by decide
  rcases family_descends (prefixWord ++ tailWord_974292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974296 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 3]
def baseStart_974296 : Nat := 118140960795 + 974296 * 2 ^ 59
def prefixEnd_974296 : Nat := 4983230072969 + 3 ^ 40 * 974296 * 2
def baseEnd_974296 : Nat := 444695242447133596550489

theorem tailTrace_974296 : CollatzResearch.WordTrace tailWord_974296 prefixEnd_974296 444695242447133596550489 := by
  unfold tailWord_974296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17767747239149731677203371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23690329652199642236271161 17767747239149731677203371)
  ·
    refine ⟨26651620858724597515805057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17767747239149731677203371 26651620858724597515805057)
    ·
      refine ⟨19988715644043448136853793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26651620858724597515805057 19988715644043448136853793)
      ·
        refine ⟨14991536733032586102640345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19988715644043448136853793 14991536733032586102640345)
        ·
          refine ⟨11243652549774439576980259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14991536733032586102640345 11243652549774439576980259)
          ·
            refine ⟨16865478824661659365470389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11243652549774439576980259 16865478824661659365470389)
            ·
              refine ⟨1581138639812030565512849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16865478824661659365470389 1581138639812030565512849)
              ·
                refine ⟨1185853979859022924134637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581138639812030565512849 1185853979859022924134637)
                ·
                  refine ⟨444695242447133596550489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185853979859022924134637 444695242447133596550489)
                  ·
                    rfl

theorem cell20_974296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_974296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974296 prefixEnd_974296 := by exact prefixLift 974296
  have htrace : WordTrace (prefixWord ++ tailWord_974296) baseStart_974296 baseEnd_974296 := by
    simpa [prefixWord, tailWord_974296, baseEnd_974296] using wordTrace_append hprefix tailTrace_974296
  have hstable : (prefixWord ++ tailWord_974296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974296).length < 2 ^ (prefixWord ++ tailWord_974296).sum := by decide
  have hdescent : baseEnd_974296 < baseStart_974296 := by decide
  rcases family_descends (prefixWord ++ tailWord_974296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974303 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 4]
def baseStart_974303 : Nat := 118140960795 + 974303 * 2 ^ 59
def prefixEnd_974303 : Nat := 4983230072969 + 3 ^ 40 * 974303 * 2
def baseEnd_974303 : Nat := 444698437437872683317127

theorem tailTrace_974303 : CollatzResearch.WordTrace tailWord_974303 prefixEnd_974303 444698437437872683317127 := by
  unfold tailWord_974303
  simp only [CollatzResearch.WordTrace]
  refine ⟨35535749789274103549911563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23690499859516069033274375 35535749789274103549911563)
  ·
    refine ⟨53303624683911155324867345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35535749789274103549911563 53303624683911155324867345)
    ·
      refine ⟨39977718512933366493650509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53303624683911155324867345 39977718512933366493650509)
      ·
        refine ⟨14991644442350012435118941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39977718512933366493650509 14991644442350012435118941)
        ·
          refine ⟨5621866665881254663169603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14991644442350012435118941 5621866665881254663169603)
          ·
            refine ⟨8432799998821881994754405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5621866665881254663169603 8432799998821881994754405)
            ·
              refine ⟨1581149999779102874016451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8432799998821881994754405 1581149999779102874016451)
              ·
                refine ⟨2371724999668654311024677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1581149999779102874016451 2371724999668654311024677)
                ·
                  refine ⟨444698437437872683317127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2371724999668654311024677 444698437437872683317127)
                  ·
                    rfl

theorem cell20_974303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_974303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974303 prefixEnd_974303 := by exact prefixLift 974303
  have htrace : WordTrace (prefixWord ++ tailWord_974303) baseStart_974303 baseEnd_974303 := by
    simpa [prefixWord, tailWord_974303, baseEnd_974303] using wordTrace_append hprefix tailTrace_974303
  have hstable : (prefixWord ++ tailWord_974303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974303).length < 2 ^ (prefixWord ++ tailWord_974303).sum := by decide
  have hdescent : baseEnd_974303 < baseStart_974303 := by decide
  rcases family_descends (prefixWord ++ tailWord_974303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974331 : List Nat := [1, 1, 1, 1, 1, 3, 2, 10]
def baseStart_974331 : Nat := 118140960795 + 974331 * 2 ^ 59
def prefixEnd_974331 : Nat := 4983230072969 + 3 ^ 40 * 974331 * 2
def baseEnd_974331 : Nat := 148237072466943010127893

theorem tailTrace_974331 : CollatzResearch.WordTrace tailWord_974331 prefixEnd_974331 148237072466943010127893 := by
  unfold tailWord_974331
  simp only [CollatzResearch.WordTrace]
  refine ⟨35536771033172664331930847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23691180688781776221287231 35536771033172664331930847)
  ·
    refine ⟨53305156549758996497896271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35536771033172664331930847 53305156549758996497896271)
    ·
      refine ⟨79957734824638494746844407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53305156549758996497896271 79957734824638494746844407)
      ·
        refine ⟨119936602236957742120266611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79957734824638494746844407 119936602236957742120266611)
        ·
          refine ⟨179904903355436613180399917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119936602236957742120266611 179904903355436613180399917)
          ·
            refine ⟨67464338758288729942649969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179904903355436613180399917 67464338758288729942649969)
            ·
              refine ⟨50598254068716547456987477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67464338758288729942649969 50598254068716547456987477)
              ·
                refine ⟨148237072466943010127893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50598254068716547456987477 148237072466943010127893)
                ·
                  rfl

theorem cell20_974331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_974331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974331 prefixEnd_974331 := by exact prefixLift 974331
  have htrace : WordTrace (prefixWord ++ tailWord_974331) baseStart_974331 baseEnd_974331 := by
    simpa [prefixWord, tailWord_974331, baseEnd_974331] using wordTrace_append hprefix tailTrace_974331
  have hstable : (prefixWord ++ tailWord_974331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974331).length < 2 ^ (prefixWord ++ tailWord_974331).sum := by decide
  have hdescent : baseEnd_974331 < baseStart_974331 := by decide
  rcases family_descends (prefixWord ++ tailWord_974331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974355 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 5]
def baseStart_974355 : Nat := 118140960795 + 974355 * 2 ^ 59
def prefixEnd_974355 : Nat := 4983230072969 + 3 ^ 40 * 974355 * 2
def baseEnd_974355 : Nat := 444722171654791613583581

theorem tailTrace_974355 : CollatzResearch.WordTrace tailWord_974355 prefixEnd_974355 444722171654791613583581 := by
  unfold tailWord_974355
  simp only [CollatzResearch.WordTrace]
  refine ⟨35537646385085716430804519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23691764256723810953869679 35537646385085716430804519)
  ·
    refine ⟨53306469577628574646206779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35537646385085716430804519 53306469577628574646206779)
    ·
      refine ⟨79959704366442861969310169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53306469577628574646206779 79959704366442861969310169)
      ·
        refine ⟨59969778274832146476982627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79959704366442861969310169 59969778274832146476982627)
        ·
          refine ⟨89954667412248219715473941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59969778274832146476982627 89954667412248219715473941)
          ·
            refine ⟨4216625034949135299162841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89954667412248219715473941 4216625034949135299162841)
            ·
              refine ⟨3162468776211851474372131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4216625034949135299162841 3162468776211851474372131)
              ·
                refine ⟨4743703164317777211558197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162468776211851474372131 4743703164317777211558197)
                ·
                  refine ⟨444722171654791613583581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4743703164317777211558197 444722171654791613583581)
                  ·
                    rfl

theorem cell20_974355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_974355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974355 prefixEnd_974355 := by exact prefixLift 974355
  have htrace : WordTrace (prefixWord ++ tailWord_974355) baseStart_974355 baseEnd_974355 := by
    simpa [prefixWord, tailWord_974355, baseEnd_974355] using wordTrace_append hprefix tailTrace_974355
  have hstable : (prefixWord ++ tailWord_974355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974355).length < 2 ^ (prefixWord ++ tailWord_974355).sum := by decide
  have hdescent : baseEnd_974355 < baseStart_974355 := by decide
  rcases family_descends (prefixWord ++ tailWord_974355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974368 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 3]
def baseStart_974368 : Nat := 118140960795 + 974368 * 2 ^ 59
def prefixEnd_974368 : Nat := 4983230072969 + 3 ^ 40 * 974368 * 2
def baseEnd_974368 : Nat := 444728105209021346150195

theorem tailTrace_974368 : CollatzResearch.WordTrace tailWord_974368 prefixEnd_974368 444728105209021346150195 := by
  unfold tailWord_974368
  simp only [CollatzResearch.WordTrace]
  refine ⟨17769060267019309825513879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23692080356025746434018505 17769060267019309825513879)
  ·
    refine ⟨26653590400528964738270819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17769060267019309825513879 26653590400528964738270819)
    ·
      refine ⟨39980385600793447107406229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26653590400528964738270819 39980385600793447107406229)
      ·
        refine ⟨1874080575037192833159667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39980385600793447107406229 1874080575037192833159667)
        ·
          refine ⟨2811120862555789249739501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874080575037192833159667 2811120862555789249739501)
          ·
            refine ⟨1054170323458420968652313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2811120862555789249739501 1054170323458420968652313)
            ·
              refine ⟨790627742593815726489235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054170323458420968652313 790627742593815726489235)
              ·
                refine ⟨1185941613890723589733853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790627742593815726489235 1185941613890723589733853)
                ·
                  refine ⟨444728105209021346150195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185941613890723589733853 444728105209021346150195)
                  ·
                    rfl

theorem cell20_974368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_974368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974368 prefixEnd_974368 := by exact prefixLift 974368
  have htrace : WordTrace (prefixWord ++ tailWord_974368) baseStart_974368 baseEnd_974368 := by
    simpa [prefixWord, tailWord_974368, baseEnd_974368] using wordTrace_append hprefix tailTrace_974368
  have hstable : (prefixWord ++ tailWord_974368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974368).length < 2 ^ (prefixWord ++ tailWord_974368).sum := by decide
  have hdescent : baseEnd_974368 < baseStart_974368 := by decide
  rcases family_descends (prefixWord ++ tailWord_974368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974407 : List Nat := [1, 1, 4, 1, 13]
def baseStart_974407 : Nat := 118140960795 + 974407 * 2 ^ 59
def prefixEnd_974407 : Nat := 4983230072969 + 3 ^ 40 * 974407 * 2
def baseEnd_974407 : Nat := 5490690195947043751235

theorem tailTrace_974407 : CollatzResearch.WordTrace tailWord_974407 prefixEnd_974407 5490690195947043751235 := by
  unfold tailWord_974407
  simp only [CollatzResearch.WordTrace]
  refine ⟨35539542980897329311697475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23693028653931552874464983 35539542980897329311697475)
  ·
    refine ⟨53309314471345993967546213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35539542980897329311697475 53309314471345993967546213)
    ·
      refine ⟨9995496463377373868914915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53309314471345993967546213 9995496463377373868914915)
      ·
        refine ⟨14993244695066060803372373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9995496463377373868914915 14993244695066060803372373)
        ·
          refine ⟨5490690195947043751235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 14993244695066060803372373 5490690195947043751235)
          ·
            rfl

theorem cell20_974407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 13].length) (baseStart_974407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974407 prefixEnd_974407 := by exact prefixLift 974407
  have htrace : WordTrace (prefixWord ++ tailWord_974407) baseStart_974407 baseEnd_974407 := by
    simpa [prefixWord, tailWord_974407, baseEnd_974407] using wordTrace_append hprefix tailTrace_974407
  have hstable : (prefixWord ++ tailWord_974407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974407).length < 2 ^ (prefixWord ++ tailWord_974407).sum := by decide
  have hdescent : baseEnd_974407 < baseStart_974407 := by decide
  rcases family_descends (prefixWord ++ tailWord_974407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974410 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_974410 : Nat := 118140960795 + 974410 * 2 ^ 59
def prefixEnd_974410 : Nat := 4983230072969 + 3 ^ 40 * 974410 * 2
def baseEnd_974410 : Nat := 444747275153455866750023

theorem tailTrace_974410 : CollatzResearch.WordTrace tailWord_974410 prefixEnd_974410 444747275153455866750023 := by
  unfold tailWord_974410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8884913099971615206014171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23693101599924307216037789 8884913099971615206014171)
  ·
    refine ⟨13327369649957422809021257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8884913099971615206014171 13327369649957422809021257)
    ·
      refine ⟨9995527237468067106765943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13327369649957422809021257 9995527237468067106765943)
      ·
        refine ⟨14993290856202100660148915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9995527237468067106765943 14993290856202100660148915)
        ·
          refine ⟨22489936284303150990223373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14993290856202100660148915 22489936284303150990223373)
          ·
            refine ⟨8433726106613681621333765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22489936284303150990223373 8433726106613681621333765)
            ·
              refine ⟨1581323644990065304000081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8433726106613681621333765 1581323644990065304000081)
              ·
                refine ⟨1185992733742548978000061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581323644990065304000081 1185992733742548978000061)
                ·
                  refine ⟨444747275153455866750023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1185992733742548978000061 444747275153455866750023)
                  ·
                    rfl

theorem cell20_974410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_974410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974410 prefixEnd_974410 := by exact prefixLift 974410
  have htrace : WordTrace (prefixWord ++ tailWord_974410) baseStart_974410 baseEnd_974410 := by
    simpa [prefixWord, tailWord_974410, baseEnd_974410] using wordTrace_append hprefix tailTrace_974410
  have hstable : (prefixWord ++ tailWord_974410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974410).length < 2 ^ (prefixWord ++ tailWord_974410).sum := by decide
  have hdescent : baseEnd_974410 < baseStart_974410 := by decide
  rcases family_descends (prefixWord ++ tailWord_974410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974465 : List Nat := [1, 2, 4, 2, 1, 4, 1, 2, 3]
def baseStart_974465 : Nat := 118140960795 + 974465 * 2 ^ 59
def prefixEnd_974465 : Nat := 4983230072969 + 3 ^ 40 * 974465 * 2
def baseEnd_974465 : Nat := 444772378652120119916465

theorem tailTrace_974465 : CollatzResearch.WordTrace tailWord_974465 prefixEnd_974465 444772378652120119916465 := by
  unfold tailWord_974465
  simp only [CollatzResearch.WordTrace]
  refine ⟨35541658414687205217308849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23694438943124803478205899 35541658414687205217308849)
  ·
    refine ⟨26656243811015403912981637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35541658414687205217308849 26656243811015403912981637)
    ·
      refine ⟨4998045714565388233684057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26656243811015403912981637 4998045714565388233684057)
      ·
        refine ⟨3748534285924041175263043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4998045714565388233684057 3748534285924041175263043)
        ·
          refine ⟨5622801428886061762894565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3748534285924041175263043 5622801428886061762894565)
          ·
            refine ⟨1054275267916136580542731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5622801428886061762894565 1054275267916136580542731)
            ·
              refine ⟨1581412901874204870814097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054275267916136580542731 1581412901874204870814097)
              ·
                refine ⟨1186059676405653653110573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1581412901874204870814097 1186059676405653653110573)
                ·
                  refine ⟨444772378652120119916465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186059676405653653110573 444772378652120119916465)
                  ·
                    rfl

theorem cell20_974465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_974465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974465 prefixEnd_974465 := by exact prefixLift 974465
  have htrace : WordTrace (prefixWord ++ tailWord_974465) baseStart_974465 baseEnd_974465 := by
    simpa [prefixWord, tailWord_974465, baseEnd_974465] using wordTrace_append hprefix tailTrace_974465
  have hstable : (prefixWord ++ tailWord_974465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974465).length < 2 ^ (prefixWord ++ tailWord_974465).sum := by decide
  have hdescent : baseEnd_974465 < baseStart_974465 := by decide
  rcases family_descends (prefixWord ++ tailWord_974465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974469 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 5]
def baseStart_974469 : Nat := 118140960795 + 974469 * 2 ^ 59
def prefixEnd_974469 : Nat := 4983230072969 + 3 ^ 40 * 974469 * 2
def baseEnd_974469 : Nat := 444774204361113883783115

theorem tailTrace_974469 : CollatzResearch.WordTrace tailWord_974469 prefixEnd_974469 444774204361113883783115 := by
  unfold tailWord_974469
  simp only [CollatzResearch.WordTrace]
  refine ⟨35541804306672713900454461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23694536204448475933636307 35541804306672713900454461)
  ·
    refine ⟨13328176615002267712670423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35541804306672713900454461 13328176615002267712670423)
    ·
      refine ⟨19992264922503401569005635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13328176615002267712670423 19992264922503401569005635)
      ·
        refine ⟨29988397383755102353508453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19992264922503401569005635 29988397383755102353508453)
        ·
          refine ⟨5622824509454081691282835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29988397383755102353508453 5622824509454081691282835)
          ·
            refine ⟨8434236764181122536924253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5622824509454081691282835 8434236764181122536924253)
            ·
              refine ⟨3162838786567920951346595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8434236764181122536924253 3162838786567920951346595)
              ·
                refine ⟨4744258179851881427019893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3162838786567920951346595 4744258179851881427019893)
                ·
                  refine ⟨444774204361113883783115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4744258179851881427019893 444774204361113883783115)
                  ·
                    rfl

theorem cell20_974469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_974469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974469 prefixEnd_974469 := by exact prefixLift 974469
  have htrace : WordTrace (prefixWord ++ tailWord_974469) baseStart_974469 baseEnd_974469 := by
    simpa [prefixWord, tailWord_974469, baseEnd_974469] using wordTrace_append hprefix tailTrace_974469
  have hstable : (prefixWord ++ tailWord_974469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974469).length < 2 ^ (prefixWord ++ tailWord_974469).sum := by decide
  have hdescent : baseEnd_974469 < baseStart_974469 := by decide
  rcases family_descends (prefixWord ++ tailWord_974469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974482 : List Nat := [3, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_974482 : Nat := 118140960795 + 974482 * 2 ^ 59
def prefixEnd_974482 : Nat := 4983230072969 + 3 ^ 40 * 974482 * 2
def baseEnd_974482 : Nat := 444780137915343616349729

theorem tailTrace_974482 : CollatzResearch.WordTrace tailWord_974482 prefixEnd_974482 444780137915343616349729 := by
  unfold tailWord_974482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8885569613906404280169425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23694852303750411413785133 8885569613906404280169425)
  ·
    refine ⟨6664177210429803210127069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8885569613906404280169425 6664177210429803210127069)
    ·
      refine ⟨2499066453911176203797651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6664177210429803210127069 2499066453911176203797651)
      ·
        refine ⟨3748599680866764305696477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499066453911176203797651 3748599680866764305696477)
        ·
          refine ⟨1405724880325036614636179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3748599680866764305696477 1405724880325036614636179)
          ·
            refine ⟨2108587320487554921954269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405724880325036614636179 2108587320487554921954269)
            ·
              refine ⟨790720245182833095732851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2108587320487554921954269 790720245182833095732851)
              ·
                refine ⟨1186080367774249643599277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790720245182833095732851 1186080367774249643599277)
                ·
                  refine ⟨444780137915343616349729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186080367774249643599277 444780137915343616349729)
                  ·
                    rfl

theorem cell20_974482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_974482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974482 prefixEnd_974482 := by exact prefixLift 974482
  have htrace : WordTrace (prefixWord ++ tailWord_974482) baseStart_974482 baseEnd_974482 := by
    simpa [prefixWord, tailWord_974482, baseEnd_974482] using wordTrace_append hprefix tailTrace_974482
  have hstable : (prefixWord ++ tailWord_974482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974482).length < 2 ^ (prefixWord ++ tailWord_974482).sum := by decide
  have hdescent : baseEnd_974482 < baseStart_974482 := by decide
  rcases family_descends (prefixWord ++ tailWord_974482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974500 : List Nat := [2, 3, 1, 2, 2, 3, 1, 6]
def baseStart_974500 : Nat := 118140960795 + 974500 * 2 ^ 59
def prefixEnd_974500 : Nat := 4983230072969 + 3 ^ 40 * 974500 * 2
def baseEnd_974500 : Nat := 148262784535271851249885

theorem tailTrace_974500 : CollatzResearch.WordTrace tailWord_974500 prefixEnd_974500 148262784535271851249885 := by
  unfold tailWord_974500
  simp only [CollatzResearch.WordTrace]
  refine ⟨17771467484780203097416477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23695289979706937463221969 17771467484780203097416477)
  ·
    refine ⟨6664300306792576161531179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17771467484780203097416477 6664300306792576161531179)
    ·
      refine ⟨9996450460188864242296769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6664300306792576161531179 9996450460188864242296769)
      ·
        refine ⟨7497337845141648181722577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9996450460188864242296769 7497337845141648181722577)
        ·
          refine ⟨5623003383856236136291933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7497337845141648181722577 5623003383856236136291933)
          ·
            refine ⟨2108626268946088551109475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5623003383856236136291933 2108626268946088551109475)
            ·
              refine ⟨3162939403419132826664213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108626268946088551109475 3162939403419132826664213)
              ·
                refine ⟨148262784535271851249885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3162939403419132826664213 148262784535271851249885)
                ·
                  rfl

theorem cell20_974500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_974500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974500 prefixEnd_974500 := by exact prefixLift 974500
  have htrace : WordTrace (prefixWord ++ tailWord_974500) baseStart_974500 baseEnd_974500 := by
    simpa [prefixWord, tailWord_974500, baseEnd_974500] using wordTrace_append hprefix tailTrace_974500
  have hstable : (prefixWord ++ tailWord_974500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974500).length < 2 ^ (prefixWord ++ tailWord_974500).sum := by decide
  have hdescent : baseEnd_974500 < baseStart_974500 := by decide
  rcases family_descends (prefixWord ++ tailWord_974500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974514 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_974514 : Nat := 118140960795 + 974514 * 2 ^ 59
def prefixEnd_974514 : Nat := 4983230072969 + 3 ^ 40 * 974514 * 2
def baseEnd_974514 : Nat := 444794743587293727282931

theorem tailTrace_974514 : CollatzResearch.WordTrace tailWord_974514 prefixEnd_974514 444794743587293727282931 := by
  unfold tailWord_974514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8885861397877421646460649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23695630394339791057228397 8885861397877421646460649)
  ·
    refine ⟨6664396048408066234845487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8885861397877421646460649 6664396048408066234845487)
    ·
      refine ⟨9996594072612099352268231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6664396048408066234845487 9996594072612099352268231)
      ·
        refine ⟨14994891108918149028402347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9996594072612099352268231 14994891108918149028402347)
        ·
          refine ⟨22492336663377223542603521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14994891108918149028402347 22492336663377223542603521)
          ·
            refine ⟨16869252497532917656952641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22492336663377223542603521 16869252497532917656952641)
            ·
              refine ⟨12651939373149688242714481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16869252497532917656952641 12651939373149688242714481)
              ·
                refine ⟨9488954529862266182035861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12651939373149688242714481 9488954529862266182035861)
                ·
                  refine ⟨444794743587293727282931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9488954529862266182035861 444794743587293727282931)
                  ·
                    rfl

theorem cell20_974514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_974514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974514 prefixEnd_974514 := by exact prefixLift 974514
  have htrace : WordTrace (prefixWord ++ tailWord_974514) baseStart_974514 baseEnd_974514 := by
    simpa [prefixWord, tailWord_974514, baseEnd_974514] using wordTrace_append hprefix tailTrace_974514
  have hstable : (prefixWord ++ tailWord_974514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974514).length < 2 ^ (prefixWord ++ tailWord_974514).sum := by decide
  have hdescent : baseEnd_974514 < baseStart_974514 := by decide
  rcases family_descends (prefixWord ++ tailWord_974514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974517 : List Nat := [1, 3, 3, 3, 2, 2, 6]
def baseStart_974517 : Nat := 118140960795 + 974517 * 2 ^ 59
def prefixEnd_974517 : Nat := 4983230072969 + 3 ^ 40 * 974517 * 2
def baseEnd_974517 : Nat := 49421790318782116686991

theorem tailTrace_974517 : CollatzResearch.WordTrace tailWord_974517 prefixEnd_974517 49421790318782116686991 := by
  unfold tailWord_974517
  simp only [CollatzResearch.WordTrace]
  refine ⟨35543555010498818098201805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23695703340332545398801203 35543555010498818098201805)
  ·
    refine ⟨13328833128937056786825677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35543555010498818098201805 13328833128937056786825677)
    ·
      refine ⟨4998312423351396295059629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13328833128937056786825677 4998312423351396295059629)
      ·
        refine ⟨1874367158756773610647361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4998312423351396295059629 1874367158756773610647361)
        ·
          refine ⟨1405775369067580207985521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1874367158756773610647361 1405775369067580207985521)
          ·
            refine ⟨1054331526800685155989141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1405775369067580207985521 1054331526800685155989141)
            ·
              refine ⟨49421790318782116686991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1054331526800685155989141 49421790318782116686991)
              ·
                rfl

theorem cell20_974517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 6].length) (baseStart_974517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974517 prefixEnd_974517 := by exact prefixLift 974517
  have htrace : WordTrace (prefixWord ++ tailWord_974517) baseStart_974517 baseEnd_974517 := by
    simpa [prefixWord, tailWord_974517, baseEnd_974517] using wordTrace_append hprefix tailTrace_974517
  have hstable : (prefixWord ++ tailWord_974517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974517).length < 2 ^ (prefixWord ++ tailWord_974517).sum := by decide
  have hdescent : baseEnd_974517 < baseStart_974517 := by decide
  rcases family_descends (prefixWord ++ tailWord_974517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974521 : List Nat := [1, 2, 1, 4, 1, 1, 10]
def baseStart_974521 : Nat := 118140960795 + 974521 * 2 ^ 59
def prefixEnd_974521 : Nat := 4983230072969 + 3 ^ 40 * 974521 * 2
def baseEnd_974521 : Nat := 49421993175336979338841

theorem tailTrace_974521 : CollatzResearch.WordTrace tailWord_974521 prefixEnd_974521 49421993175336979338841 := by
  unfold tailWord_974521
  simp only [CollatzResearch.WordTrace]
  refine ⟨35543700902484326781347417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23695800601656217854231611 35543700902484326781347417)
  ·
    refine ⟨26657775676863245086010563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35543700902484326781347417 26657775676863245086010563)
    ·
      refine ⟨39986663515294867629015845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26657775676863245086010563 39986663515294867629015845)
      ·
        refine ⟨7497499409117787680440471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39986663515294867629015845 7497499409117787680440471)
        ·
          refine ⟨11246249113676681520660707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7497499409117787680440471 11246249113676681520660707)
          ·
            refine ⟨16869373670515022280991061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11246249113676681520660707 16869373670515022280991061)
            ·
              refine ⟨49421993175336979338841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16869373670515022280991061 49421993175336979338841)
              ·
                rfl

theorem cell20_974521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 10].length) (baseStart_974521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974521 prefixEnd_974521 := by exact prefixLift 974521
  have htrace : WordTrace (prefixWord ++ tailWord_974521) baseStart_974521 baseEnd_974521 := by
    simpa [prefixWord, tailWord_974521, baseEnd_974521] using wordTrace_append hprefix tailTrace_974521
  have hstable : (prefixWord ++ tailWord_974521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974521).length < 2 ^ (prefixWord ++ tailWord_974521).sum := by decide
  have hdescent : baseEnd_974521 < baseStart_974521 := by decide
  rcases family_descends (prefixWord ++ tailWord_974521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974534 : List Nat := [6, 1, 2, 1, 1, 1, 1, 7]
def baseStart_974534 : Nat := 118140960795 + 974534 * 2 ^ 59
def prefixEnd_974534 : Nat := 4983230072969 + 3 ^ 40 * 974534 * 2
def baseEnd_974534 : Nat := 148267957377420848872061

theorem tailTrace_974534 : CollatzResearch.WordTrace tailWord_974534 prefixEnd_974534 148267957377420848872061 := by
  unfold tailWord_974534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110755470357413437549083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23696116700958153334380437 1110755470357413437549083)
  ·
    refine ⟨1666133205536120156323625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1110755470357413437549083 1666133205536120156323625)
    ·
      refine ⟨1249599904152090117242719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1666133205536120156323625 1249599904152090117242719)
      ·
        refine ⟨1874399856228135175864079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249599904152090117242719 1874399856228135175864079)
        ·
          refine ⟨2811599784342202763796119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874399856228135175864079 2811599784342202763796119)
          ·
            refine ⟨4217399676513304145694179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2811599784342202763796119 4217399676513304145694179)
            ·
              refine ⟨6326099514769956218541269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4217399676513304145694179 6326099514769956218541269)
              ·
                refine ⟨148267957377420848872061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6326099514769956218541269 148267957377420848872061)
                ·
                  rfl

theorem cell20_974534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_974534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974534 prefixEnd_974534 := by exact prefixLift 974534
  have htrace : WordTrace (prefixWord ++ tailWord_974534) baseStart_974534 baseEnd_974534 := by
    simpa [prefixWord, tailWord_974534, baseEnd_974534] using wordTrace_append hprefix tailTrace_974534
  have hstable : (prefixWord ++ tailWord_974534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974534).length < 2 ^ (prefixWord ++ tailWord_974534).sum := by decide
  have hdescent : baseEnd_974534 < baseStart_974534 := by decide
  rcases family_descends (prefixWord ++ tailWord_974534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974552 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_974552 : Nat := 118140960795 + 974552 * 2 ^ 59
def prefixEnd_974552 : Nat := 4983230072969 + 3 ^ 40 * 974552 * 2
def baseEnd_974552 : Nat := 444812087822734484016109

theorem tailTrace_974552 : CollatzResearch.WordTrace tailWord_974552 prefixEnd_974552 444812087822734484016109 := by
  unfold tailWord_974552
  simp only [CollatzResearch.WordTrace]
  refine ⟨17772415782686009537862955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23696554376914679383817273 17772415782686009537862955)
  ·
    refine ⟨26658623674029014306794433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17772415782686009537862955 26658623674029014306794433)
    ·
      refine ⟨19993967755521760730095825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26658623674029014306794433 19993967755521760730095825)
      ·
        refine ⟨14995475816641320547571869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19993967755521760730095825 14995475816641320547571869)
        ·
          refine ⟨5623303431240495205339451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14995475816641320547571869 5623303431240495205339451)
          ·
            refine ⟨8434955146860742808009177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623303431240495205339451 8434955146860742808009177)
            ·
              refine ⟨6326216360145557106006883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8434955146860742808009177 6326216360145557106006883)
              ·
                refine ⟨9489324540218335659010325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6326216360145557106006883 9489324540218335659010325)
                ·
                  refine ⟨444812087822734484016109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9489324540218335659010325 444812087822734484016109)
                  ·
                    rfl

theorem cell20_974552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_974552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974552 prefixEnd_974552 := by exact prefixLift 974552
  have htrace : WordTrace (prefixWord ++ tailWord_974552) baseStart_974552 baseEnd_974552 := by
    simpa [prefixWord, tailWord_974552, baseEnd_974552] using wordTrace_append hprefix tailTrace_974552
  have hstable : (prefixWord ++ tailWord_974552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974552).length < 2 ^ (prefixWord ++ tailWord_974552).sum := by decide
  have hdescent : baseEnd_974552 < baseStart_974552 := by decide
  rcases family_descends (prefixWord ++ tailWord_974552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974559 : List Nat := [1, 1, 2, 3, 2, 2, 1, 8]
def baseStart_974559 : Nat := 118140960795 + 974559 * 2 ^ 59
def prefixEnd_974559 : Nat := 4983230072969 + 3 ^ 40 * 974559 * 2
def baseEnd_974559 : Nat := 148271760937824523594249

theorem tailTrace_974559 : CollatzResearch.WordTrace tailWord_974559 prefixEnd_974559 148271760937824523594249 := by
  unfold tailWord_974559
  simp only [CollatzResearch.WordTrace]
  refine ⟨35545086876346659271230731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23696724584231106180820487 35545086876346659271230731)
  ·
    refine ⟨53317630314519988906846097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35545086876346659271230731 53317630314519988906846097)
    ·
      refine ⟨39988222735889991680134573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53317630314519988906846097 39988222735889991680134573)
      ·
        refine ⟨14995583525958746880050465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39988222735889991680134573 14995583525958746880050465)
        ·
          refine ⟨11246687644469060160037849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14995583525958746880050465 11246687644469060160037849)
          ·
            refine ⟨8435015733351795120028387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11246687644469060160037849 8435015733351795120028387)
            ·
              refine ⟨12652523600027692680042581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8435015733351795120028387 12652523600027692680042581)
              ·
                refine ⟨148271760937824523594249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12652523600027692680042581 148271760937824523594249)
                ·
                  rfl

theorem cell20_974559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_974559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974559 prefixEnd_974559 := by exact prefixLift 974559
  have htrace : WordTrace (prefixWord ++ tailWord_974559) baseStart_974559 baseEnd_974559 := by
    simpa [prefixWord, tailWord_974559, baseEnd_974559] using wordTrace_append hprefix tailTrace_974559
  have hstable : (prefixWord ++ tailWord_974559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974559).length < 2 ^ (prefixWord ++ tailWord_974559).sum := by decide
  have hdescent : baseEnd_974559 < baseStart_974559 := by decide
  rcases family_descends (prefixWord ++ tailWord_974559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974569 : List Nat := [1, 2, 1, 1, 1, 2, 3, 7, 2]
def baseStart_974569 : Nat := 118140960795 + 974569 * 2 ^ 59
def prefixEnd_974569 : Nat := 4983230072969 + 3 ^ 40 * 974569 * 2
def baseEnd_974569 : Nat := 444819847085957980449373

theorem tailTrace_974569 : CollatzResearch.WordTrace tailWord_974569 prefixEnd_974569 444819847085957980449373 := by
  unfold tailWord_974569
  simp only [CollatzResearch.WordTrace]
  refine ⟨35545451606310430979094761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23696967737540287319396507 35545451606310430979094761)
  ·
    refine ⟨26659088704732823234321071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35545451606310430979094761 26659088704732823234321071)
    ·
      refine ⟨39988633057099234851481607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26659088704732823234321071 39988633057099234851481607)
      ·
        refine ⟨59982949585648852277222411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39988633057099234851481607 59982949585648852277222411)
        ·
          refine ⟨89974424378473278415833617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59982949585648852277222411 89974424378473278415833617)
          ·
            refine ⟨67480818283854958811875213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89974424378473278415833617 67480818283854958811875213)
            ·
              refine ⟨25305306856445609554453205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67480818283854958811875213 25305306856445609554453205)
              ·
                refine ⟨593093129447943973932497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25305306856445609554453205 593093129447943973932497)
                ·
                  refine ⟨444819847085957980449373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593093129447943973932497 444819847085957980449373)
                  ·
                    rfl

theorem cell20_974569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 2].length) (baseStart_974569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974569 prefixEnd_974569 := by exact prefixLift 974569
  have htrace : WordTrace (prefixWord ++ tailWord_974569) baseStart_974569 baseEnd_974569 := by
    simpa [prefixWord, tailWord_974569, baseEnd_974569] using wordTrace_append hprefix tailTrace_974569
  have hstable : (prefixWord ++ tailWord_974569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974569).length < 2 ^ (prefixWord ++ tailWord_974569).sum := by decide
  have hdescent : baseEnd_974569 < baseStart_974569 := by decide
  rcases family_descends (prefixWord ++ tailWord_974569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974582 : List Nat := [5, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_974582 : Nat := 118140960795 + 974582 * 2 ^ 59
def prefixEnd_974582 : Nat := 4983230072969 + 3 ^ 40 * 974582 * 2
def baseEnd_974582 : Nat := 444825780640187713015987

theorem tailTrace_974582 : CollatzResearch.WordTrace tailWord_974582 prefixEnd_974582 444825780640187713015987 := by
  unfold tailWord_974582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221620359703958387457375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23697283836842222799545333 2221620359703958387457375)
  ·
    refine ⟨3332430539555937581186063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2221620359703958387457375 3332430539555937581186063)
    ·
      refine ⟨4998645809333906371779095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3332430539555937581186063 4998645809333906371779095)
      ·
        refine ⟨7497968714000859557668643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4998645809333906371779095 7497968714000859557668643)
        ·
          refine ⟨11246953071001289336502965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7497968714000859557668643 11246953071001289336502965)
          ·
            refine ⟨1054401850406370875297153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11246953071001289336502965 1054401850406370875297153)
            ·
              refine ⟨790801387804778156472865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054401850406370875297153 790801387804778156472865)
              ·
                refine ⟨593101040853583617354649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790801387804778156472865 593101040853583617354649)
                ·
                  refine ⟨444825780640187713015987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593101040853583617354649 444825780640187713015987)
                  ·
                    rfl

theorem cell20_974582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_974582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974582 prefixEnd_974582 := by exact prefixLift 974582
  have htrace : WordTrace (prefixWord ++ tailWord_974582) baseStart_974582 baseEnd_974582 := by
    simpa [prefixWord, tailWord_974582, baseEnd_974582] using wordTrace_append hprefix tailTrace_974582
  have hstable : (prefixWord ++ tailWord_974582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974582).length < 2 ^ (prefixWord ++ tailWord_974582).sum := by decide
  have hdescent : baseEnd_974582 < baseStart_974582 := by decide
  rcases family_descends (prefixWord ++ tailWord_974582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974583 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 3]
def baseStart_974583 : Nat := 118140960795 + 974583 * 2 ^ 59
def prefixEnd_974583 : Nat := 4983230072969 + 3 ^ 40 * 974583 * 2
def baseEnd_974583 : Nat := 444826237067436153982649

theorem tailTrace_974583 : CollatzResearch.WordTrace tailWord_974583 prefixEnd_974583 444826237067436153982649 := by
  unfold tailWord_974583
  simp only [CollatzResearch.WordTrace]
  refine ⟨35545962228259711370104403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23697308152173140913402935 35545962228259711370104403)
  ·
    refine ⟨53318943342389567055156605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35545962228259711370104403 53318943342389567055156605)
    ·
      refine ⟨19994603753396087645683727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53318943342389567055156605 19994603753396087645683727)
      ·
        refine ⟨29991905630094131468525591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19994603753396087645683727 29991905630094131468525591)
        ·
          refine ⟨44987858445141197202788387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29991905630094131468525591 44987858445141197202788387)
          ·
            refine ⟨67481787667711795804182581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44987858445141197202788387 67481787667711795804182581)
            ·
              refine ⟨6326417593847980856642117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67481787667711795804182581 6326417593847980856642117)
              ·
                refine ⟨1186203298846496410620397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6326417593847980856642117 1186203298846496410620397)
                ·
                  refine ⟨444826237067436153982649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186203298846496410620397 444826237067436153982649)
                  ·
                    rfl

theorem cell20_974583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 3].length) (baseStart_974583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974583 prefixEnd_974583 := by exact prefixLift 974583
  have htrace : WordTrace (prefixWord ++ tailWord_974583) baseStart_974583 baseEnd_974583 := by
    simpa [prefixWord, tailWord_974583, baseEnd_974583] using wordTrace_append hprefix tailTrace_974583
  have hstable : (prefixWord ++ tailWord_974583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974583).length < 2 ^ (prefixWord ++ tailWord_974583).sum := by decide
  have hdescent : baseEnd_974583 < baseStart_974583 := by decide
  rcases family_descends (prefixWord ++ tailWord_974583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974610 : List Nat := [3, 2, 4, 1, 1, 2, 3, 4]
def baseStart_974610 : Nat := 118140960795 + 974610 * 2 ^ 59
def prefixEnd_974610 : Nat := 4983230072969 + 3 ^ 40 * 974610 * 2
def baseEnd_974610 : Nat := 148279520201048020027513

theorem tailTrace_974610 : CollatzResearch.WordTrace tailWord_974610 prefixEnd_974610 148279520201048020027513 := by
  unfold tailWord_974610
  simp only [CollatzResearch.WordTrace]
  refine ⟨8886736749790473745334321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23697964666107929987558189 8886736749790473745334321)
  ·
    refine ⟨6665052562342855309000741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8886736749790473745334321 6665052562342855309000741)
    ·
      refine ⟨1249697355439285370437639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6665052562342855309000741 1249697355439285370437639)
      ·
        refine ⟨1874546033158928055656459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249697355439285370437639 1874546033158928055656459)
        ·
          refine ⟨2811819049738392083484689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874546033158928055656459 2811819049738392083484689)
          ·
            refine ⟨2108864287303794062613517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2811819049738392083484689 2108864287303794062613517)
            ·
              refine ⟨790824107738922773480069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2108864287303794062613517 790824107738922773480069)
              ·
                refine ⟨148279520201048020027513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 790824107738922773480069 148279520201048020027513)
                ·
                  rfl

theorem cell20_974610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_974610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974610 prefixEnd_974610 := by exact prefixLift 974610
  have htrace : WordTrace (prefixWord ++ tailWord_974610) baseStart_974610 baseEnd_974610 := by
    simpa [prefixWord, tailWord_974610, baseEnd_974610] using wordTrace_append hprefix tailTrace_974610
  have hstable : (prefixWord ++ tailWord_974610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974610).length < 2 ^ (prefixWord ++ tailWord_974610).sum := by decide
  have hdescent : baseEnd_974610 < baseStart_974610 := by decide
  rcases family_descends (prefixWord ++ tailWord_974610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974624 : List Nat := [2, 1, 1, 5, 1, 1, 4, 3, 2]
def baseStart_974624 : Nat := 118140960795 + 974624 * 2 ^ 59
def prefixEnd_974624 : Nat := 4983230072969 + 3 ^ 40 * 974624 * 2
def baseEnd_974624 : Nat := 444844950584622233615815

theorem tailTrace_974624 : CollatzResearch.WordTrace tailWord_974624 prefixEnd_974624 444844950584622233615815 := by
  unfold tailWord_974624
  simp only [CollatzResearch.WordTrace]
  refine ⟨17773728810555587686173463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23698305080740783581564617 17773728810555587686173463)
  ·
    refine ⟨26660593215833381529260195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17773728810555587686173463 26660593215833381529260195)
    ·
      refine ⟨39990889823750072293890293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26660593215833381529260195 39990889823750072293890293)
      ·
        refine ⟨3749145920976569277552215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39990889823750072293890293 3749145920976569277552215)
        ·
          refine ⟨5623718881464853916328323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3749145920976569277552215 5623718881464853916328323)
          ·
            refine ⟨8435578322197280874492485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5623718881464853916328323 8435578322197280874492485)
            ·
              refine ⟨1581670935411990163967341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8435578322197280874492485 1581670935411990163967341)
              ·
                refine ⟨593126600779496311487753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1581670935411990163967341 593126600779496311487753)
                ·
                  refine ⟨444844950584622233615815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593126600779496311487753 444844950584622233615815)
                  ·
                    rfl

theorem cell20_974624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 2].length) (baseStart_974624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974624 prefixEnd_974624 := by exact prefixLift 974624
  have htrace : WordTrace (prefixWord ++ tailWord_974624) baseStart_974624 baseEnd_974624 := by
    simpa [prefixWord, tailWord_974624, baseEnd_974624] using wordTrace_append hprefix tailTrace_974624
  have hstable : (prefixWord ++ tailWord_974624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974624).length < 2 ^ (prefixWord ++ tailWord_974624).sum := by decide
  have hdescent : baseEnd_974624 < baseStart_974624 := by decide
  rcases family_descends (prefixWord ++ tailWord_974624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974655 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 3]
def baseStart_974655 : Nat := 118140960795 + 974655 * 2 ^ 59
def prefixEnd_974655 : Nat := 4983230072969 + 3 ^ 40 * 974655 * 2
def baseEnd_974655 : Nat := 444859099829323903582355

theorem tailTrace_974655 : CollatzResearch.WordTrace tailWord_974655 prefixEnd_974655 444859099829323903582355 := by
  unfold tailWord_974655
  simp only [CollatzResearch.WordTrace]
  refine ⟨35548588283998867666725419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23699058855999245111150279 35548588283998867666725419)
  ·
    refine ⟨53322882425998301500088129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35548588283998867666725419 53322882425998301500088129)
    ·
      refine ⟨39992161819498726125066097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53322882425998301500088129 39992161819498726125066097)
      ·
        refine ⟨29994121364624044593799573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39992161819498726125066097 29994121364624044593799573)
        ·
          refine ⟨1405974438966752090334355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29994121364624044593799573 1405974438966752090334355)
          ·
            refine ⟨2108961658450128135501533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405974438966752090334355 2108961658450128135501533)
            ·
              refine ⟨790860621918798050813075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2108961658450128135501533 790860621918798050813075)
              ·
                refine ⟨1186290932878197076219613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790860621918798050813075 1186290932878197076219613)
                ·
                  refine ⟨444859099829323903582355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186290932878197076219613 444859099829323903582355)
                  ·
                    rfl

theorem cell20_974655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 3].length) (baseStart_974655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974655 prefixEnd_974655 := by exact prefixLift 974655
  have htrace : WordTrace (prefixWord ++ tailWord_974655) baseStart_974655 baseEnd_974655 := by
    simpa [prefixWord, tailWord_974655, baseEnd_974655] using wordTrace_append hprefix tailTrace_974655
  have hstable : (prefixWord ++ tailWord_974655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974655).length < 2 ^ (prefixWord ++ tailWord_974655).sum := by decide
  have hdescent : baseEnd_974655 < baseStart_974655 := by decide
  rcases family_descends (prefixWord ++ tailWord_974655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974666 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_974666 : Nat := 118140960795 + 974666 * 2 ^ 59
def prefixEnd_974666 : Nat := 4983230072969 + 3 ^ 40 * 974666 * 2
def baseEnd_974666 : Nat := 444864120529056754215643

theorem tailTrace_974666 : CollatzResearch.WordTrace tailWord_974666 prefixEnd_974666 444864120529056754215643 := by
  unfold tailWord_974666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887247371739754136343963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23699326324639344363583901 8887247371739754136343963)
  ·
    refine ⟨13330871057609631204515945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8887247371739754136343963 13330871057609631204515945)
    ·
      refine ⟨9998153293207223403386959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13330871057609631204515945 9998153293207223403386959)
      ·
        refine ⟨14997229939810835105080439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9998153293207223403386959 14997229939810835105080439)
        ·
          refine ⟨22495844909716252657620659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14997229939810835105080439 22495844909716252657620659)
          ·
            refine ⟨33743767364574378986430989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22495844909716252657620659 33743767364574378986430989)
            ·
              refine ⟨12653912761715392119911621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33743767364574378986430989 12653912761715392119911621)
              ·
                refine ⟨2372608642821636022483429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12653912761715392119911621 2372608642821636022483429)
                ·
                  refine ⟨444864120529056754215643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2372608642821636022483429 444864120529056754215643)
                  ·
                    rfl

theorem cell20_974666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_974666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974666 prefixEnd_974666 := by exact prefixLift 974666
  have htrace : WordTrace (prefixWord ++ tailWord_974666) baseStart_974666 baseEnd_974666 := by
    simpa [prefixWord, tailWord_974666, baseEnd_974666] using wordTrace_append hprefix tailTrace_974666
  have hstable : (prefixWord ++ tailWord_974666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974666).length < 2 ^ (prefixWord ++ tailWord_974666).sum := by decide
  have hdescent : baseEnd_974666 < baseStart_974666 := by decide
  rcases family_descends (prefixWord ++ tailWord_974666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974669 : List Nat := [1, 6, 1, 2, 1, 2, 1, 6]
def baseStart_974669 : Nat := 118140960795 + 974669 * 2 ^ 59
def prefixEnd_974669 : Nat := 4983230072969 + 3 ^ 40 * 974669 * 2
def baseEnd_974669 : Nat := 148288496603600692371877

theorem tailTrace_974669 : CollatzResearch.WordTrace tailWord_974669 prefixEnd_974669 148288496603600692371877 := by
  unfold tailWord_974669
  simp only [CollatzResearch.WordTrace]
  refine ⟨35549098905948148057735061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23699399270632098705156707 35549098905948148057735061)
  ·
    refine ⟨1666364011216319440206331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35549098905948148057735061 1666364011216319440206331)
    ·
      refine ⟨2499546016824479160309497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1666364011216319440206331 2499546016824479160309497)
      ·
        refine ⟨1874659512618359370232123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2499546016824479160309497 1874659512618359370232123)
        ·
          refine ⟨2811989268927539055348185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874659512618359370232123 2811989268927539055348185)
          ·
            refine ⟨2108991951695654291511139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2811989268927539055348185 2108991951695654291511139)
            ·
              refine ⟨3163487927543481437266709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2108991951695654291511139 3163487927543481437266709)
              ·
                refine ⟨148288496603600692371877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3163487927543481437266709 148288496603600692371877)
                ·
                  rfl

theorem cell20_974669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_974669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974669 prefixEnd_974669 := by exact prefixLift 974669
  have htrace : WordTrace (prefixWord ++ tailWord_974669) baseStart_974669 baseEnd_974669 := by
    simpa [prefixWord, tailWord_974669, baseEnd_974669] using wordTrace_append hprefix tailTrace_974669
  have hstable : (prefixWord ++ tailWord_974669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974669).length < 2 ^ (prefixWord ++ tailWord_974669).sum := by decide
  have hdescent : baseEnd_974669 < baseStart_974669 := by decide
  rcases family_descends (prefixWord ++ tailWord_974669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974679 : List Nat := [1, 1, 3, 2, 5, 2, 1, 3, 2]
def baseStart_974679 : Nat := 118140960795 + 974679 * 2 ^ 59
def prefixEnd_974679 : Nat := 4983230072969 + 3 ^ 40 * 974679 * 2
def baseEnd_974679 : Nat := 444870054083286486782257

theorem tailTrace_974679 : CollatzResearch.WordTrace tailWord_974679 prefixEnd_974679 444870054083286486782257 := by
  unfold tailWord_974679
  simp only [CollatzResearch.WordTrace]
  refine ⟨35549463635911919765599091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23699642423941279843732727 35549463635911919765599091)
  ·
    refine ⟨53324195453867879648398637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35549463635911919765599091 53324195453867879648398637)
    ·
      refine ⟨19996573295200454868149489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53324195453867879648398637 19996573295200454868149489)
      ·
        refine ⟨14997429971400341151112117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19996573295200454868149489 14997429971400341151112117)
        ·
          refine ⟨1406009059818781982916761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14997429971400341151112117 1406009059818781982916761)
          ·
            refine ⟨1054506794864086487187571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406009059818781982916761 1054506794864086487187571)
            ·
              refine ⟨1581760192296129730781357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054506794864086487187571 1581760192296129730781357)
              ·
                refine ⟨593160072111048649043009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1581760192296129730781357 593160072111048649043009)
                ·
                  refine ⟨444870054083286486782257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593160072111048649043009 444870054083286486782257)
                  ·
                    rfl

theorem cell20_974679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3, 2].length) (baseStart_974679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974679 prefixEnd_974679 := by exact prefixLift 974679
  have htrace : WordTrace (prefixWord ++ tailWord_974679) baseStart_974679 baseEnd_974679 := by
    simpa [prefixWord, tailWord_974679, baseEnd_974679] using wordTrace_append hprefix tailTrace_974679
  have hstable : (prefixWord ++ tailWord_974679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974679).length < 2 ^ (prefixWord ++ tailWord_974679).sum := by decide
  have hdescent : baseEnd_974679 < baseStart_974679 := by decide
  rcases family_descends (prefixWord ++ tailWord_974679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974690 : List Nat := [3, 3, 2, 1, 2, 1, 8]
def baseStart_974690 : Nat := 118140960795 + 974690 * 2 ^ 59
def prefixEnd_974690 : Nat := 4983230072969 + 3 ^ 40 * 974690 * 2
def baseEnd_974690 : Nat := 49430563864779926379505

theorem tailTrace_974690 : CollatzResearch.WordTrace tailWord_974690 prefixEnd_974690 49430563864779926379505 := by
  unfold tailWord_974690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887466209718017161062381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23699909892581379096166349 8887466209718017161062381)
  ·
    refine ⟨3332799828644256435398393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8887466209718017161062381 3332799828644256435398393)
    ·
      refine ⟨2499599871483192326548795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3332799828644256435398393 2499599871483192326548795)
      ·
        refine ⟨3749399807224788489823193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499599871483192326548795 3749399807224788489823193)
        ·
          refine ⟨2812049855418591367367395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3749399807224788489823193 2812049855418591367367395)
          ·
            refine ⟨4218074783127887051051093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812049855418591367367395 4218074783127887051051093)
            ·
              refine ⟨49430563864779926379505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4218074783127887051051093 49430563864779926379505)
              ·
                rfl

theorem cell20_974690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 8].length) (baseStart_974690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974690 prefixEnd_974690 := by exact prefixLift 974690
  have htrace : WordTrace (prefixWord ++ tailWord_974690) baseStart_974690 baseEnd_974690 := by
    simpa [prefixWord, tailWord_974690, baseEnd_974690] using wordTrace_append hprefix tailTrace_974690
  have hstable : (prefixWord ++ tailWord_974690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974690).length < 2 ^ (prefixWord ++ tailWord_974690).sum := by decide
  have hdescent : baseEnd_974690 < baseStart_974690 := by decide
  rcases family_descends (prefixWord ++ tailWord_974690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974714 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_974714 : Nat := 118140960795 + 974714 * 2 ^ 59
def prefixEnd_974714 : Nat := 4983230072969 + 3 ^ 40 * 974714 * 2
def baseEnd_974714 : Nat := 444886029036981920615447

theorem tailTrace_974714 : CollatzResearch.WordTrace tailWord_974714 prefixEnd_974714 444886029036981920615447 := by
  unfold tailWord_974714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8887685047696280185780799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23700493460523413828748797 8887685047696280185780799)
  ·
    refine ⟨13331527571544420278671199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8887685047696280185780799 13331527571544420278671199)
    ·
      refine ⟨19997291357316630418006799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13331527571544420278671199 19997291357316630418006799)
      ·
        refine ⟨29995937035974945627010199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19997291357316630418006799 29995937035974945627010199)
        ·
          refine ⟨44993905553962418440515299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29995937035974945627010199 44993905553962418440515299)
          ·
            refine ⟨67490858330943627660772949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44993905553962418440515299 67490858330943627660772949)
            ·
              refine ⟨790908496065745636649683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 67490858330943627660772949 790908496065745636649683)
              ·
                refine ⟨1186362744098618454974525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790908496065745636649683 1186362744098618454974525)
                ·
                  refine ⟨444886029036981920615447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186362744098618454974525 444886029036981920615447)
                  ·
                    rfl

theorem cell20_974714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_974714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974714 prefixEnd_974714 := by exact prefixLift 974714
  have htrace : WordTrace (prefixWord ++ tailWord_974714) baseStart_974714 baseEnd_974714 := by
    simpa [prefixWord, tailWord_974714, baseEnd_974714] using wordTrace_append hprefix tailTrace_974714
  have hstable : (prefixWord ++ tailWord_974714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974714).length < 2 ^ (prefixWord ++ tailWord_974714).sum := by decide
  have hdescent : baseEnd_974714 < baseStart_974714 := by decide
  rcases family_descends (prefixWord ++ tailWord_974714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974749 : List Nat := [1, 4, 2, 1, 2, 10]
def baseStart_974749 : Nat := 118140960795 + 974749 * 2 ^ 59
def prefixEnd_974749 : Nat := 4983230072969 + 3 ^ 40 * 974749 * 2
def baseEnd_974749 : Nat := 16477851999654716831431

theorem tailTrace_974749 : CollatzResearch.WordTrace tailWord_974749 prefixEnd_974749 16477851999654716831431 := by
  unfold tailWord_974749
  simp only [CollatzResearch.WordTrace]
  refine ⟨35552016745658321720647301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23701344497105547813764867 35552016745658321720647301)
  ·
    refine ⟨6666003139810935322621369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35552016745658321720647301 6666003139810935322621369)
    ·
      refine ⟨4999502354858201491966027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6666003139810935322621369 4999502354858201491966027)
      ·
        refine ⟨7499253532287302237949041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4999502354858201491966027 7499253532287302237949041)
        ·
          refine ⟨5624440149215476678461781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7499253532287302237949041 5624440149215476678461781)
          ·
            refine ⟨16477851999654716831431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5624440149215476678461781 16477851999654716831431)
            ·
              rfl

theorem cell20_974749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 10].length) (baseStart_974749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974749 prefixEnd_974749 := by exact prefixLift 974749
  have htrace : WordTrace (prefixWord ++ tailWord_974749) baseStart_974749 baseEnd_974749 := by
    simpa [prefixWord, tailWord_974749, baseEnd_974749] using wordTrace_append hprefix tailTrace_974749
  have hstable : (prefixWord ++ tailWord_974749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974749).length < 2 ^ (prefixWord ++ tailWord_974749).sum := by decide
  have hdescent : baseEnd_974749 < baseStart_974749 := by decide
  rcases family_descends (prefixWord ++ tailWord_974749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974838 : List Nat := [5, 1, 1, 1, 4, 2, 2, 4]
def baseStart_974838 : Nat := 118140960795 + 974838 * 2 ^ 59
def prefixEnd_974838 : Nat := 4983230072969 + 3 ^ 40 * 974838 * 2
def baseEnd_974838 : Nat := 148314208671929533493869

theorem tailTrace_974838 : CollatzResearch.WordTrace tailWord_974838 prefixEnd_974838 148314208671929533493869 := by
  unfold tailWord_974838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222203927645993120039823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23703508561557259947091445 2222203927645993120039823)
  ·
    refine ⟨3333305891468989680059735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2222203927645993120039823 3333305891468989680059735)
    ·
      refine ⟨4999958837203484520089603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3333305891468989680059735 4999958837203484520089603)
      ·
        refine ⟨7499938255805226780134405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4999958837203484520089603 7499938255805226780134405)
        ·
          refine ⟨1406238422963480021275201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7499938255805226780134405 1406238422963480021275201)
          ·
            refine ⟨1054678817222610015956401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406238422963480021275201 1054678817222610015956401)
            ·
              refine ⟨791009112916957511967301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054678817222610015956401 791009112916957511967301)
              ·
                refine ⟨148314208671929533493869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 791009112916957511967301 148314208671929533493869)
                ·
                  rfl

theorem cell20_974838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_974838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974838 prefixEnd_974838 := by exact prefixLift 974838
  have htrace : WordTrace (prefixWord ++ tailWord_974838) baseStart_974838 baseEnd_974838 := by
    simpa [prefixWord, tailWord_974838, baseEnd_974838] using wordTrace_append hprefix tailTrace_974838
  have hstable : (prefixWord ++ tailWord_974838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974838).length < 2 ^ (prefixWord ++ tailWord_974838).sum := by decide
  have hdescent : baseEnd_974838 < baseStart_974838 := by decide
  rcases family_descends (prefixWord ++ tailWord_974838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974869 : List Nat := [1, 3, 2, 1, 5, 1, 3, 2, 2]
def baseStart_974869 : Nat := 118140960795 + 974869 * 2 ^ 59
def prefixEnd_974869 : Nat := 4983230072969 + 3 ^ 40 * 974869 * 2
def baseEnd_974869 : Nat := 444956775260490270448147

theorem tailTrace_974869 : CollatzResearch.WordTrace tailWord_974869 prefixEnd_974869 444956775260490270448147 := by
  unfold tailWord_974869
  simp only [CollatzResearch.WordTrace]
  refine ⟨35556393505223582215015661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23704262336815721476677107 35556393505223582215015661)
  ·
    refine ⟨13333647564458843330630873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35556393505223582215015661 13333647564458843330630873)
    ·
      refine ⟨10000235673344132497973155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13333647564458843330630873 10000235673344132497973155)
      ·
        refine ⟨15000353510016198746959733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10000235673344132497973155 15000353510016198746959733)
        ·
          refine ⟨1406283141564018632527475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15000353510016198746959733 1406283141564018632527475)
          ·
            refine ⟨2109424712346027948791213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406283141564018632527475 2109424712346027948791213)
            ·
              refine ⟨791034267129760480796705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2109424712346027948791213 791034267129760480796705)
              ·
                refine ⟨593275700347320360597529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791034267129760480796705 593275700347320360597529)
                ·
                  refine ⟨444956775260490270448147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593275700347320360597529 444956775260490270448147)
                  ·
                    rfl

theorem cell20_974869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_974869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974869 prefixEnd_974869 := by exact prefixLift 974869
  have htrace : WordTrace (prefixWord ++ tailWord_974869) baseStart_974869 baseEnd_974869 := by
    simpa [prefixWord, tailWord_974869, baseEnd_974869] using wordTrace_append hprefix tailTrace_974869
  have hstable : (prefixWord ++ tailWord_974869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974869).length < 2 ^ (prefixWord ++ tailWord_974869).sum := by decide
  have hdescent : baseEnd_974869 < baseStart_974869 := by decide
  rcases family_descends (prefixWord ++ tailWord_974869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974901 : List Nat := [1, 3, 3, 1, 1, 1, 4, 6]
def baseStart_974901 : Nat := 118140960795 + 974901 * 2 ^ 59
def prefixEnd_974901 : Nat := 4983230072969 + 3 ^ 40 * 974901 * 2
def baseEnd_974901 : Nat := 148323793644146793793783

theorem tailTrace_974901 : CollatzResearch.WordTrace tailWord_974901 prefixEnd_974901 148323793644146793793783 := by
  unfold tailWord_974901
  simp only [CollatzResearch.WordTrace]
  refine ⟨35557560641107651680180557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23705040427405101120120371 35557560641107651680180557)
  ·
    refine ⟨13334085240415369380067709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35557560641107651680180557 13334085240415369380067709)
    ·
      refine ⟨5000281965155763517525391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13334085240415369380067709 5000281965155763517525391)
      ·
        refine ⟨7500422947733645276288087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5000281965155763517525391 7500422947733645276288087)
        ·
          refine ⟨11250634421600467914432131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7500422947733645276288087 11250634421600467914432131)
          ·
            refine ⟨16875951632400701871648197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11250634421600467914432131 16875951632400701871648197)
            ·
              refine ⟨3164240931075131600934037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16875951632400701871648197 3164240931075131600934037)
              ·
                refine ⟨148323793644146793793783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3164240931075131600934037 148323793644146793793783)
                ·
                  rfl

theorem cell20_974901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_974901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974901 prefixEnd_974901 := by exact prefixLift 974901
  have htrace : WordTrace (prefixWord ++ tailWord_974901) baseStart_974901 baseEnd_974901 := by
    simpa [prefixWord, tailWord_974901, baseEnd_974901] using wordTrace_append hprefix tailTrace_974901
  have hstable : (prefixWord ++ tailWord_974901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974901).length < 2 ^ (prefixWord ++ tailWord_974901).sum := by decide
  have hdescent : baseEnd_974901 < baseStart_974901 := by decide
  rcases family_descends (prefixWord ++ tailWord_974901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974915 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_974915 : Nat := 118140960795 + 974915 * 2 ^ 59
def prefixEnd_974915 : Nat := 4983230072969 + 3 ^ 40 * 974915 * 2
def baseEnd_974915 : Nat := 444977770913918554914625

theorem tailTrace_974915 : CollatzResearch.WordTrace tailWord_974915 prefixEnd_974915 444977770913918554914625 := by
  unfold tailWord_974915
  simp only [CollatzResearch.WordTrace]
  refine ⟨35558071263056932071190199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23705380842037954714126799 35558071263056932071190199)
  ·
    refine ⟨53337106894585398106785299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35558071263056932071190199 53337106894585398106785299)
    ·
      refine ⟨80005660341878097160177949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53337106894585398106785299 80005660341878097160177949)
      ·
        refine ⟨30002122628204286435066731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80005660341878097160177949 30002122628204286435066731)
        ·
          refine ⟨45003183942306429652600097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30002122628204286435066731 45003183942306429652600097)
          ·
            refine ⟨33752387956729822239450073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45003183942306429652600097 33752387956729822239450073)
            ·
              refine ⟨25314290967547366679587555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33752387956729822239450073 25314290967547366679587555)
              ·
                refine ⟨37971436451321050019381333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25314290967547366679587555 37971436451321050019381333)
                ·
                  refine ⟨444977770913918554914625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37971436451321050019381333 444977770913918554914625)
                  ·
                    rfl

theorem cell20_974915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_974915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974915 prefixEnd_974915 := by exact prefixLift 974915
  have htrace : WordTrace (prefixWord ++ tailWord_974915) baseStart_974915 baseEnd_974915 := by
    simpa [prefixWord, tailWord_974915, baseEnd_974915] using wordTrace_append hprefix tailTrace_974915
  have hstable : (prefixWord ++ tailWord_974915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974915).length < 2 ^ (prefixWord ++ tailWord_974915).sum := by decide
  have hdescent : baseEnd_974915 < baseStart_974915 := by decide
  rcases family_descends (prefixWord ++ tailWord_974915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974932 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_974932 : Nat := 118140960795 + 974932 * 2 ^ 59
def prefixEnd_974932 : Nat := 4983230072969 + 3 ^ 40 * 974932 * 2
def baseEnd_974932 : Nat := 444985530177142051347889

theorem tailTrace_974932 : CollatzResearch.WordTrace tailWord_974932 prefixEnd_974932 444985530177142051347889 := by
  unfold tailWord_974932
  simp only [CollatzResearch.WordTrace]
  refine ⟨17779345651997671987279525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23705794202663562649706033 17779345651997671987279525)
  ·
    refine ⟨3333627309749563497614911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17779345651997671987279525 3333627309749563497614911)
    ·
      refine ⟨5000440964624345246422367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3333627309749563497614911 5000440964624345246422367)
      ·
        refine ⟨7500661446936517869633551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5000440964624345246422367 7500661446936517869633551)
        ·
          refine ⟨11250992170404776804450327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7500661446936517869633551 11250992170404776804450327)
          ·
            refine ⟨16876488255607165206675491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11250992170404776804450327 16876488255607165206675491)
            ·
              refine ⟨25314732383410747810013237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16876488255607165206675491 25314732383410747810013237)
              ·
                refine ⟨2373256160944757607188741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25314732383410747810013237 2373256160944757607188741)
                ·
                  refine ⟨444985530177142051347889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2373256160944757607188741 444985530177142051347889)
                  ·
                    rfl

theorem cell20_974932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_974932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974932 prefixEnd_974932 := by exact prefixLift 974932
  have htrace : WordTrace (prefixWord ++ tailWord_974932) baseStart_974932 baseEnd_974932 := by
    simpa [prefixWord, tailWord_974932, baseEnd_974932] using wordTrace_append hprefix tailTrace_974932
  have hstable : (prefixWord ++ tailWord_974932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974932).length < 2 ^ (prefixWord ++ tailWord_974932).sum := by decide
  have hdescent : baseEnd_974932 < baseStart_974932 := by decide
  rcases family_descends (prefixWord ++ tailWord_974932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974956 : List Nat := [2, 2, 1, 1, 3, 4, 3, 4]
def baseStart_974956 : Nat := 118140960795 + 974956 * 2 ^ 59
def prefixEnd_974956 : Nat := 4983230072969 + 3 ^ 40 * 974956 * 2
def baseEnd_974956 : Nat := 148332161477034878182597

theorem tailTrace_974956 : CollatzResearch.WordTrace tailWord_974956 prefixEnd_974956 148332161477034878182597 := by
  unfold tailWord_974956
  simp only [CollatzResearch.WordTrace]
  refine ⟨17779783327954198036716361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23706377770605597382288481 17779783327954198036716361)
  ·
    refine ⟨13334837495965648527537271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17779783327954198036716361 13334837495965648527537271)
    ·
      refine ⟨20002256243948472791305907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13334837495965648527537271 20002256243948472791305907)
      ·
        refine ⟨30003384365922709186958861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20002256243948472791305907 30003384365922709186958861)
        ·
          refine ⟨11251269137221015945109573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30003384365922709186958861 11251269137221015945109573)
          ·
            refine ⟨2109612963228940489708045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11251269137221015945109573 2109612963228940489708045)
            ·
              refine ⟨791104861210852683640517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2109612963228940489708045 791104861210852683640517)
              ·
                refine ⟨148332161477034878182597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 791104861210852683640517 148332161477034878182597)
                ·
                  rfl

theorem cell20_974956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_974956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974956 prefixEnd_974956 := by exact prefixLift 974956
  have htrace : WordTrace (prefixWord ++ tailWord_974956) baseStart_974956 baseEnd_974956 := by
    simpa [prefixWord, tailWord_974956, baseEnd_974956] using wordTrace_append hprefix tailTrace_974956
  have hstable : (prefixWord ++ tailWord_974956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974956).length < 2 ^ (prefixWord ++ tailWord_974956).sum := by decide
  have hdescent : baseEnd_974956 < baseStart_974956 := by decide
  rcases family_descends (prefixWord ++ tailWord_974956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_974966 : List Nat := [5, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_974966 : Nat := 118140960795 + 974966 * 2 ^ 59
def prefixEnd_974966 : Nat := 4983230072969 + 3 ^ 40 * 974966 * 2
def baseEnd_974966 : Nat := 445001048703589044214417

theorem tailTrace_974966 : CollatzResearch.WordTrace tailWord_974966 prefixEnd_974966 445001048703589044214417 := by
  unfold tailWord_974966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222495711617010486331047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23706620923914778520864501 2222495711617010486331047)
  ·
    refine ⟨3333743567425515729496571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2222495711617010486331047 3333743567425515729496571)
    ·
      refine ⟨5000615351138273594244857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3333743567425515729496571 5000615351138273594244857)
      ·
        refine ⟨3750461513353705195683643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5000615351138273594244857 3750461513353705195683643)
        ·
          refine ⟨5625692270030557793525465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3750461513353705195683643 5625692270030557793525465)
          ·
            refine ⟨4219269202522918345144099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5625692270030557793525465 4219269202522918345144099)
            ·
              refine ⟨6328903803784377517716149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4219269202522918345144099 6328903803784377517716149)
              ·
                refine ⟨593334731604785392285889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6328903803784377517716149 593334731604785392285889)
                ·
                  refine ⟨445001048703589044214417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593334731604785392285889 445001048703589044214417)
                  ·
                    rfl

theorem cell20_974966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_974966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_974966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_974966 prefixEnd_974966 := by exact prefixLift 974966
  have htrace : WordTrace (prefixWord ++ tailWord_974966) baseStart_974966 baseEnd_974966 := by
    simpa [prefixWord, tailWord_974966, baseEnd_974966] using wordTrace_append hprefix tailTrace_974966
  have hstable : (prefixWord ++ tailWord_974966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_974966).length < 2 ^ (prefixWord ++ tailWord_974966).sum := by decide
  have hdescent : baseEnd_974966 < baseStart_974966 := by decide
  rcases family_descends (prefixWord ++ tailWord_974966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975008 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_975008 : Nat := 118140960795 + 975008 * 2 ^ 59
def prefixEnd_975008 : Nat := 4983230072969 + 3 ^ 40 * 975008 * 2
def baseEnd_975008 : Nat := 445020218648023564814245

theorem tailTrace_975008 : CollatzResearch.WordTrace tailWord_975008 prefixEnd_975008 445020218648023564814245 := by
  unfold tailWord_975008
  simp only [CollatzResearch.WordTrace]
  refine ⟨17780731625860004477162839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23707642167813339302883785 17780731625860004477162839)
  ·
    refine ⟨26671097438790006715744259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17780731625860004477162839 26671097438790006715744259)
    ·
      refine ⟨40006646158185010073616389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26671097438790006715744259 40006646158185010073616389)
      ·
        refine ⟨7501246154659689388803073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40006646158185010073616389 7501246154659689388803073)
        ·
          refine ⟨5625934615994767041602305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7501246154659689388803073 5625934615994767041602305)
          ·
            refine ⟨4219450961996075281201729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5625934615994767041602305 4219450961996075281201729)
            ·
              refine ⟨3164588221497056460901297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4219450961996075281201729 3164588221497056460901297)
              ·
                refine ⟨2373441166122792345675973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3164588221497056460901297 2373441166122792345675973)
                ·
                  refine ⟨445020218648023564814245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2373441166122792345675973 445020218648023564814245)
                  ·
                    rfl

theorem cell20_975008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_975008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975008 prefixEnd_975008 := by exact prefixLift 975008
  have htrace : WordTrace (prefixWord ++ tailWord_975008) baseStart_975008 baseEnd_975008 := by
    simpa [prefixWord, tailWord_975008, baseEnd_975008] using wordTrace_append hprefix tailTrace_975008
  have hstable : (prefixWord ++ tailWord_975008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975008).length < 2 ^ (prefixWord ++ tailWord_975008).sum := by decide
  have hdescent : baseEnd_975008 < baseStart_975008 := by decide
  rcases family_descends (prefixWord ++ tailWord_975008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975021 : List Nat := [1, 5, 2, 1, 2, 3, 1, 3, 2]
def baseStart_975021 : Nat := 118140960795 + 975021 * 2 ^ 59
def prefixEnd_975021 : Nat := 4983230072969 + 3 ^ 40 * 975021 * 2
def baseEnd_975021 : Nat := 445026152202253297380859

theorem tailTrace_975021 : CollatzResearch.WordTrace tailWord_975021 prefixEnd_975021 445026152202253297380859 := by
  unfold tailWord_975021
  simp only [CollatzResearch.WordTrace]
  refine ⟨35561937400672912174548917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23707958267115274783032611 35561937400672912174548917)
  ·
    refine ⟨3333931631313085516363961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35561937400672912174548917 3333931631313085516363961)
    ·
      refine ⟨2500448723484814137272971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3333931631313085516363961 2500448723484814137272971)
      ·
        refine ⟨3750673085227221205909457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500448723484814137272971 3750673085227221205909457)
        ·
          refine ⟨2813004813920415904432093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3750673085227221205909457 2813004813920415904432093)
          ·
            refine ⟨1054876805220155964162035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2813004813920415904432093 1054876805220155964162035)
            ·
              refine ⟨1582315207830233946243053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054876805220155964162035 1582315207830233946243053)
              ·
                refine ⟨593368202936337729841145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1582315207830233946243053 593368202936337729841145)
                ·
                  refine ⟨445026152202253297380859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593368202936337729841145 445026152202253297380859)
                  ·
                    rfl

theorem cell20_975021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_975021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975021 prefixEnd_975021 := by exact prefixLift 975021
  have htrace : WordTrace (prefixWord ++ tailWord_975021) baseStart_975021 baseEnd_975021 := by
    simpa [prefixWord, tailWord_975021, baseEnd_975021] using wordTrace_append hprefix tailTrace_975021
  have hstable : (prefixWord ++ tailWord_975021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975021).length < 2 ^ (prefixWord ++ tailWord_975021).sum := by decide
  have hdescent : baseEnd_975021 < baseStart_975021 := by decide
  rcases family_descends (prefixWord ++ tailWord_975021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975052 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 3]
def baseStart_975052 : Nat := 118140960795 + 975052 * 2 ^ 59
def prefixEnd_975052 : Nat := 4983230072969 + 3 ^ 40 * 975052 * 2
def baseEnd_975052 : Nat := 445040301446954967347399

theorem tailTrace_975052 : CollatzResearch.WordTrace tailWord_975052 prefixEnd_975052 445040301446954967347399 := by
  unfold tailWord_975052
  simp only [CollatzResearch.WordTrace]
  refine ⟨17781534031780302234463705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23708712042373736312618273 17781534031780302234463705)
  ·
    refine ⟨13336150523835226675847779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17781534031780302234463705 13336150523835226675847779)
    ·
      refine ⟨20004225785752840013771669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13336150523835226675847779 20004225785752840013771669)
      ·
        refine ⟨937698083707164375645547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20004225785752840013771669 937698083707164375645547)
        ·
          refine ⟨1406547125560746563468321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937698083707164375645547 1406547125560746563468321)
          ·
            refine ⟨1054910344170559922601241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406547125560746563468321 1054910344170559922601241)
            ·
              refine ⟨791182758127919941950931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054910344170559922601241 791182758127919941950931)
              ·
                refine ⟨1186774137191879912926397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791182758127919941950931 1186774137191879912926397)
                ·
                  refine ⟨445040301446954967347399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186774137191879912926397 445040301446954967347399)
                  ·
                    rfl

theorem cell20_975052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_975052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975052 prefixEnd_975052 := by exact prefixLift 975052
  have htrace : WordTrace (prefixWord ++ tailWord_975052) baseStart_975052 baseEnd_975052 := by
    simpa [prefixWord, tailWord_975052, baseEnd_975052] using wordTrace_append hprefix tailTrace_975052
  have hstable : (prefixWord ++ tailWord_975052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975052).length < 2 ^ (prefixWord ++ tailWord_975052).sum := by decide
  have hdescent : baseEnd_975052 < baseStart_975052 := by decide
  rcases family_descends (prefixWord ++ tailWord_975052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975139 : List Nat := [1, 1, 1, 4, 2, 2, 4, 3, 2]
def baseStart_975139 : Nat := 118140960795 + 975139 * 2 ^ 59
def prefixEnd_975139 : Nat := 4983230072969 + 3 ^ 40 * 975139 * 2
def baseEnd_975139 : Nat := 445080010617569331447043

theorem tailTrace_975139 : CollatzResearch.WordTrace tailWord_975139 prefixEnd_975139 445080010617569331447043 := by
  unfold tailWord_975139
  simp only [CollatzResearch.WordTrace]
  refine ⟨35566241214245418327344471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23710827476163612218229647 35566241214245418327344471)
  ·
    refine ⟨53349361821368127491016707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35566241214245418327344471 53349361821368127491016707)
    ·
      refine ⟨80024042732052191236525061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53349361821368127491016707 80024042732052191236525061)
      ·
        refine ⟨15004508012259785856848449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80024042732052191236525061 15004508012259785856848449)
        ·
          refine ⟨11253381009194839392636337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15004508012259785856848449 11253381009194839392636337)
          ·
            refine ⟨8440035756896129544477253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11253381009194839392636337 8440035756896129544477253)
            ·
              refine ⟨1582506704418024289589485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8440035756896129544477253 1582506704418024289589485)
              ·
                refine ⟨593440014156759108596057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1582506704418024289589485 593440014156759108596057)
                ·
                  refine ⟨445080010617569331447043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593440014156759108596057 445080010617569331447043)
                  ·
                    rfl

theorem cell20_975139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 2].length) (baseStart_975139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975139 prefixEnd_975139 := by exact prefixLift 975139
  have htrace : WordTrace (prefixWord ++ tailWord_975139) baseStart_975139 baseEnd_975139 := by
    simpa [prefixWord, tailWord_975139, baseEnd_975139] using wordTrace_append hprefix tailTrace_975139
  have hstable : (prefixWord ++ tailWord_975139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975139).length < 2 ^ (prefixWord ++ tailWord_975139).sum := by decide
  have hdescent : baseEnd_975139 < baseStart_975139 := by decide
  rcases family_descends (prefixWord ++ tailWord_975139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975146 : List Nat := [3, 1, 4, 2, 2, 1, 7]
def baseStart_975146 : Nat := 118140960795 + 975146 * 2 ^ 59
def prefixEnd_975146 : Nat := 4983230072969 + 3 ^ 40 * 975146 * 2
def baseEnd_975146 : Nat := 49453689512034268690409

theorem tailTrace_975146 : CollatzResearch.WordTrace tailWord_975146 prefixEnd_975146 49453689512034268690409 := by
  unfold tailWord_975146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8891624131305014630712323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23710997683480039015232861 8891624131305014630712323)
  ·
    refine ⟨13337436196957521946068485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8891624131305014630712323 13337436196957521946068485)
    ·
      refine ⟨2500769286929535364887841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13337436196957521946068485 2500769286929535364887841)
      ·
        refine ⟨1875576965197151523665881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2500769286929535364887841 1875576965197151523665881)
        ·
          refine ⟨1406682723897863642749411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1875576965197151523665881 1406682723897863642749411)
          ·
            refine ⟨2110024085846795464124117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406682723897863642749411 2110024085846795464124117)
            ·
              refine ⟨49453689512034268690409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2110024085846795464124117 49453689512034268690409)
              ·
                rfl

theorem cell20_975146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 7].length) (baseStart_975146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975146 prefixEnd_975146 := by exact prefixLift 975146
  have htrace : WordTrace (prefixWord ++ tailWord_975146) baseStart_975146 baseEnd_975146 := by
    simpa [prefixWord, tailWord_975146, baseEnd_975146] using wordTrace_append hprefix tailTrace_975146
  have hstable : (prefixWord ++ tailWord_975146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975146).length < 2 ^ (prefixWord ++ tailWord_975146).sum := by decide
  have hdescent : baseEnd_975146 < baseStart_975146 := by decide
  rcases family_descends (prefixWord ++ tailWord_975146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975153 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 5]
def baseStart_975153 : Nat := 118140960795 + 975153 * 2 ^ 59
def prefixEnd_975153 : Nat := 4983230072969 + 3 ^ 40 * 975153 * 2
def baseEnd_975153 : Nat := 445086400599047504980319

theorem tailTrace_975153 : CollatzResearch.WordTrace tailWord_975153 prefixEnd_975153 445086400599047504980319 := by
  unfold tailWord_975153
  simp only [CollatzResearch.WordTrace]
  refine ⟨35566751836194698718354113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23711167890796465812236075 35566751836194698718354113)
  ·
    refine ⟨26675063877146024038765585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35566751836194698718354113 26675063877146024038765585)
    ·
      refine ⟨20006297907859518029074189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26675063877146024038765585 20006297907859518029074189)
      ·
        refine ⟨7502361715447319260902821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20006297907859518029074189 7502361715447319260902821)
        ·
          refine ⟨1406692821646372361419279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7502361715447319260902821 1406692821646372361419279)
          ·
            refine ⟨2110039232469558542128919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406692821646372361419279 2110039232469558542128919)
            ·
              refine ⟨3165058848704337813193379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110039232469558542128919 3165058848704337813193379)
              ·
                refine ⟨4747588273056506719790069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3165058848704337813193379 4747588273056506719790069)
                ·
                  refine ⟨445086400599047504980319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4747588273056506719790069 445086400599047504980319)
                  ·
                    rfl

theorem cell20_975153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_975153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975153 prefixEnd_975153 := by exact prefixLift 975153
  have htrace : WordTrace (prefixWord ++ tailWord_975153) baseStart_975153 baseEnd_975153 := by
    simpa [prefixWord, tailWord_975153, baseEnd_975153] using wordTrace_append hprefix tailTrace_975153
  have hstable : (prefixWord ++ tailWord_975153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975153).length < 2 ^ (prefixWord ++ tailWord_975153).sum := by decide
  have hdescent : baseEnd_975153 < baseStart_975153 := by decide
  rcases family_descends (prefixWord ++ tailWord_975153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975156 : List Nat := [2, 5, 1, 1, 1, 2, 2, 4, 2]
def baseStart_975156 : Nat := 118140960795 + 975156 * 2 ^ 59
def prefixEnd_975156 : Nat := 4983230072969 + 3 ^ 40 * 975156 * 2
def baseEnd_975156 : Nat := 445087769880792827880307

theorem tailTrace_975156 : CollatzResearch.WordTrace tailWord_975156 prefixEnd_975156 445087769880792827880307 := by
  unfold tailWord_975156
  simp only [CollatzResearch.WordTrace]
  refine ⟨17783430627591915115356661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23711240836789220153808881 17783430627591915115356661)
  ·
    refine ⟨1667196621336742042064687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17783430627591915115356661 1667196621336742042064687)
    ·
      refine ⟨2500794932005113063097031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667196621336742042064687 2500794932005113063097031)
      ·
        refine ⟨3751192398007669594645547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500794932005113063097031 3751192398007669594645547)
        ·
          refine ⟨5626788597011504391968321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751192398007669594645547 5626788597011504391968321)
          ·
            refine ⟨4220091447758628293976241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5626788597011504391968321 4220091447758628293976241)
            ·
              refine ⟨3165068585818971220482181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4220091447758628293976241 3165068585818971220482181)
              ·
                refine ⟨593450359841057103840409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3165068585818971220482181 593450359841057103840409)
                ·
                  refine ⟨445087769880792827880307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593450359841057103840409 445087769880792827880307)
                  ·
                    rfl

theorem cell20_975156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_975156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975156 prefixEnd_975156 := by exact prefixLift 975156
  have htrace : WordTrace (prefixWord ++ tailWord_975156) baseStart_975156 baseEnd_975156 := by
    simpa [prefixWord, tailWord_975156, baseEnd_975156] using wordTrace_append hprefix tailTrace_975156
  have hstable : (prefixWord ++ tailWord_975156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975156).length < 2 ^ (prefixWord ++ tailWord_975156).sum := by decide
  have hdescent : baseEnd_975156 < baseStart_975156 := by decide
  rcases family_descends (prefixWord ++ tailWord_975156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975184 : List Nat := [2, 1, 1, 1, 1, 8, 2, 4]
def baseStart_975184 : Nat := 118140960795 + 975184 * 2 ^ 59
def prefixEnd_975184 : Nat := 4983230072969 + 3 ^ 40 * 975184 * 2
def baseEnd_975184 : Nat := 148366849947916391648953

theorem tailTrace_975184 : CollatzResearch.WordTrace tailWord_975184 prefixEnd_975184 148366849947916391648953 := by
  unfold tailWord_975184
  simp only [CollatzResearch.WordTrace]
  refine ⟨17783941249541195506366303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23711921666054927341821737 17783941249541195506366303)
  ·
    refine ⟨26675911874311793259549455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17783941249541195506366303 26675911874311793259549455)
    ·
      refine ⟨40013867811467689889324183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26675911874311793259549455 40013867811467689889324183)
      ·
        refine ⟨60020801717201534833986275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40013867811467689889324183 60020801717201534833986275)
        ·
          refine ⟨90031202575802302250979413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60020801717201534833986275 90031202575802302250979413)
          ·
            refine ⟨1055053155185183229503665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 90031202575802302250979413 1055053155185183229503665)
            ·
              refine ⟨791289866388887422127749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055053155185183229503665 791289866388887422127749)
              ·
                refine ⟨148366849947916391648953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 791289866388887422127749 148366849947916391648953)
                ·
                  rfl

theorem cell20_975184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_975184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975184 prefixEnd_975184 := by exact prefixLift 975184
  have htrace : WordTrace (prefixWord ++ tailWord_975184) baseStart_975184 baseEnd_975184 := by
    simpa [prefixWord, tailWord_975184, baseEnd_975184] using wordTrace_append hprefix tailTrace_975184
  have hstable : (prefixWord ++ tailWord_975184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975184).length < 2 ^ (prefixWord ++ tailWord_975184).sum := by decide
  have hdescent : baseEnd_975184 < baseStart_975184 := by decide
  rcases family_descends (prefixWord ++ tailWord_975184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975205 : List Nat := [1, 3, 1, 3, 1, 5, 6]
def baseStart_975205 : Nat := 118140960795 + 975205 * 2 ^ 59
def prefixEnd_975205 : Nat := 4983230072969 + 3 ^ 40 * 975205 * 2
def baseEnd_975205 : Nat := 49456681646218492805197

theorem tailTrace_975205 : CollatzResearch.WordTrace tailWord_975205 prefixEnd_975205 49456681646218492805197 := by
  unfold tailWord_975205
  simp only [CollatzResearch.WordTrace]
  refine ⟨35568648432006311599247069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23712432288004207732831379 35568648432006311599247069)
  ·
    refine ⟨13338243162002366849717651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35568648432006311599247069 13338243162002366849717651)
    ·
      refine ⟨20007364743003550274576477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13338243162002366849717651 20007364743003550274576477)
      ·
        refine ⟨7502761778626331352966179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20007364743003550274576477 7502761778626331352966179)
        ·
          refine ⟨11254142667939497029449269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502761778626331352966179 11254142667939497029449269)
          ·
            refine ⟨1055075875119327846510869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11254142667939497029449269 1055075875119327846510869)
            ·
              refine ⟨49456681646218492805197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1055075875119327846510869 49456681646218492805197)
              ·
                rfl

theorem cell20_975205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 6].length) (baseStart_975205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975205 prefixEnd_975205 := by exact prefixLift 975205
  have htrace : WordTrace (prefixWord ++ tailWord_975205) baseStart_975205 baseEnd_975205 := by
    simpa [prefixWord, tailWord_975205, baseEnd_975205] using wordTrace_append hprefix tailTrace_975205
  have hstable : (prefixWord ++ tailWord_975205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975205).length < 2 ^ (prefixWord ++ tailWord_975205).sum := by decide
  have hdescent : baseEnd_975205 < baseStart_975205 := by decide
  rcases family_descends (prefixWord ++ tailWord_975205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975229 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 3]
def baseStart_975229 : Nat := 118140960795 + 975229 * 2 ^ 59
def prefixEnd_975229 : Nat := 4983230072969 + 3 ^ 40 * 975229 * 2
def baseEnd_975229 : Nat := 445121089069929018446675

theorem tailTrace_975229 : CollatzResearch.WordTrace tailWord_975229 prefixEnd_975229 445121089069929018446675 := by
  unfold tailWord_975229
  simp only [CollatzResearch.WordTrace]
  refine ⟨35569523783919363698120741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23713015855946242465413827 35569523783919363698120741)
  ·
    refine ⟨6669285709484880693397639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35569523783919363698120741 6669285709484880693397639)
    ·
      refine ⟨10003928564227321040096459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6669285709484880693397639 10003928564227321040096459)
      ·
        refine ⟨15005892846340981560144689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10003928564227321040096459 15005892846340981560144689)
        ·
          refine ⟨11254419634755736170108517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15005892846340981560144689 11254419634755736170108517)
          ·
            refine ⟨2110203681516700531895347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11254419634755736170108517 2110203681516700531895347)
            ·
              refine ⟨3165305522275050797843021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110203681516700531895347 3165305522275050797843021)
              ·
                refine ⟨1186989570853144049191133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3165305522275050797843021 1186989570853144049191133)
                ·
                  refine ⟨445121089069929018446675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1186989570853144049191133 445121089069929018446675)
                  ·
                    rfl

theorem cell20_975229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_975229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975229 prefixEnd_975229 := by exact prefixLift 975229
  have htrace : WordTrace (prefixWord ++ tailWord_975229) baseStart_975229 baseEnd_975229 := by
    simpa [prefixWord, tailWord_975229, baseEnd_975229] using wordTrace_append hprefix tailTrace_975229
  have hstable : (prefixWord ++ tailWord_975229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975229).length < 2 ^ (prefixWord ++ tailWord_975229).sum := by decide
  have hdescent : baseEnd_975229 < baseStart_975229 := by decide
  rcases family_descends (prefixWord ++ tailWord_975229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975264 : List Nat := [2, 1, 1, 4, 1, 11]
def baseStart_975264 : Nat := 118140960795 + 975264 * 2 ^ 59
def prefixEnd_975264 : Nat := 4983230072969 + 3 ^ 40 * 975264 * 2
def baseEnd_975264 : Nat := 16486557926800905639995

theorem tailTrace_975264 : CollatzResearch.WordTrace tailWord_975264 prefixEnd_975264 16486557926800905639995 := by
  unfold tailWord_975264
  simp only [CollatzResearch.WordTrace]
  refine ⟨17785400169396282337822423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23713866892528376450429897 17785400169396282337822423)
  ·
    refine ⟨26678100254094423506733635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17785400169396282337822423 26678100254094423506733635)
    ·
      refine ⟨40017150381141635260100453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26678100254094423506733635 40017150381141635260100453)
      ·
        refine ⟨7503215696464056611268835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40017150381141635260100453 7503215696464056611268835)
        ·
          refine ⟨11254823544696084916903253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7503215696464056611268835 11254823544696084916903253)
          ·
            refine ⟨16486557926800905639995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11254823544696084916903253 16486557926800905639995)
            ·
              rfl

theorem cell20_975264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 11].length) (baseStart_975264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975264 prefixEnd_975264 := by exact prefixLift 975264
  have htrace : WordTrace (prefixWord ++ tailWord_975264) baseStart_975264 baseEnd_975264 := by
    simpa [prefixWord, tailWord_975264, baseEnd_975264] using wordTrace_append hprefix tailTrace_975264
  have hstable : (prefixWord ++ tailWord_975264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975264).length < 2 ^ (prefixWord ++ tailWord_975264).sum := by decide
  have hdescent : baseEnd_975264 < baseStart_975264 := by decide
  rcases family_descends (prefixWord ++ tailWord_975264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975267 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 3]
def baseStart_975267 : Nat := 118140960795 + 975267 * 2 ^ 59
def prefixEnd_975267 : Nat := 4983230072969 + 3 ^ 40 * 975267 * 2
def baseEnd_975267 : Nat := 445138433305369775179853

theorem tailTrace_975267 : CollatzResearch.WordTrace tailWord_975267 prefixEnd_975267 445138433305369775179853 := by
  unfold tailWord_975267
  simp only [CollatzResearch.WordTrace]
  refine ⟨35570909757781696188004055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23713939838521130792002703 35570909757781696188004055)
  ·
    refine ⟨53356364636672544282006083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35570909757781696188004055 53356364636672544282006083)
    ·
      refine ⟨80034546955008816423009125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53356364636672544282006083 80034546955008816423009125)
      ·
        refine ⟨15006477554064153079314211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80034546955008816423009125 15006477554064153079314211)
        ·
          refine ⟨22509716331096229618971317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15006477554064153079314211 22509716331096229618971317)
          ·
            refine ⟨2110285906040271526778561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22509716331096229618971317 2110285906040271526778561)
            ·
              refine ⟨1582714429530203645083921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2110285906040271526778561 1582714429530203645083921)
              ·
                refine ⟨1187035822147652733812941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1582714429530203645083921 1187035822147652733812941)
                ·
                  refine ⟨445138433305369775179853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187035822147652733812941 445138433305369775179853)
                  ·
                    rfl

theorem cell20_975267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 3].length) (baseStart_975267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975267 prefixEnd_975267 := by exact prefixLift 975267
  have htrace : WordTrace (prefixWord ++ tailWord_975267) baseStart_975267 baseEnd_975267 := by
    simpa [prefixWord, tailWord_975267, baseEnd_975267] using wordTrace_append hprefix tailTrace_975267
  have hstable : (prefixWord ++ tailWord_975267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975267).length < 2 ^ (prefixWord ++ tailWord_975267).sum := by decide
  have hdescent : baseEnd_975267 < baseStart_975267 := by decide
  rcases family_descends (prefixWord ++ tailWord_975267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975277 : List Nat := [1, 5, 2, 2, 2, 2, 1, 5]
def baseStart_975277 : Nat := 118140960795 + 975277 * 2 ^ 59
def prefixEnd_975277 : Nat := 4983230072969 + 3 ^ 40 * 975277 * 2
def baseEnd_975277 : Nat := 148380999192618061615493

theorem tailTrace_975277 : CollatzResearch.WordTrace tailWord_975277 prefixEnd_975277 148380999192618061615493 := by
  unfold tailWord_975277
  simp only [CollatzResearch.WordTrace]
  refine ⟨35571274487745467895868085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23714182991830311930578723 35571274487745467895868085)
  ·
    refine ⟨3334806983226137615237633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35571274487745467895868085 3334806983226137615237633)
    ·
      refine ⟨2501105237419603211428225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3334806983226137615237633 2501105237419603211428225)
      ·
        refine ⟨1875828928064702408571169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2501105237419603211428225 1875828928064702408571169)
        ·
          refine ⟨1406871696048526806428377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1875828928064702408571169 1406871696048526806428377)
          ·
            refine ⟨1055153772036395104821283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1406871696048526806428377 1055153772036395104821283)
            ·
              refine ⟨1582730658054592657231925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055153772036395104821283 1582730658054592657231925)
              ·
                refine ⟨148380999192618061615493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1582730658054592657231925 148380999192618061615493)
                ·
                  rfl

theorem cell20_975277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 5].length) (baseStart_975277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975277 prefixEnd_975277 := by exact prefixLift 975277
  have htrace : WordTrace (prefixWord ++ tailWord_975277) baseStart_975277 baseEnd_975277 := by
    simpa [prefixWord, tailWord_975277, baseEnd_975277] using wordTrace_append hprefix tailTrace_975277
  have hstable : (prefixWord ++ tailWord_975277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975277).length < 2 ^ (prefixWord ++ tailWord_975277).sum := by decide
  have hdescent : baseEnd_975277 < baseStart_975277 := by decide
  rcases family_descends (prefixWord ++ tailWord_975277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975281 : List Nat := [1, 2, 2, 4, 1, 2, 3, 5]
def baseStart_975281 : Nat := 118140960795 + 975281 * 2 ^ 59
def prefixEnd_975281 : Nat := 4983230072969 + 3 ^ 40 * 975281 * 2
def baseEnd_975281 : Nat := 148381607762282649571043

theorem tailTrace_975281 : CollatzResearch.WordTrace tailWord_975281 prefixEnd_975281 148381607762282649571043 := by
  unfold tailWord_975281
  simp only [CollatzResearch.WordTrace]
  refine ⟨35571420379730976579013697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23714280253153984386009131 35571420379730976579013697)
  ·
    refine ⟨26678565284798232434260273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35571420379730976579013697 26678565284798232434260273)
    ·
      refine ⟨20008923963598674325695205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26678565284798232434260273 20008923963598674325695205)
      ·
        refine ⟨3751673243174751436067851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20008923963598674325695205 3751673243174751436067851)
        ·
          refine ⟨5627509864762127154101777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3751673243174751436067851 5627509864762127154101777)
          ·
            refine ⟨4220632398571595365576333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5627509864762127154101777 4220632398571595365576333)
            ·
              refine ⟨1582737149464348262091125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4220632398571595365576333 1582737149464348262091125)
              ·
                refine ⟨148381607762282649571043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1582737149464348262091125 148381607762282649571043)
                ·
                  rfl

theorem cell20_975281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_975281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975281 prefixEnd_975281 := by exact prefixLift 975281
  have htrace : WordTrace (prefixWord ++ tailWord_975281) baseStart_975281 baseEnd_975281 := by
    simpa [prefixWord, tailWord_975281, baseEnd_975281] using wordTrace_append hprefix tailTrace_975281
  have hstable : (prefixWord ++ tailWord_975281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975281).length < 2 ^ (prefixWord ++ tailWord_975281).sum := by decide
  have hdescent : baseEnd_975281 < baseStart_975281 := by decide
  rcases family_descends (prefixWord ++ tailWord_975281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975308 : List Nat := [2, 2, 1, 4, 3, 1, 2, 3, 2]
def baseStart_975308 : Nat := 118140960795 + 975308 * 2 ^ 59
def prefixEnd_975308 : Nat := 4983230072969 + 3 ^ 40 * 975308 * 2
def baseEnd_975308 : Nat := 445157146822555854813019

theorem tailTrace_975308 : CollatzResearch.WordTrace tailWord_975308 prefixEnd_975308 445157146822555854813019 := by
  unfold tailWord_975308
  simp only [CollatzResearch.WordTrace]
  refine ⟨17786202575316580095123289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23714936767088773460164385 17786202575316580095123289)
  ·
    refine ⟨13339651931487435071342467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17786202575316580095123289 13339651931487435071342467)
    ·
      refine ⟨20009477897231152607013701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13339651931487435071342467 20009477897231152607013701)
      ·
        refine ⟨3751777105730841113815069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20009477897231152607013701 3751777105730841113815069)
        ·
          refine ⟨1406916414649065417680651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3751777105730841113815069 1406916414649065417680651)
          ·
            refine ⟨2110374621973598126520977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406916414649065417680651 2110374621973598126520977)
            ·
              refine ⟨1582780966480198594890733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2110374621973598126520977 1582780966480198594890733)
              ·
                refine ⟨593542862430074473084025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1582780966480198594890733 593542862430074473084025)
                ·
                  refine ⟨445157146822555854813019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593542862430074473084025 445157146822555854813019)
                  ·
                    rfl

theorem cell20_975308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_975308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975308 prefixEnd_975308 := by exact prefixLift 975308
  have htrace : WordTrace (prefixWord ++ tailWord_975308) baseStart_975308 baseEnd_975308 := by
    simpa [prefixWord, tailWord_975308, baseEnd_975308] using wordTrace_append hprefix tailTrace_975308
  have hstable : (prefixWord ++ tailWord_975308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975308).length < 2 ^ (prefixWord ++ tailWord_975308).sum := by decide
  have hdescent : baseEnd_975308 < baseStart_975308 := by decide
  rcases family_descends (prefixWord ++ tailWord_975308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975340 : List Nat := [2, 2, 1, 1, 2, 1, 4, 7]
def baseStart_975340 : Nat := 118140960795 + 975340 * 2 ^ 59
def prefixEnd_975340 : Nat := 4983230072969 + 3 ^ 40 * 975340 * 2
def baseEnd_975340 : Nat := 148390584164835321915407

theorem tailTrace_975340 : CollatzResearch.WordTrace tailWord_975340 prefixEnd_975340 148390584164835321915407 := by
  unfold tailWord_975340
  simp only [CollatzResearch.WordTrace]
  refine ⟨17786786143258614827705737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23715714857678153103607649 17786786143258614827705737)
  ·
    refine ⟨13340089607443961120779303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17786786143258614827705737 13340089607443961120779303)
    ·
      refine ⟨20010134411165941681168955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13340089607443961120779303 20010134411165941681168955)
      ·
        refine ⟨30015201616748912521753433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20010134411165941681168955 30015201616748912521753433)
        ·
          refine ⟨22511401212561684391315075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30015201616748912521753433 22511401212561684391315075)
          ·
            refine ⟨33767101818842526586972613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22511401212561684391315075 33767101818842526586972613)
            ·
              refine ⟨6331331591032973735057365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33767101818842526586972613 6331331591032973735057365)
              ·
                refine ⟨148390584164835321915407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6331331591032973735057365 148390584164835321915407)
                ·
                  rfl

theorem cell20_975340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_975340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975340 prefixEnd_975340 := by exact prefixLift 975340
  have htrace : WordTrace (prefixWord ++ tailWord_975340) baseStart_975340 baseEnd_975340 := by
    simpa [prefixWord, tailWord_975340, baseEnd_975340] using wordTrace_append hprefix tailTrace_975340
  have hstable : (prefixWord ++ tailWord_975340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975340).length < 2 ^ (prefixWord ++ tailWord_975340).sum := by decide
  have hdescent : baseEnd_975340 < baseStart_975340 := by decide
  rcases family_descends (prefixWord ++ tailWord_975340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975350 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_975350 : Nat := 118140960795 + 975350 * 2 ^ 59
def prefixEnd_975350 : Nat := 4983230072969 + 3 ^ 40 * 975350 * 2
def baseEnd_975350 : Nat := 445176316766990375412847

theorem tailTrace_975350 : CollatzResearch.WordTrace tailWord_975350 prefixEnd_975350 445176316766990375412847 := by
  unfold tailWord_975350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223371063530062585204719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23715958010987334242183669 2223371063530062585204719)
  ·
    refine ⟨3335056595295093877807079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2223371063530062585204719 3335056595295093877807079)
    ·
      refine ⟨5002584892942640816710619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3335056595295093877807079 5002584892942640816710619)
      ·
        refine ⟨7503877339413961225065929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002584892942640816710619 7503877339413961225065929)
        ·
          refine ⟨5627908004560470918799447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7503877339413961225065929 5627908004560470918799447)
          ·
            refine ⟨8441862006840706378199171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627908004560470918799447 8441862006840706378199171)
            ·
              refine ⟨12662793010261059567298757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8441862006840706378199171 12662793010261059567298757)
              ·
                refine ⟨2374273689423948668868517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12662793010261059567298757 2374273689423948668868517)
                ·
                  refine ⟨445176316766990375412847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374273689423948668868517 445176316766990375412847)
                  ·
                    rfl

theorem cell20_975350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_975350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975350 prefixEnd_975350 := by exact prefixLift 975350
  have htrace : WordTrace (prefixWord ++ tailWord_975350) baseStart_975350 baseEnd_975350 := by
    simpa [prefixWord, tailWord_975350, baseEnd_975350] using wordTrace_append hprefix tailTrace_975350
  have hstable : (prefixWord ++ tailWord_975350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975350).length < 2 ^ (prefixWord ++ tailWord_975350).sum := by decide
  have hdescent : baseEnd_975350 < baseStart_975350 := by decide
  rcases family_descends (prefixWord ++ tailWord_975350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975384 : List Nat := [2, 1, 2, 3, 3, 2, 3, 2, 2]
def baseStart_975384 : Nat := 118140960795 + 975384 * 2 ^ 59
def prefixEnd_975384 : Nat := 4983230072969 + 3 ^ 40 * 975384 * 2
def baseEnd_975384 : Nat := 445191835293437368279375

theorem tailTrace_975384 : CollatzResearch.WordTrace tailWord_975384 prefixEnd_975384 445191835293437368279375 := by
  unfold tailWord_975384
  simp only [CollatzResearch.WordTrace]
  refine ⟨17787588549178912585006603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23716784732238550113342137 17787588549178912585006603)
  ·
    refine ⟨26681382823768368877509905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17787588549178912585006603 26681382823768368877509905)
    ·
      refine ⟨20011037117826276658132429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26681382823768368877509905 20011037117826276658132429)
      ·
        refine ⟨7504138919184853746799661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20011037117826276658132429 7504138919184853746799661)
        ·
          refine ⟨2814052094694320155049873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7504138919184853746799661 2814052094694320155049873)
          ·
            refine ⟨2110539071020740116287405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2814052094694320155049873 2110539071020740116287405)
            ·
              refine ⟨791452151632777543607777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2110539071020740116287405 791452151632777543607777)
              ·
                refine ⟨593589113724583157705833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791452151632777543607777 593589113724583157705833)
                ·
                  refine ⟨445191835293437368279375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593589113724583157705833 445191835293437368279375)
                  ·
                    rfl

theorem cell20_975384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 2].length) (baseStart_975384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975384 prefixEnd_975384 := by exact prefixLift 975384
  have htrace : WordTrace (prefixWord ++ tailWord_975384) baseStart_975384 baseEnd_975384 := by
    simpa [prefixWord, tailWord_975384, baseEnd_975384] using wordTrace_append hprefix tailTrace_975384
  have hstable : (prefixWord ++ tailWord_975384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975384).length < 2 ^ (prefixWord ++ tailWord_975384).sum := by decide
  have hdescent : baseEnd_975384 < baseStart_975384 := by decide
  rcases family_descends (prefixWord ++ tailWord_975384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975388 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_975388 : Nat := 118140960795 + 975388 * 2 ^ 59
def prefixEnd_975388 : Nat := 4983230072969 + 3 ^ 40 * 975388 * 2
def baseEnd_975388 : Nat := 445193661002431132146025

theorem tailTrace_975388 : CollatzResearch.WordTrace tailWord_975388 prefixEnd_975388 445193661002431132146025 := by
  unfold tailWord_975388
  simp only [CollatzResearch.WordTrace]
  refine ⟨17787661495171666926579409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23716881993562222568772545 17787661495171666926579409)
  ·
    refine ⟨13340746121378750194934557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17787661495171666926579409 13340746121378750194934557)
    ·
      refine ⟨5002779795517031323100459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13340746121378750194934557 5002779795517031323100459)
      ·
        refine ⟨7504169693275546984650689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002779795517031323100459 7504169693275546984650689)
        ·
          refine ⟨5628127269956660238488017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7504169693275546984650689 5628127269956660238488017)
          ·
            refine ⟨4221095452467495178866013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5628127269956660238488017 4221095452467495178866013)
            ·
              refine ⟨1582910794675310692074755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4221095452467495178866013 1582910794675310692074755)
              ·
                refine ⟨2374366192012966038112133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582910794675310692074755 2374366192012966038112133)
                ·
                  refine ⟨445193661002431132146025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374366192012966038112133 445193661002431132146025)
                  ·
                    rfl

theorem cell20_975388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_975388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975388 prefixEnd_975388 := by exact prefixLift 975388
  have htrace : WordTrace (prefixWord ++ tailWord_975388) baseStart_975388 baseEnd_975388 := by
    simpa [prefixWord, tailWord_975388, baseEnd_975388] using wordTrace_append hprefix tailTrace_975388
  have hstable : (prefixWord ++ tailWord_975388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975388).length < 2 ^ (prefixWord ++ tailWord_975388).sum := by decide
  have hdescent : baseEnd_975388 < baseStart_975388 := by decide
  rcases family_descends (prefixWord ++ tailWord_975388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975395 : List Nat := [1, 1, 1, 4, 4, 2, 2, 5]
def baseStart_975395 : Nat := 118140960795 + 975395 * 2 ^ 59
def prefixEnd_975395 : Nat := 4983230072969 + 3 ^ 40 * 975395 * 2
def baseEnd_975395 : Nat := 148398951997723406304221

theorem tailTrace_975395 : CollatzResearch.WordTrace tailWord_975395 prefixEnd_975395 148398951997723406304221 := by
  unfold tailWord_975395
  simp only [CollatzResearch.WordTrace]
  refine ⟨35575578301317974048663639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23717052200878649365775759 35575578301317974048663639)
  ·
    refine ⟨53363367451976961072995459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35575578301317974048663639 53363367451976961072995459)
    ·
      refine ⟨80045051177965441609493189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53363367451976961072995459 80045051177965441609493189)
      ·
        refine ⟨15008447095868520301779973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80045051177965441609493189 15008447095868520301779973)
        ·
          refine ⟨2814083830475347556583745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15008447095868520301779973 2814083830475347556583745)
          ·
            refine ⟨2110562872856510667437809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2814083830475347556583745 2110562872856510667437809)
            ·
              refine ⟨1582922154642383000578357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2110562872856510667437809 1582922154642383000578357)
              ·
                refine ⟨148398951997723406304221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1582922154642383000578357 148398951997723406304221)
                ·
                  rfl

theorem cell20_975395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_975395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975395 prefixEnd_975395 := by exact prefixLift 975395
  have htrace : WordTrace (prefixWord ++ tailWord_975395) baseStart_975395 baseEnd_975395 := by
    simpa [prefixWord, tailWord_975395, baseEnd_975395] using wordTrace_append hprefix tailTrace_975395
  have hstable : (prefixWord ++ tailWord_975395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975395).length < 2 ^ (prefixWord ++ tailWord_975395).sum := by decide
  have hdescent : baseEnd_975395 < baseStart_975395 := by decide
  rcases family_descends (prefixWord ++ tailWord_975395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975409 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 4]
def baseStart_975409 : Nat := 118140960795 + 975409 * 2 ^ 59
def prefixEnd_975409 : Nat := 4983230072969 + 3 ^ 40 * 975409 * 2
def baseEnd_975409 : Nat := 445203245974648392445939

theorem tailTrace_975409 : CollatzResearch.WordTrace tailWord_975409 prefixEnd_975409 445203245974648392445939 := by
  unfold tailWord_975409
  simp only [CollatzResearch.WordTrace]
  refine ⟨35576088923267254439673281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23717392615511502959782187 35576088923267254439673281)
  ·
    refine ⟨26682066692450440829754961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35576088923267254439673281 26682066692450440829754961)
    ·
      refine ⟨20011550019337830622316221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26682066692450440829754961 20011550019337830622316221)
      ·
        refine ⟨7504331257251686483368583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20011550019337830622316221 7504331257251686483368583)
        ·
          refine ⟨11256496885877529725052875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7504331257251686483368583 11256496885877529725052875)
          ·
            refine ⟨16884745328816294587579313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11256496885877529725052875 16884745328816294587579313)
            ·
              refine ⟨12663558996612220940684485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16884745328816294587579313 12663558996612220940684485)
              ·
                refine ⟨2374417311864791426378341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12663558996612220940684485 2374417311864791426378341)
                ·
                  refine ⟨445203245974648392445939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374417311864791426378341 445203245974648392445939)
                  ·
                    rfl

theorem cell20_975409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_975409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975409 prefixEnd_975409 := by exact prefixLift 975409
  have htrace : WordTrace (prefixWord ++ tailWord_975409) baseStart_975409 baseEnd_975409 := by
    simpa [prefixWord, tailWord_975409, baseEnd_975409] using wordTrace_append hprefix tailTrace_975409
  have hstable : (prefixWord ++ tailWord_975409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975409).length < 2 ^ (prefixWord ++ tailWord_975409).sum := by decide
  have hdescent : baseEnd_975409 < baseStart_975409 := by decide
  rcases family_descends (prefixWord ++ tailWord_975409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975416 : List Nat := [2, 1, 2, 1, 4, 1, 1, 8]
def baseStart_975416 : Nat := 118140960795 + 975416 * 2 ^ 59
def prefixEnd_975416 : Nat := 4983230072969 + 3 ^ 40 * 975416 * 2
def baseEnd_975416 : Nat := 148402146988462493070859

theorem tailTrace_975416 : CollatzResearch.WordTrace tailWord_975416 prefixEnd_975416 148402146988462493070859 := by
  unfold tailWord_975416
  simp only [CollatzResearch.WordTrace]
  refine ⟨17788172117120947317589051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23717562822827929756785401 17788172117120947317589051)
  ·
    refine ⟨26682258175681420976383577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17788172117120947317589051 26682258175681420976383577)
    ·
      refine ⟨20011693631761065732287683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26682258175681420976383577 20011693631761065732287683)
      ·
        refine ⟨30017540447641598598431525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20011693631761065732287683 30017540447641598598431525)
        ·
          refine ⟨5628288833932799737205911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30017540447641598598431525 5628288833932799737205911)
          ·
            refine ⟨8442433250899199605808867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628288833932799737205911 8442433250899199605808867)
            ·
              refine ⟨12663649876348799408713301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8442433250899199605808867 12663649876348799408713301)
              ·
                refine ⟨148402146988462493070859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12663649876348799408713301 148402146988462493070859)
                ·
                  rfl

theorem cell20_975416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_975416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975416 prefixEnd_975416 := by exact prefixLift 975416
  have htrace : WordTrace (prefixWord ++ tailWord_975416) baseStart_975416 baseEnd_975416 := by
    simpa [prefixWord, tailWord_975416, baseEnd_975416] using wordTrace_append hprefix tailTrace_975416
  have hstable : (prefixWord ++ tailWord_975416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975416).length < 2 ^ (prefixWord ++ tailWord_975416).sum := by decide
  have hdescent : baseEnd_975416 < baseStart_975416 := by decide
  rcases family_descends (prefixWord ++ tailWord_975416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975447 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 4]
def baseStart_975447 : Nat := 118140960795 + 975447 * 2 ^ 59
def prefixEnd_975447 : Nat := 4983230072969 + 3 ^ 40 * 975447 * 2
def baseEnd_975447 : Nat := 445220590210089149179117

theorem tailTrace_975447 : CollatzResearch.WordTrace tailWord_975447 prefixEnd_975447 445220590210089149179117 := by
  unfold tailWord_975447
  simp only [CollatzResearch.WordTrace]
  refine ⟨35577474897129586929556595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23718316598086391286371063 35577474897129586929556595)
  ·
    refine ⟨53366212345694380394334893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35577474897129586929556595 53366212345694380394334893)
    ·
      refine ⟨20012329629635392647875585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53366212345694380394334893 20012329629635392647875585)
      ·
        refine ⟨15009247222226544485906689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20012329629635392647875585 15009247222226544485906689)
        ·
          refine ⟨11256935416669908364430017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15009247222226544485906689 11256935416669908364430017)
          ·
            refine ⟨8442701562502431273322513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11256935416669908364430017 8442701562502431273322513)
            ·
              refine ⟨6332026171876823454991885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8442701562502431273322513 6332026171876823454991885)
              ·
                refine ⟨2374509814453808795621957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6332026171876823454991885 2374509814453808795621957)
                ·
                  refine ⟨445220590210089149179117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374509814453808795621957 445220590210089149179117)
                  ·
                    rfl

theorem cell20_975447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_975447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975447 prefixEnd_975447 := by exact prefixLift 975447
  have htrace : WordTrace (prefixWord ++ tailWord_975447) baseStart_975447 baseEnd_975447 := by
    simpa [prefixWord, tailWord_975447, baseEnd_975447] using wordTrace_append hprefix tailTrace_975447
  have hstable : (prefixWord ++ tailWord_975447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975447).length < 2 ^ (prefixWord ++ tailWord_975447).sum := by decide
  have hdescent : baseEnd_975447 < baseStart_975447 := by decide
  rcases family_descends (prefixWord ++ tailWord_975447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975481 : List Nat := [1, 2, 1, 3, 3, 3, 2, 3, 2]
def baseStart_975481 : Nat := 118140960795 + 975481 * 2 ^ 59
def prefixEnd_975481 : Nat := 4983230072969 + 3 ^ 40 * 975481 * 2
def baseEnd_975481 : Nat := 445236108736536142045645

theorem tailTrace_975481 : CollatzResearch.WordTrace tailWord_975481 prefixEnd_975481 445236108736536142045645 := by
  unfold tailWord_975481
  simp only [CollatzResearch.WordTrace]
  refine ⟨35578714979006410736294297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23719143319337607157529531 35578714979006410736294297)
  ·
    refine ⟨26684036234254808052220723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35578714979006410736294297 26684036234254808052220723)
    ·
      refine ⟨40026054351382212078331085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26684036234254808052220723 40026054351382212078331085)
      ·
        refine ⟨15009770381768329529374157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40026054351382212078331085 15009770381768329529374157)
        ·
          refine ⟨5628663893163123573515309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15009770381768329529374157 5628663893163123573515309)
          ·
            refine ⟨2110748959936171340068241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5628663893163123573515309 2110748959936171340068241)
            ·
              refine ⟨1583061719952128505051181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2110748959936171340068241 1583061719952128505051181)
              ·
                refine ⟨593648144982048189394193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1583061719952128505051181 593648144982048189394193)
                ·
                  refine ⟨445236108736536142045645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593648144982048189394193 445236108736536142045645)
                  ·
                    rfl

theorem cell20_975481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 2].length) (baseStart_975481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975481 prefixEnd_975481 := by exact prefixLift 975481
  have htrace : WordTrace (prefixWord ++ tailWord_975481) baseStart_975481 baseEnd_975481 := by
    simpa [prefixWord, tailWord_975481, baseEnd_975481] using wordTrace_append hprefix tailTrace_975481
  have hstable : (prefixWord ++ tailWord_975481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975481).length < 2 ^ (prefixWord ++ tailWord_975481).sum := by decide
  have hdescent : baseEnd_975481 < baseStart_975481 := by decide
  rcases family_descends (prefixWord ++ tailWord_975481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975502 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_975502 : Nat := 118140960795 + 975502 * 2 ^ 59
def prefixEnd_975502 : Nat := 4983230072969 + 3 ^ 40 * 975502 * 2
def baseEnd_975502 : Nat := 445245693708753402345559

theorem tailTrace_975502 : CollatzResearch.WordTrace tailWord_975502 prefixEnd_975502 445245693708753402345559 := by
  unfold tailWord_975502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4447435113991291415351095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23719653941286887548539173 4447435113991291415351095)
  ·
    refine ⟨6671152670986937123026643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4447435113991291415351095 6671152670986937123026643)
    ·
      refine ⟨10006729006480405684539965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6671152670986937123026643 10006729006480405684539965)
      ·
        refine ⟨3752523377430152131702487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10006729006480405684539965 3752523377430152131702487)
        ·
          refine ⟨5628785066145228197553731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3752523377430152131702487 5628785066145228197553731)
          ·
            refine ⟨8443177599217842296330597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628785066145228197553731 8443177599217842296330597)
            ·
              refine ⟨1583095799853345430561987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8443177599217842296330597 1583095799853345430561987)
              ·
                refine ⟨2374643699780018145842981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583095799853345430561987 2374643699780018145842981)
                ·
                  refine ⟨445245693708753402345559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374643699780018145842981 445245693708753402345559)
                  ·
                    rfl

theorem cell20_975502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_975502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975502 prefixEnd_975502 := by exact prefixLift 975502
  have htrace : WordTrace (prefixWord ++ tailWord_975502) baseStart_975502 baseEnd_975502 := by
    simpa [prefixWord, tailWord_975502, baseEnd_975502] using wordTrace_append hprefix tailTrace_975502
  have hstable : (prefixWord ++ tailWord_975502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975502).length < 2 ^ (prefixWord ++ tailWord_975502).sum := by decide
  have hdescent : baseEnd_975502 < baseStart_975502 := by decide
  rcases family_descends (prefixWord ++ tailWord_975502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975553 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 4]
def baseStart_975553 : Nat := 118140960795 + 975553 * 2 ^ 59
def prefixEnd_975553 : Nat := 4983230072969 + 3 ^ 40 * 975553 * 2
def baseEnd_975553 : Nat := 445268971498423891645351

theorem tailTrace_975553 : CollatzResearch.WordTrace tailWord_975553 prefixEnd_975553 445268971498423891645351 := by
  unfold tailWord_975553
  simp only [CollatzResearch.WordTrace]
  refine ⟨35581341034745567032915313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23720894023163711355276875 35581341034745567032915313)
  ·
    refine ⟨26686005776059175274686485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35581341034745567032915313 26686005776059175274686485)
    ·
      refine ⟨1250906520752773841000929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26686005776059175274686485 1250906520752773841000929)
      ·
        refine ⟨938179890564580380750697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1250906520752773841000929 938179890564580380750697)
        ·
          refine ⟨703634917923435285563023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938179890564580380750697 703634917923435285563023)
          ·
            refine ⟨1055452376885152928344535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703634917923435285563023 1055452376885152928344535)
            ·
              refine ⟨1583178565327729392516803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055452376885152928344535 1583178565327729392516803)
              ·
                refine ⟨2374767847991594088775205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583178565327729392516803 2374767847991594088775205)
                ·
                  refine ⟨445268971498423891645351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374767847991594088775205 445268971498423891645351)
                  ·
                    rfl

theorem cell20_975553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 4].length) (baseStart_975553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975553 prefixEnd_975553 := by exact prefixLift 975553
  have htrace : WordTrace (prefixWord ++ tailWord_975553) baseStart_975553 baseEnd_975553 := by
    simpa [prefixWord, tailWord_975553, baseEnd_975553] using wordTrace_append hprefix tailTrace_975553
  have hstable : (prefixWord ++ tailWord_975553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975553).length < 2 ^ (prefixWord ++ tailWord_975553).sum := by decide
  have hdescent : baseEnd_975553 < baseStart_975553 := by decide
  rcases family_descends (prefixWord ++ tailWord_975553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975612 : List Nat := [2, 2, 2, 1, 3, 4, 2, 2, 2]
def baseStart_975612 : Nat := 118140960795 + 975612 * 2 ^ 59
def prefixEnd_975612 : Nat := 4983230072969 + 3 ^ 40 * 975612 * 2
def baseEnd_975612 : Nat := 445295900706081908678443

theorem tailTrace_975612 : CollatzResearch.WordTrace tailWord_975612 prefixEnd_975612 445295900706081908678443 := by
  unfold tailWord_975612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17791746470765910054656545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23722328627687880072875393 17791746470765910054656545)
  ·
    refine ⟨13343809853074432540992409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17791746470765910054656545 13343809853074432540992409)
    ·
      refine ⟨10007857389805824405744307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13343809853074432540992409 10007857389805824405744307)
      ·
        refine ⟨15011786084708736608616461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10007857389805824405744307 15011786084708736608616461)
        ·
          refine ⟨5629419781765776228231173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15011786084708736608616461 5629419781765776228231173)
          ·
            refine ⟨1055516209081083042793345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5629419781765776228231173 1055516209081083042793345)
            ·
              refine ⟨791637156810812282095009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055516209081083042793345 791637156810812282095009)
              ·
                refine ⟨593727867608109211571257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791637156810812282095009 593727867608109211571257)
                ·
                  refine ⟨445295900706081908678443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593727867608109211571257 445295900706081908678443)
                  ·
                    rfl

theorem cell20_975612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_975612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975612 prefixEnd_975612 := by exact prefixLift 975612
  have htrace : WordTrace (prefixWord ++ tailWord_975612) baseStart_975612 baseEnd_975612 := by
    simpa [prefixWord, tailWord_975612, baseEnd_975612] using wordTrace_append hprefix tailTrace_975612
  have hstable : (prefixWord ++ tailWord_975612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975612).length < 2 ^ (prefixWord ++ tailWord_975612).sum := by decide
  have hdescent : baseEnd_975612 < baseStart_975612 := by decide
  rcases family_descends (prefixWord ++ tailWord_975612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975623 : List Nat := [1, 1, 4, 4, 1, 1, 3, 5]
def baseStart_975623 : Nat := 118140960795 + 975623 * 2 ^ 59
def prefixEnd_975623 : Nat := 4983230072969 + 3 ^ 40 * 975623 * 2
def baseEnd_975623 : Nat := 148433640468604919770577

theorem tailTrace_975623 : CollatzResearch.WordTrace tailWord_975623 prefixEnd_975623 148433640468604919770577 := by
  unfold tailWord_975623
  simp only [CollatzResearch.WordTrace]
  refine ⟨35583894144491968987963523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23722596096327979325309015 35583894144491968987963523)
  ·
    refine ⟨53375841216737953481945285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35583894144491968987963523 53375841216737953481945285)
    ·
      refine ⟨10007970228138366277864741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53375841216737953481945285 10007970228138366277864741)
      ·
        refine ⟨1876494417775943677099639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10007970228138366277864741 1876494417775943677099639)
        ·
          refine ⟨2814741626663915515649459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876494417775943677099639 2814741626663915515649459)
          ·
            refine ⟨4222112439995873273474189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814741626663915515649459 4222112439995873273474189)
            ·
              refine ⟨1583292164998452477552821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4222112439995873273474189 1583292164998452477552821)
              ·
                refine ⟨148433640468604919770577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1583292164998452477552821 148433640468604919770577)
                ·
                  rfl

theorem cell20_975623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_975623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975623 prefixEnd_975623 := by exact prefixLift 975623
  have htrace : WordTrace (prefixWord ++ tailWord_975623) baseStart_975623 baseEnd_975623 := by
    simpa [prefixWord, tailWord_975623, baseEnd_975623] using wordTrace_append hprefix tailTrace_975623
  have hstable : (prefixWord ++ tailWord_975623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975623).length < 2 ^ (prefixWord ++ tailWord_975623).sum := by decide
  have hdescent : baseEnd_975623 < baseStart_975623 := by decide
  rcases family_descends (prefixWord ++ tailWord_975623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975637 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 4]
def baseStart_975637 : Nat := 118140960795 + 975637 * 2 ^ 59
def prefixEnd_975637 : Nat := 4983230072969 + 3 ^ 40 * 975637 * 2
def baseEnd_975637 : Nat := 445307311387292932845007

theorem tailTrace_975637 : CollatzResearch.WordTrace tailWord_975637 prefixEnd_975637 445307311387292932845007 := by
  unfold tailWord_975637
  simp only [CollatzResearch.WordTrace]
  refine ⟨35584404766441249378973165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23722936510960832919315443 35584404766441249378973165)
  ·
    refine ⟨13344151787415468517114937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35584404766441249378973165 13344151787415468517114937)
    ·
      refine ⟨10008113840561601387836203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13344151787415468517114937 10008113840561601387836203)
      ·
        refine ⟨15012170760842402081754305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10008113840561601387836203 15012170760842402081754305)
        ·
          refine ⟨11259128070631801561315729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15012170760842402081754305 11259128070631801561315729)
          ·
            refine ⟨8444346052973851170986797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11259128070631801561315729 8444346052973851170986797)
            ·
              refine ⟨3166629769865194189120049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8444346052973851170986797 3166629769865194189120049)
              ·
                refine ⟨2374972327398895641840037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3166629769865194189120049 2374972327398895641840037)
                ·
                  refine ⟨445307311387292932845007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2374972327398895641840037 445307311387292932845007)
                  ·
                    rfl

theorem cell20_975637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_975637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975637 prefixEnd_975637 := by exact prefixLift 975637
  have htrace : WordTrace (prefixWord ++ tailWord_975637) baseStart_975637 baseEnd_975637 := by
    simpa [prefixWord, tailWord_975637, baseEnd_975637] using wordTrace_append hprefix tailTrace_975637
  have hstable : (prefixWord ++ tailWord_975637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975637).length < 2 ^ (prefixWord ++ tailWord_975637).sum := by decide
  have hdescent : baseEnd_975637 < baseStart_975637 := by decide
  rcases family_descends (prefixWord ++ tailWord_975637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975651 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_975651 : Nat := 118140960795 + 975651 * 2 ^ 59
def prefixEnd_975651 : Nat := 4983230072969 + 3 ^ 40 * 975651 * 2
def baseEnd_975651 : Nat := 445313701368771106378283

theorem tailTrace_975651 : CollatzResearch.WordTrace tailWord_975651 prefixEnd_975651 445313701368771106378283 := by
  unfold tailWord_975651
  simp only [CollatzResearch.WordTrace]
  refine ⟨35584915388390529769982807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23723276925593686513321871 35584915388390529769982807)
  ·
    refine ⟨53377373082585794654974211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35584915388390529769982807 53377373082585794654974211)
    ·
      refine ⟨80066059623878691982461317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53377373082585794654974211 80066059623878691982461317)
      ·
        refine ⟨15012386179477254746711497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80066059623878691982461317 15012386179477254746711497)
        ·
          refine ⟨11259289634607941060033623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15012386179477254746711497 11259289634607941060033623)
          ·
            refine ⟨16888934451911911590050435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11259289634607941060033623 16888934451911911590050435)
            ·
              refine ⟨25333401677867867385075653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16888934451911911590050435 25333401677867867385075653)
              ·
                refine ⟨4750012814600225134701685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25333401677867867385075653 4750012814600225134701685)
                ·
                  refine ⟨445313701368771106378283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4750012814600225134701685 445313701368771106378283)
                  ·
                    rfl

theorem cell20_975651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_975651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975651 prefixEnd_975651 := by exact prefixLift 975651
  have htrace : WordTrace (prefixWord ++ tailWord_975651) baseStart_975651 baseEnd_975651 := by
    simpa [prefixWord, tailWord_975651, baseEnd_975651] using wordTrace_append hprefix tailTrace_975651
  have hstable : (prefixWord ++ tailWord_975651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975651).length < 2 ^ (prefixWord ++ tailWord_975651).sum := by decide
  have hdescent : baseEnd_975651 < baseStart_975651 := by decide
  rcases family_descends (prefixWord ++ tailWord_975651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975681 : List Nat := [1, 2, 5, 3, 1, 1, 3, 1, 3]
def baseStart_975681 : Nat := 118140960795 + 975681 * 2 ^ 59
def prefixEnd_975681 : Nat := 4983230072969 + 3 ^ 40 * 975681 * 2
def baseEnd_975681 : Nat := 445327394186224335378161

theorem tailTrace_975681 : CollatzResearch.WordTrace tailWord_975681 prefixEnd_975681 445327394186224335378161 := by
  unfold tailWord_975681
  simp only [CollatzResearch.WordTrace]
  refine ⟨35586009578281844893574897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23724006385521229929049931 35586009578281844893574897)
  ·
    refine ⟨26689507183711383670181173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35586009578281844893574897 26689507183711383670181173)
    ·
      refine ⟨2502141298472942219079485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26689507183711383670181173 2502141298472942219079485)
      ·
        refine ⟨938302986927353332154807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2502141298472942219079485 938302986927353332154807)
        ·
          refine ⟨1407454480391029998232211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938302986927353332154807 1407454480391029998232211)
          ·
            refine ⟨2111181720586544997348317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407454480391029998232211 2111181720586544997348317)
            ·
              refine ⟨791693145219954374005619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2111181720586544997348317 791693145219954374005619)
              ·
                refine ⟨1187539717829931561008429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791693145219954374005619 1187539717829931561008429)
                ·
                  refine ⟨445327394186224335378161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187539717829931561008429 445327394186224335378161)
                  ·
                    rfl

theorem cell20_975681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_975681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975681 prefixEnd_975681 := by exact prefixLift 975681
  have htrace : WordTrace (prefixWord ++ tailWord_975681) baseStart_975681 baseEnd_975681 := by
    simpa [prefixWord, tailWord_975681, baseEnd_975681] using wordTrace_append hprefix tailTrace_975681
  have hstable : (prefixWord ++ tailWord_975681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975681).length < 2 ^ (prefixWord ++ tailWord_975681).sum := by decide
  have hdescent : baseEnd_975681 < baseStart_975681 := by decide
  rcases family_descends (prefixWord ++ tailWord_975681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975720 : List Nat := [2, 1, 4, 2, 1, 2, 8]
def baseStart_975720 : Nat := 118140960795 + 975720 * 2 ^ 59
def prefixEnd_975720 : Nat := 4983230072969 + 3 ^ 40 * 975720 * 2
def baseEnd_975720 : Nat := 49482799427657059230889

theorem tailTrace_975720 : CollatzResearch.WordTrace tailWord_975720 prefixEnd_975720 49482799427657059230889 := by
  unfold tailWord_975720
  simp only [CollatzResearch.WordTrace]
  refine ⟨17793716012570277277122307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23724954683427036369496409 17793716012570277277122307)
  ·
    refine ⟨26690574018855415915683461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17793716012570277277122307 26690574018855415915683461)
    ·
      refine ⟨5004482628535390484190649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26690574018855415915683461 5004482628535390484190649)
      ·
        refine ⟨3753361971401542863142987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5004482628535390484190649 3753361971401542863142987)
        ·
          refine ⟨5630042957102314294714481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3753361971401542863142987 5630042957102314294714481)
          ·
            refine ⟨4222532217826735721035861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5630042957102314294714481 4222532217826735721035861)
            ·
              refine ⟨49482799427657059230889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4222532217826735721035861 49482799427657059230889)
              ·
                rfl

theorem cell20_975720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 8].length) (baseStart_975720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975720 prefixEnd_975720 := by exact prefixLift 975720
  have htrace : WordTrace (prefixWord ++ tailWord_975720) baseStart_975720 baseEnd_975720 := by
    simpa [prefixWord, tailWord_975720, baseEnd_975720] using wordTrace_append hprefix tailTrace_975720
  have hstable : (prefixWord ++ tailWord_975720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975720).length < 2 ^ (prefixWord ++ tailWord_975720).sum := by decide
  have hdescent : baseEnd_975720 < baseStart_975720 := by decide
  rcases family_descends (prefixWord ++ tailWord_975720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975726 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_975726 : Nat := 118140960795 + 975726 * 2 ^ 59
def prefixEnd_975726 : Nat := 4983230072969 + 3 ^ 40 * 975726 * 2
def baseEnd_975726 : Nat := 445347933412404178877977

theorem tailTrace_975726 : CollatzResearch.WordTrace tailWord_975726 prefixEnd_975726 445347933412404178877977 := by
  unfold tailWord_975726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4448456357889852197370379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23725100575412545052642021 4448456357889852197370379)
  ·
    refine ⟨6672684536834778296055569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4448456357889852197370379 6672684536834778296055569)
    ·
      refine ⟨5004513402626083722041677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6672684536834778296055569 5004513402626083722041677)
      ·
        refine ⟨1876692525984781395765629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5004513402626083722041677 1876692525984781395765629)
        ·
          refine ⟨703759697244293023412111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1876692525984781395765629 703759697244293023412111)
          ·
            refine ⟨1055639545866439535118167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703759697244293023412111 1055639545866439535118167)
            ·
              refine ⟨1583459318799659302677251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055639545866439535118167 1583459318799659302677251)
              ·
                refine ⟨2375188978199488954015877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583459318799659302677251 2375188978199488954015877)
                ·
                  refine ⟨445347933412404178877977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2375188978199488954015877 445347933412404178877977)
                  ·
                    rfl

theorem cell20_975726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_975726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975726 prefixEnd_975726 := by exact prefixLift 975726
  have htrace : WordTrace (prefixWord ++ tailWord_975726) baseStart_975726 baseEnd_975726 := by
    simpa [prefixWord, tailWord_975726, baseEnd_975726] using wordTrace_append hprefix tailTrace_975726
  have hstable : (prefixWord ++ tailWord_975726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975726).length < 2 ^ (prefixWord ++ tailWord_975726).sum := by decide
  have hdescent : baseEnd_975726 < baseStart_975726 := by decide
  rcases family_descends (prefixWord ++ tailWord_975726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975730 : List Nat := [3, 2, 1, 2, 1, 1, 2, 6, 2]
def baseStart_975730 : Nat := 118140960795 + 975730 * 2 ^ 59
def prefixEnd_975730 : Nat := 4983230072969 + 3 ^ 40 * 975730 * 2
def baseEnd_975730 : Nat := 445349759121397942744627

theorem tailTrace_975730 : CollatzResearch.WordTrace tailWord_975730 prefixEnd_975730 445349759121397942744627 := by
  unfold tailWord_975730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8896949188776081565527161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23725197836736217508072429 8896949188776081565527161)
  ·
    refine ⟨6672711891582061174145371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8896949188776081565527161 6672711891582061174145371)
    ·
      refine ⟨10009067837373091761218057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6672711891582061174145371 10009067837373091761218057)
      ·
        refine ⟨7506800878029818820913543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10009067837373091761218057 7506800878029818820913543)
        ·
          refine ⟨11260201317044728231370315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7506800878029818820913543 11260201317044728231370315)
          ·
            refine ⟨16890301975567092347055473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11260201317044728231370315 16890301975567092347055473)
            ·
              refine ⟨12667726481675319260291605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16890301975567092347055473 12667726481675319260291605)
              ·
                refine ⟨593799678828530590326169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12667726481675319260291605 593799678828530590326169)
                ·
                  refine ⟨445349759121397942744627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593799678828530590326169 445349759121397942744627)
                  ·
                    rfl

theorem cell20_975730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_975730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975730 prefixEnd_975730 := by exact prefixLift 975730
  have htrace : WordTrace (prefixWord ++ tailWord_975730) baseStart_975730 baseEnd_975730 := by
    simpa [prefixWord, tailWord_975730, baseEnd_975730] using wordTrace_append hprefix tailTrace_975730
  have hstable : (prefixWord ++ tailWord_975730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975730).length < 2 ^ (prefixWord ++ tailWord_975730).sum := by decide
  have hdescent : baseEnd_975730 < baseStart_975730 := by decide
  rcases family_descends (prefixWord ++ tailWord_975730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975834 : List Nat := [3, 1, 1, 2, 4, 2, 7]
def baseStart_975834 : Nat := 118140960795 + 975834 * 2 ^ 59
def prefixEnd_975834 : Nat := 4983230072969 + 3 ^ 40 * 975834 * 2
def baseEnd_975834 : Nat := 49488580839470644808615

theorem tailTrace_975834 : CollatzResearch.WordTrace tailWord_975834 prefixEnd_975834 49488580839470644808615 := by
  unfold tailWord_975834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8897897486681888005973639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23727726631151701349263037 8897897486681888005973639)
  ·
    refine ⟨13346846230022832008960459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8897897486681888005973639 13346846230022832008960459)
    ·
      refine ⟨20020269345034248013440689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13346846230022832008960459 20020269345034248013440689)
      ·
        refine ⟨15015202008775686010080517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20020269345034248013440689 15015202008775686010080517)
        ·
          refine ⟨2815350376645441126890097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15015202008775686010080517 2815350376645441126890097)
          ·
            refine ⟨2111512782484080845167573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2815350376645441126890097 2111512782484080845167573)
            ·
              refine ⟨49488580839470644808615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2111512782484080845167573 49488580839470644808615)
              ·
                rfl

theorem cell20_975834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 7].length) (baseStart_975834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975834 prefixEnd_975834 := by exact prefixLift 975834
  have htrace : WordTrace (prefixWord ++ tailWord_975834) baseStart_975834 baseEnd_975834 := by
    simpa [prefixWord, tailWord_975834, baseEnd_975834] using wordTrace_append hprefix tailTrace_975834
  have hstable : (prefixWord ++ tailWord_975834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975834).length < 2 ^ (prefixWord ++ tailWord_975834).sum := by decide
  have hdescent : baseEnd_975834 < baseStart_975834 := by decide
  rcases family_descends (prefixWord ++ tailWord_975834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975837 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 3]
def baseStart_975837 : Nat := 118140960795 + 975837 * 2 ^ 59
def prefixEnd_975837 : Nat := 4983230072969 + 3 ^ 40 * 975837 * 2
def baseEnd_975837 : Nat := 445398596836981126177523

theorem tailTrace_975837 : CollatzResearch.WordTrace tailWord_975837 prefixEnd_975837 445398596836981126177523 := by
  unfold tailWord_975837
  simp only [CollatzResearch.WordTrace]
  refine ⟨35591699365716683536253765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23727799577144455690835843 35591699365716683536253765)
  ·
    refine ⟨6673443631071878163047581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35591699365716683536253765 6673443631071878163047581)
    ·
      refine ⟨2502541361651954311142843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6673443631071878163047581 2502541361651954311142843)
      ·
        refine ⟨3753812042477931466714265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2502541361651954311142843 3753812042477931466714265)
        ·
          refine ⟨2815359031858448600035699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3753812042477931466714265 2815359031858448600035699)
          ·
            refine ⟨4223038547787672900053549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815359031858448600035699 4223038547787672900053549)
            ·
              refine ⟨1583639455420377337520081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4223038547787672900053549 1583639455420377337520081)
              ·
                refine ⟨1187729591565283003140061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583639455420377337520081 1187729591565283003140061)
                ·
                  refine ⟨445398596836981126177523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187729591565283003140061 445398596836981126177523)
                  ·
                    rfl

theorem cell20_975837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_975837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975837 prefixEnd_975837 := by exact prefixLift 975837
  have htrace : WordTrace (prefixWord ++ tailWord_975837) baseStart_975837 baseEnd_975837 := by
    simpa [prefixWord, tailWord_975837, baseEnd_975837] using wordTrace_append hprefix tailTrace_975837
  have hstable : (prefixWord ++ tailWord_975837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975837).length < 2 ^ (prefixWord ++ tailWord_975837).sum := by decide
  have hdescent : baseEnd_975837 < baseStart_975837 := by decide
  rcases family_descends (prefixWord ++ tailWord_975837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975854 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_975854 : Nat := 118140960795 + 975854 * 2 ^ 59
def prefixEnd_975854 : Nat := 4983230072969 + 3 ^ 40 * 975854 * 2
def baseEnd_975854 : Nat := 445406356100204622610787

theorem tailTrace_975854 : CollatzResearch.WordTrace tailWord_975854 prefixEnd_975854 445406356100204622610787 := by
  unfold tailWord_975854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4449039925831886929952827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23728212937770063626415077 4449039925831886929952827)
  ·
    refine ⟨6673559888747830394929241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4449039925831886929952827 6673559888747830394929241)
    ·
      refine ⟨5005169916560872796196931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6673559888747830394929241 5005169916560872796196931)
      ·
        refine ⟨7507754874841309194295397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5005169916560872796196931 7507754874841309194295397)
        ·
          refine ⟨1407704039032745473930387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7507754874841309194295397 1407704039032745473930387)
          ·
            refine ⟨2111556058549118210895581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407704039032745473930387 2111556058549118210895581)
            ·
              refine ⟨791833521955919329085843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2111556058549118210895581 791833521955919329085843)
              ·
                refine ⟨1187750282933878993628765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791833521955919329085843 1187750282933878993628765)
                ·
                  refine ⟨445406356100204622610787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187750282933878993628765 445406356100204622610787)
                  ·
                    rfl

theorem cell20_975854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_975854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975854 prefixEnd_975854 := by exact prefixLift 975854
  have htrace : WordTrace (prefixWord ++ tailWord_975854) baseStart_975854 baseEnd_975854 := by
    simpa [prefixWord, tailWord_975854, baseEnd_975854] using wordTrace_append hprefix tailTrace_975854
  have hstable : (prefixWord ++ tailWord_975854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975854).length < 2 ^ (prefixWord ++ tailWord_975854).sum := by decide
  have hdescent : baseEnd_975854 < baseStart_975854 := by decide
  rcases family_descends (prefixWord ++ tailWord_975854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975860 : List Nat := [2, 6, 2, 1, 2, 1, 2, 4]
def baseStart_975860 : Nat := 118140960795 + 975860 * 2 ^ 59
def prefixEnd_975860 : Nat := 4983230072969 + 3 ^ 40 * 975860 * 2
def baseEnd_975860 : Nat := 148469698221231756136921

theorem tailTrace_975860 : CollatzResearch.WordTrace tailWord_975860 prefixEnd_975860 148469698221231756136921 := by
  unfold tailWord_975860
  simp only [CollatzResearch.WordTrace]
  refine ⟨17796269122316679232170517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23728358829755572309560689 17796269122316679232170517)
  ·
    refine ⟨834200115108594339007993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17796269122316679232170517 834200115108594339007993)
    ·
      refine ⟨625650086331445754255995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 834200115108594339007993 625650086331445754255995)
      ·
        refine ⟨938475129497168631383993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625650086331445754255995 938475129497168631383993)
        ·
          refine ⟨703856347122876473537995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938475129497168631383993 703856347122876473537995)
          ·
            refine ⟨1055784520684314710306993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703856347122876473537995 1055784520684314710306993)
            ·
              refine ⟨791838390513236032730245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055784520684314710306993 791838390513236032730245)
              ·
                refine ⟨148469698221231756136921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 791838390513236032730245 148469698221231756136921)
                ·
                  rfl

theorem cell20_975860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_975860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975860 prefixEnd_975860 := by exact prefixLift 975860
  have htrace : WordTrace (prefixWord ++ tailWord_975860) baseStart_975860 baseEnd_975860 := by
    simpa [prefixWord, tailWord_975860, baseEnd_975860] using wordTrace_append hprefix tailTrace_975860
  have hstable : (prefixWord ++ tailWord_975860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975860).length < 2 ^ (prefixWord ++ tailWord_975860).sum := by decide
  have hdescent : baseEnd_975860 < baseStart_975860 := by decide
  rcases family_descends (prefixWord ++ tailWord_975860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975874 : List Nat := [3, 4, 1, 3, 2, 1, 1, 3, 2]
def baseStart_975874 : Nat := 118140960795 + 975874 * 2 ^ 59
def prefixEnd_975874 : Nat := 4983230072969 + 3 ^ 40 * 975874 * 2
def baseEnd_975874 : Nat := 445415484645173441944039

theorem tailTrace_975874 : CollatzResearch.WordTrace tailWord_975874 prefixEnd_975874 445415484645173441944039 := by
  unfold tailWord_975874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8898262216645659713837669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23728699244388425903567117 8898262216645659713837669)
  ·
    refine ⟨1668424165621061196344563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8898262216645659713837669 1668424165621061196344563)
    ·
      refine ⟨2502636248431591794516845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1668424165621061196344563 2502636248431591794516845)
      ·
        refine ⟨938488593161846922943817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2502636248431591794516845 938488593161846922943817)
        ·
          refine ⟨703866444871385192207863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938488593161846922943817 703866444871385192207863)
          ·
            refine ⟨1055799667307077788311795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703866444871385192207863 1055799667307077788311795)
            ·
              refine ⟨1583699500960616682467693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055799667307077788311795 1583699500960616682467693)
              ·
                refine ⟨593887312860231255925385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1583699500960616682467693 593887312860231255925385)
                ·
                  refine ⟨445415484645173441944039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593887312860231255925385 445415484645173441944039)
                  ·
                    rfl

theorem cell20_975874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_975874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975874 prefixEnd_975874 := by exact prefixLift 975874
  have htrace : WordTrace (prefixWord ++ tailWord_975874) baseStart_975874 baseEnd_975874 := by
    simpa [prefixWord, tailWord_975874, baseEnd_975874] using wordTrace_append hprefix tailTrace_975874
  have hstable : (prefixWord ++ tailWord_975874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975874).length < 2 ^ (prefixWord ++ tailWord_975874).sum := by decide
  have hdescent : baseEnd_975874 < baseStart_975874 := by decide
  rcases family_descends (prefixWord ++ tailWord_975874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975879 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 7]
def baseStart_975879 : Nat := 118140960795 + 975879 * 2 ^ 59
def prefixEnd_975879 : Nat := 4983230072969 + 3 ^ 40 * 975879 * 2
def baseEnd_975879 : Nat := 445417766781415646777351

theorem tailTrace_975879 : CollatzResearch.WordTrace tailWord_975879 prefixEnd_975879 445417766781415646777351 := by
  unfold tailWord_975879
  simp only [CollatzResearch.WordTrace]
  refine ⟨35593231231564524709282691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23728820821043016472855127 35593231231564524709282691)
  ·
    refine ⟨53389846847346787063924037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35593231231564524709282691 53389846847346787063924037)
    ·
      refine ⟨10010596283877522574485757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53389846847346787063924037 10010596283877522574485757)
      ·
        refine ⟨3753973606454070965432159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10010596283877522574485757 3753973606454070965432159)
        ·
          refine ⟨5630960409681106448148239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3753973606454070965432159 5630960409681106448148239)
          ·
            refine ⟨8446440614521659672222359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5630960409681106448148239 8446440614521659672222359)
            ·
              refine ⟨12669660921782489508333539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8446440614521659672222359 12669660921782489508333539)
              ·
                refine ⟨19004491382673734262500309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12669660921782489508333539 19004491382673734262500309)
                ·
                  refine ⟨445417766781415646777351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19004491382673734262500309 445417766781415646777351)
                  ·
                    rfl

theorem cell20_975879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_975879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975879 prefixEnd_975879 := by exact prefixLift 975879
  have htrace : WordTrace (prefixWord ++ tailWord_975879) baseStart_975879 baseEnd_975879 := by
    simpa [prefixWord, tailWord_975879, baseEnd_975879] using wordTrace_append hprefix tailTrace_975879
  have hstable : (prefixWord ++ tailWord_975879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975879).length < 2 ^ (prefixWord ++ tailWord_975879).sum := by decide
  have hdescent : baseEnd_975879 < baseStart_975879 := by decide
  rcases family_descends (prefixWord ++ tailWord_975879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975903 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 4]
def baseStart_975903 : Nat := 118140960795 + 975903 * 2 ^ 59
def prefixEnd_975903 : Nat := 4983230072969 + 3 ^ 40 * 975903 * 2
def baseEnd_975903 : Nat := 445428721035378229977253

theorem tailTrace_975903 : CollatzResearch.WordTrace tailWord_975903 prefixEnd_975903 445428721035378229977253 := by
  unfold tailWord_975903
  simp only [CollatzResearch.WordTrace]
  refine ⟨35594106583477576808156363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23729404388985051205437575 35594106583477576808156363)
  ·
    refine ⟨53391159875216365212234545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35594106583477576808156363 53391159875216365212234545)
    ·
      refine ⟨40043369906412273909175909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53391159875216365212234545 40043369906412273909175909)
      ·
        refine ⟨7508131857452301357970483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40043369906412273909175909 7508131857452301357970483)
        ·
          refine ⟨11262197786178452036955725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7508131857452301357970483 11262197786178452036955725)
          ·
            refine ⟨4223324169816919513858397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11262197786178452036955725 4223324169816919513858397)
            ·
              refine ⟨1583746563681344817696899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4223324169816919513858397 1583746563681344817696899)
              ·
                refine ⟨2375619845522017226545349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583746563681344817696899 2375619845522017226545349)
                ·
                  refine ⟨445428721035378229977253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2375619845522017226545349 445428721035378229977253)
                  ·
                    rfl

theorem cell20_975903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_975903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975903 prefixEnd_975903 := by exact prefixLift 975903
  have htrace : WordTrace (prefixWord ++ tailWord_975903) baseStart_975903 baseEnd_975903 := by
    simpa [prefixWord, tailWord_975903, baseEnd_975903] using wordTrace_append hprefix tailTrace_975903
  have hstable : (prefixWord ++ tailWord_975903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975903).length < 2 ^ (prefixWord ++ tailWord_975903).sum := by decide
  have hdescent : baseEnd_975903 < baseStart_975903 := by decide
  rcases family_descends (prefixWord ++ tailWord_975903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975954 : List Nat := [3, 2, 2, 1, 3, 3, 2, 2, 2]
def baseStart_975954 : Nat := 118140960795 + 975954 * 2 ^ 59
def prefixEnd_975954 : Nat := 4983230072969 + 3 ^ 40 * 975954 * 2
def baseEnd_975954 : Nat := 445451998825048719277045

theorem tailTrace_975954 : CollatzResearch.WordTrace tailWord_975954 prefixEnd_975954 445451998825048719277045 := by
  unfold tailWord_975954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8898991676573203129565729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23730644470861875012175277 8898991676573203129565729)
  ·
    refine ⟨6674243757429902347174297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8898991676573203129565729 6674243757429902347174297)
    ·
      refine ⟨5005682818072426760380723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6674243757429902347174297 5005682818072426760380723)
      ·
        refine ⟨7508524227108640140571085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5005682818072426760380723 7508524227108640140571085)
        ·
          refine ⟨2815696585165740052714157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7508524227108640140571085 2815696585165740052714157)
          ·
            refine ⟨1055886219437152519767809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2815696585165740052714157 1055886219437152519767809)
            ·
              refine ⟨791914664577864389825857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1055886219437152519767809 791914664577864389825857)
              ·
                refine ⟨593935998433398292369393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791914664577864389825857 593935998433398292369393)
                ·
                  refine ⟨445451998825048719277045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593935998433398292369393 445451998825048719277045)
                  ·
                    rfl

theorem cell20_975954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_975954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975954 prefixEnd_975954 := by exact prefixLift 975954
  have htrace : WordTrace (prefixWord ++ tailWord_975954) baseStart_975954 baseEnd_975954 := by
    simpa [prefixWord, tailWord_975954, baseEnd_975954] using wordTrace_append hprefix tailTrace_975954
  have hstable : (prefixWord ++ tailWord_975954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975954).length < 2 ^ (prefixWord ++ tailWord_975954).sum := by decide
  have hdescent : baseEnd_975954 < baseStart_975954 := by decide
  rcases family_descends (prefixWord ++ tailWord_975954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975955 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 3]
def baseStart_975955 : Nat := 118140960795 + 975955 * 2 ^ 59
def prefixEnd_975955 : Nat := 4983230072969 + 3 ^ 40 * 975955 * 2
def baseEnd_975955 : Nat := 445452455252297160243707

theorem tailTrace_975955 : CollatzResearch.WordTrace tailWord_975955 prefixEnd_975955 445452455252297160243707 := by
  unfold tailWord_975955
  simp only [CollatzResearch.WordTrace]
  refine ⟨35596003179289189689049319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23730668786192793126032879 35596003179289189689049319)
  ·
    refine ⟨53394004768933784533573979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35596003179289189689049319 53394004768933784533573979)
    ·
      refine ⟨80091007153400676800360969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53394004768933784533573979 80091007153400676800360969)
      ·
        refine ⟨60068255365050507600270727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80091007153400676800360969 60068255365050507600270727)
        ·
          refine ⟨90102383047575761400406091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60068255365050507600270727 90102383047575761400406091)
          ·
            refine ⟨135153574571363642100609137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90102383047575761400406091 135153574571363642100609137)
            ·
              refine ⟨101365180928522731575456853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135153574571363642100609137 101365180928522731575456853)
              ·
                refine ⟨1187873214006125760649885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 101365180928522731575456853 1187873214006125760649885)
                ·
                  refine ⟨445452455252297160243707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1187873214006125760649885 445452455252297160243707)
                  ·
                    rfl

theorem cell20_975955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 3].length) (baseStart_975955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975955 prefixEnd_975955 := by exact prefixLift 975955
  have htrace : WordTrace (prefixWord ++ tailWord_975955) baseStart_975955 baseEnd_975955 := by
    simpa [prefixWord, tailWord_975955, baseEnd_975955] using wordTrace_append hprefix tailTrace_975955
  have hstable : (prefixWord ++ tailWord_975955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975955).length < 2 ^ (prefixWord ++ tailWord_975955).sum := by decide
  have hdescent : baseEnd_975955 < baseStart_975955 := by decide
  rcases family_descends (prefixWord ++ tailWord_975955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_975996 : List Nat := [2, 2, 2, 1, 1, 3, 4, 3, 2]
def baseStart_975996 : Nat := 118140960795 + 975996 * 2 ^ 59
def prefixEnd_975996 : Nat := 4983230072969 + 3 ^ 40 * 975996 * 2
def baseEnd_975996 : Nat := 445471168769483239876873

theorem tailTrace_975996 : CollatzResearch.WordTrace tailWord_975996 prefixEnd_975996 445471168769483239876873 := by
  unfold tailWord_975996
  simp only [CollatzResearch.WordTrace]
  refine ⟨17798749286070326845645921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23731665714760435794194561 17798749286070326845645921)
  ·
    refine ⟨13349061964552745134234441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17798749286070326845645921 13349061964552745134234441)
    ·
      refine ⟨10011796473414558850675831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13349061964552745134234441 10011796473414558850675831)
      ·
        refine ⟨15017694710121838276013747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10011796473414558850675831 15017694710121838276013747)
        ·
          refine ⟨22526542065182757414020621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15017694710121838276013747 22526542065182757414020621)
          ·
            refine ⟨8447453274443534030257733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22526542065182757414020621 8447453274443534030257733)
            ·
              refine ⟨1583897488958162630673325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8447453274443534030257733 1583897488958162630673325)
              ·
                refine ⟨593961558359310986502497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1583897488958162630673325 593961558359310986502497)
                ·
                  refine ⟨445471168769483239876873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 593961558359310986502497 445471168769483239876873)
                  ·
                    rfl

theorem cell20_975996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_975996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_975996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_975996 prefixEnd_975996 := by exact prefixLift 975996
  have htrace : WordTrace (prefixWord ++ tailWord_975996) baseStart_975996 baseEnd_975996 := by
    simpa [prefixWord, tailWord_975996, baseEnd_975996] using wordTrace_append hprefix tailTrace_975996
  have hstable : (prefixWord ++ tailWord_975996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_975996).length < 2 ^ (prefixWord ++ tailWord_975996).sum := by decide
  have hdescent : baseEnd_975996 < baseStart_975996 := by decide
  rcases family_descends (prefixWord ++ tailWord_975996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976062 : List Nat := [4, 2, 1, 1, 3, 1, 8]
def baseStart_976062 : Nat := 118140960795 + 976062 * 2 ^ 59
def prefixEnd_976062 : Nat := 4983230072969 + 3 ^ 40 * 976062 * 2
def baseEnd_976062 : Nat := 49500143663097815964067

theorem tailTrace_976062 : CollatzResearch.WordTrace tailWord_976062 prefixEnd_976062 49500143663097815964067 := by
  unfold tailWord_976062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4449988223737693370399305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23733270526601031308796293 4449988223737693370399305)
  ·
    refine ⟨3337491167803270027799479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4449988223737693370399305 3337491167803270027799479)
    ·
      refine ⟨5006236751704905041699219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3337491167803270027799479 5006236751704905041699219)
      ·
        refine ⟨7509355127557357562548829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5006236751704905041699219 7509355127557357562548829)
        ·
          refine ⟨2816008172834009085955811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7509355127557357562548829 2816008172834009085955811)
          ·
            refine ⟨4224012259251013628933717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816008172834009085955811 4224012259251013628933717)
            ·
              refine ⟨49500143663097815964067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4224012259251013628933717 49500143663097815964067)
              ·
                rfl

theorem cell20_976062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 8].length) (baseStart_976062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976062 prefixEnd_976062 := by exact prefixLift 976062
  have htrace : WordTrace (prefixWord ++ tailWord_976062) baseStart_976062 baseEnd_976062 := by
    simpa [prefixWord, tailWord_976062, baseEnd_976062] using wordTrace_append hprefix tailTrace_976062
  have hstable : (prefixWord ++ tailWord_976062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976062).length < 2 ^ (prefixWord ++ tailWord_976062).sum := by decide
  have hdescent : baseEnd_976062 < baseStart_976062 := by decide
  rcases family_descends (prefixWord ++ tailWord_976062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976068 : List Nat := [2, 3, 3, 1, 3, 1, 3, 2, 2]
def baseStart_976068 : Nat := 118140960795 + 976068 * 2 ^ 59
def prefixEnd_976068 : Nat := 4983230072969 + 3 ^ 40 * 976068 * 2
def baseEnd_976068 : Nat := 445504031531370989476579

theorem tailTrace_976068 : CollatzResearch.WordTrace tailWord_976068 prefixEnd_976068 445504031531370989476579 := by
  unfold tailWord_976068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17800062313939904993956429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23733416418586539991941905 17800062313939904993956429)
  ·
    refine ⟨6675023367727464372733661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17800062313939904993956429 6675023367727464372733661)
    ·
      refine ⟨2503133762897799139775123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6675023367727464372733661 2503133762897799139775123)
      ·
        refine ⟨3754700644346698709662685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503133762897799139775123 3754700644346698709662685)
        ·
          refine ⟨1408012741630012016123507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3754700644346698709662685 1408012741630012016123507)
          ·
            refine ⟨2112019112445018024185261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408012741630012016123507 2112019112445018024185261)
            ·
              refine ⟨792007167166881759069473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2112019112445018024185261 792007167166881759069473)
              ·
                refine ⟨594005375375161319302105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792007167166881759069473 594005375375161319302105)
                ·
                  refine ⟨445504031531370989476579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594005375375161319302105 445504031531370989476579)
                  ·
                    rfl

theorem cell20_976068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_976068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976068 prefixEnd_976068 := by exact prefixLift 976068
  have htrace : WordTrace (prefixWord ++ tailWord_976068) baseStart_976068 baseEnd_976068 := by
    simpa [prefixWord, tailWord_976068, baseEnd_976068] using wordTrace_append hprefix tailTrace_976068
  have hstable : (prefixWord ++ tailWord_976068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976068).length < 2 ^ (prefixWord ++ tailWord_976068).sum := by decide
  have hdescent : baseEnd_976068 < baseStart_976068 := by decide
  rcases family_descends (prefixWord ++ tailWord_976068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976069 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 3]
def baseStart_976069 : Nat := 118140960795 + 976069 * 2 ^ 59
def prefixEnd_976069 : Nat := 4983230072969 + 3 ^ 40 * 976069 * 2
def baseEnd_976069 : Nat := 445504487958619430443241

theorem tailTrace_976069 : CollatzResearch.WordTrace tailWord_976069 prefixEnd_976069 445504487958619430443241 := by
  unfold tailWord_976069
  simp only [CollatzResearch.WordTrace]
  refine ⟨35600161100876187158699261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23733440733917458105799507 35600161100876187158699261)
  ·
    refine ⟨13350060412828570184512223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35600161100876187158699261 13350060412828570184512223)
    ·
      refine ⟨20025090619242855276768335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13350060412828570184512223 20025090619242855276768335)
      ·
        refine ⟨30037635928864282915152503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20025090619242855276768335 30037635928864282915152503)
        ·
          refine ⟨45056453893296424372728755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30037635928864282915152503 45056453893296424372728755)
          ·
            refine ⟨67584680839944636559093133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45056453893296424372728755 67584680839944636559093133)
            ·
              refine ⟨25344255314979238709659925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67584680839944636559093133 25344255314979238709659925)
              ·
                refine ⟨1188011967889651814515309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25344255314979238709659925 1188011967889651814515309)
                ·
                  refine ⟨445504487958619430443241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188011967889651814515309 445504487958619430443241)
                  ·
                    rfl

theorem cell20_976069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_976069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976069 prefixEnd_976069 := by exact prefixLift 976069
  have htrace : WordTrace (prefixWord ++ tailWord_976069) baseStart_976069 baseEnd_976069 := by
    simpa [prefixWord, tailWord_976069, baseEnd_976069] using wordTrace_append hprefix tailTrace_976069
  have hstable : (prefixWord ++ tailWord_976069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976069).length < 2 ^ (prefixWord ++ tailWord_976069).sum := by decide
  have hdescent : baseEnd_976069 < baseStart_976069 := by decide
  rcases family_descends (prefixWord ++ tailWord_976069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976127 : List Nat := [1, 1, 2, 2, 1, 7, 2, 2, 2]
def baseStart_976127 : Nat := 118140960795 + 976127 * 2 ^ 59
def prefixEnd_976127 : Nat := 4983230072969 + 3 ^ 40 * 976127 * 2
def baseEnd_976127 : Nat := 445530960739029006509671

theorem tailTrace_976127 : CollatzResearch.WordTrace tailWord_976127 prefixEnd_976127 445530960739029006509671 := by
  unfold tailWord_976127
  simp only [CollatzResearch.WordTrace]
  refine ⟨35602276534666063064310635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23734851023110708709540423 35602276534666063064310635)
  ·
    refine ⟨53403414801999094596465953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35602276534666063064310635 53403414801999094596465953)
    ·
      refine ⟨40052561101499320947349465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53403414801999094596465953 40052561101499320947349465)
      ·
        refine ⟨30039420826124490710512099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40052561101499320947349465 30039420826124490710512099)
        ·
          refine ⟨45059131239186736065768149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30039420826124490710512099 45059131239186736065768149)
          ·
            refine ⟨1056073388418439126541441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45059131239186736065768149 1056073388418439126541441)
            ·
              refine ⟨792055041313829344906081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056073388418439126541441 792055041313829344906081)
              ·
                refine ⟨594041280985372008679561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792055041313829344906081 594041280985372008679561)
                ·
                  refine ⟨445530960739029006509671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594041280985372008679561 445530960739029006509671)
                  ·
                    rfl

theorem cell20_976127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 2].length) (baseStart_976127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976127 prefixEnd_976127 := by exact prefixLift 976127
  have htrace : WordTrace (prefixWord ++ tailWord_976127) baseStart_976127 baseEnd_976127 := by
    simpa [prefixWord, tailWord_976127, baseEnd_976127] using wordTrace_append hprefix tailTrace_976127
  have hstable : (prefixWord ++ tailWord_976127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976127).length < 2 ^ (prefixWord ++ tailWord_976127).sum := by decide
  have hdescent : baseEnd_976127 < baseStart_976127 := by decide
  rcases family_descends (prefixWord ++ tailWord_976127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976145 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 3]
def baseStart_976145 : Nat := 118140960795 + 976145 * 2 ^ 59
def prefixEnd_976145 : Nat := 4983230072969 + 3 ^ 40 * 976145 * 2
def baseEnd_976145 : Nat := 445539176429500943909597

theorem tailTrace_976145 : CollatzResearch.WordTrace tailWord_976145 prefixEnd_976145 445539176429500943909597 := by
  unfold tailWord_976145
  simp only [CollatzResearch.WordTrace]
  refine ⟨35602933048600852138465889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23735288699067234758977259 35602933048600852138465889)
  ·
    refine ⟨26702199786450639103849417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35602933048600852138465889 26702199786450639103849417)
    ·
      refine ⟨20026649839837979327887063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26702199786450639103849417 20026649839837979327887063)
      ·
        refine ⟨30039974759756968991830595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20026649839837979327887063 30039974759756968991830595)
        ·
          refine ⟨45059962139635453487745893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30039974759756968991830595 45059962139635453487745893)
          ·
            refine ⟨8448742901181647528952355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45059962139635453487745893 8448742901181647528952355)
            ·
              refine ⟨12673114351772471293428533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8448742901181647528952355 12673114351772471293428533)
              ·
                refine ⟨1188104470478669183758925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12673114351772471293428533 1188104470478669183758925)
                ·
                  refine ⟨445539176429500943909597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188104470478669183758925 445539176429500943909597)
                  ·
                    rfl

theorem cell20_976145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_976145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976145 prefixEnd_976145 := by exact prefixLift 976145
  have htrace : WordTrace (prefixWord ++ tailWord_976145) baseStart_976145 baseEnd_976145 := by
    simpa [prefixWord, tailWord_976145, baseEnd_976145] using wordTrace_append hprefix tailTrace_976145
  have hstable : (prefixWord ++ tailWord_976145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976145).length < 2 ^ (prefixWord ++ tailWord_976145).sum := by decide
  have hdescent : baseEnd_976145 < baseStart_976145 := by decide
  rcases family_descends (prefixWord ++ tailWord_976145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976152 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_976152 : Nat := 118140960795 + 976152 * 2 ^ 59
def prefixEnd_976152 : Nat := 4983230072969 + 3 ^ 40 * 976152 * 2
def baseEnd_976152 : Nat := 445542371420240030676235

theorem tailTrace_976152 : CollatzResearch.WordTrace tailWord_976152 prefixEnd_976152 445542371420240030676235 := by
  unfold tailWord_976152
  simp only [CollatzResearch.WordTrace]
  refine ⟨17801594179787746166985355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23735458906383661555980473 17801594179787746166985355)
  ·
    refine ⟨26702391269681619250478033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17801594179787746166985355 26702391269681619250478033)
    ·
      refine ⟨20026793452261214437858525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26702391269681619250478033 20026793452261214437858525)
      ·
        refine ⟨7510047544597955414196947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20026793452261214437858525 7510047544597955414196947)
        ·
          refine ⟨11265071316896933121295421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7510047544597955414196947 11265071316896933121295421)
          ·
            refine ⟨4224401743836349920485783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11265071316896933121295421 4224401743836349920485783)
            ·
              refine ⟨6336602615754524880728675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224401743836349920485783 6336602615754524880728675)
              ·
                refine ⟨9504903923631787321093013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6336602615754524880728675 9504903923631787321093013)
                ·
                  refine ⟨445542371420240030676235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9504903923631787321093013 445542371420240030676235)
                  ·
                    rfl

theorem cell20_976152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_976152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976152 prefixEnd_976152 := by exact prefixLift 976152
  have htrace : WordTrace (prefixWord ++ tailWord_976152) baseStart_976152 baseEnd_976152 := by
    simpa [prefixWord, tailWord_976152, baseEnd_976152] using wordTrace_append hprefix tailTrace_976152
  have hstable : (prefixWord ++ tailWord_976152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976152).length < 2 ^ (prefixWord ++ tailWord_976152).sum := by decide
  have hdescent : baseEnd_976152 < baseStart_976152 := by decide
  rcases family_descends (prefixWord ++ tailWord_976152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976196 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 3]
def baseStart_976196 : Nat := 118140960795 + 976196 * 2 ^ 59
def prefixEnd_976196 : Nat := 4983230072969 + 3 ^ 40 * 976196 * 2
def baseEnd_976196 : Nat := 445562454219171433209389

theorem tailTrace_976196 : CollatzResearch.WordTrace tailWord_976196 prefixEnd_976196 445562454219171433209389 := by
  unfold tailWord_976196
  simp only [CollatzResearch.WordTrace]
  refine ⟨17802396585708043924286221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23736528780944058565714961 17802396585708043924286221)
  ·
    refine ⟨6675898719640516471607333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17802396585708043924286221 6675898719640516471607333)
    ·
      refine ⟨1251731009932596838426375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6675898719640516471607333 1251731009932596838426375)
      ·
        refine ⟨1877596514898895257639563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251731009932596838426375 1877596514898895257639563)
        ·
          refine ⟨2816394772348342886459345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877596514898895257639563 2816394772348342886459345)
          ·
            refine ⟨2112296079261257164844509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2816394772348342886459345 2112296079261257164844509)
            ·
              refine ⟨792111029722971436816691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2112296079261257164844509 792111029722971436816691)
              ·
                refine ⟨1188166544584457155225037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792111029722971436816691 1188166544584457155225037)
                ·
                  refine ⟨445562454219171433209389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188166544584457155225037 445562454219171433209389)
                  ·
                    rfl

theorem cell20_976196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_976196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976196 prefixEnd_976196 := by exact prefixLift 976196
  have htrace : WordTrace (prefixWord ++ tailWord_976196) baseStart_976196 baseEnd_976196 := by
    simpa [prefixWord, tailWord_976196, baseEnd_976196] using wordTrace_append hprefix tailTrace_976196
  have hstable : (prefixWord ++ tailWord_976196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976196).length < 2 ^ (prefixWord ++ tailWord_976196).sum := by decide
  have hdescent : baseEnd_976196 < baseStart_976196 := by decide
  rcases family_descends (prefixWord ++ tailWord_976196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976224 : List Nat := [2, 1, 1, 3, 4, 1, 3, 3, 2]
def baseStart_976224 : Nat := 118140960795 + 976224 * 2 ^ 59
def prefixEnd_976224 : Nat := 4983230072969 + 3 ^ 40 * 976224 * 2
def baseEnd_976224 : Nat := 445575234182127780275941

theorem tailTrace_976224 : CollatzResearch.WordTrace tailWord_976224 prefixEnd_976224 445575234182127780275941 := by
  unfold tailWord_976224
  simp only [CollatzResearch.WordTrace]
  refine ⟨17802907207657324315295863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23737209610209765753727817 17802907207657324315295863)
  ·
    refine ⟨26704360811485986472943795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17802907207657324315295863 26704360811485986472943795)
    ·
      refine ⟨40056541217228979709415693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26704360811485986472943795 40056541217228979709415693)
      ·
        refine ⟨15021202956460867391030885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40056541217228979709415693 15021202956460867391030885)
        ·
          refine ⟨2816475554336412635818291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15021202956460867391030885 2816475554336412635818291)
          ·
            refine ⟨4224713331504618953727437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816475554336412635818291 4224713331504618953727437)
            ·
              refine ⟨1584267499314232107647789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4224713331504618953727437 1584267499314232107647789)
              ·
                refine ⟨594100312242837040367921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1584267499314232107647789 594100312242837040367921)
                ·
                  refine ⟨445575234182127780275941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594100312242837040367921 445575234182127780275941)
                  ·
                    rfl

theorem cell20_976224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 2].length) (baseStart_976224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976224 prefixEnd_976224 := by exact prefixLift 976224
  have htrace : WordTrace (prefixWord ++ tailWord_976224) baseStart_976224 baseEnd_976224 := by
    simpa [prefixWord, tailWord_976224, baseEnd_976224] using wordTrace_append hprefix tailTrace_976224
  have hstable : (prefixWord ++ tailWord_976224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976224).length < 2 ^ (prefixWord ++ tailWord_976224).sum := by decide
  have hdescent : baseEnd_976224 < baseStart_976224 := by decide
  rcases family_descends (prefixWord ++ tailWord_976224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976231 : List Nat := [1, 1, 5, 1, 5, 1, 6]
def baseStart_976231 : Nat := 118140960795 + 976231 * 2 ^ 59
def prefixEnd_976231 : Nat := 4983230072969 + 3 ^ 40 * 976231 * 2
def baseEnd_976231 : Nat := 49508714352540763004731

theorem tailTrace_976231 : CollatzResearch.WordTrace tailWord_976231 prefixEnd_976231 49508714352540763004731 := by
  unfold tailWord_976231
  simp only [CollatzResearch.WordTrace]
  refine ⟨35606069726289288826096547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23737379817526192550731031 35606069726289288826096547)
  ·
    refine ⟨53409104589433933239144821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35606069726289288826096547 53409104589433933239144821)
    ·
      refine ⟨5007103555259431241169827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53409104589433933239144821 5007103555259431241169827)
      ·
        refine ⟨7510655332889146861754741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5007103555259431241169827 7510655332889146861754741)
        ·
          refine ⟨704123937458357518289507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7510655332889146861754741 704123937458357518289507)
          ·
            refine ⟨1056185906187536277434261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704123937458357518289507 1056185906187536277434261)
            ·
              refine ⟨49508714352540763004731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1056185906187536277434261 49508714352540763004731)
              ·
                rfl

theorem cell20_976231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 6].length) (baseStart_976231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976231 prefixEnd_976231 := by exact prefixLift 976231
  have htrace : WordTrace (prefixWord ++ tailWord_976231) baseStart_976231 baseEnd_976231 := by
    simpa [prefixWord, tailWord_976231, baseEnd_976231] using wordTrace_append hprefix tailTrace_976231
  have hstable : (prefixWord ++ tailWord_976231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976231).length < 2 ^ (prefixWord ++ tailWord_976231).sum := by decide
  have hdescent : baseEnd_976231 < baseStart_976231 := by decide
  rcases family_descends (prefixWord ++ tailWord_976231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976300 : List Nat := [2, 2, 1, 1, 1, 1, 8, 2, 2]
def baseStart_976300 : Nat := 118140960795 + 976300 * 2 ^ 59
def prefixEnd_976300 : Nat := 4983230072969 + 3 ^ 40 * 976300 * 2
def baseEnd_976300 : Nat := 445609922653009293742297

theorem tailTrace_976300 : CollatzResearch.WordTrace tailWord_976300 prefixEnd_976300 445609922653009293742297 := by
  unfold tailWord_976300
  simp only [CollatzResearch.WordTrace]
  refine ⟨17804293181519656805179177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23739057575359542406905569 17804293181519656805179177)
  ·
    refine ⟨13353219886139742603884383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17804293181519656805179177 13353219886139742603884383)
    ·
      refine ⟨20029829829209613905826575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13353219886139742603884383 20029829829209613905826575)
      ·
        refine ⟨30044744743814420858739863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20029829829209613905826575 30044744743814420858739863)
        ·
          refine ⟨45067117115721631288109795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30044744743814420858739863 45067117115721631288109795)
          ·
            refine ⟨67600675673582446932164693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45067117115721631288109795 67600675673582446932164693)
            ·
              refine ⟨792195418049794299986305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 67600675673582446932164693 792195418049794299986305)
              ·
                refine ⟨594146563537345724989729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792195418049794299986305 594146563537345724989729)
                ·
                  refine ⟨445609922653009293742297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594146563537345724989729 445609922653009293742297)
                  ·
                    rfl

theorem cell20_976300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_976300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976300 prefixEnd_976300 := by exact prefixLift 976300
  have htrace : WordTrace (prefixWord ++ tailWord_976300) baseStart_976300 baseEnd_976300 := by
    simpa [prefixWord, tailWord_976300, baseEnd_976300] using wordTrace_append hprefix tailTrace_976300
  have hstable : (prefixWord ++ tailWord_976300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976300).length < 2 ^ (prefixWord ++ tailWord_976300).sum := by decide
  have hdescent : baseEnd_976300 < baseStart_976300 := by decide
  rcases family_descends (prefixWord ++ tailWord_976300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976328 : List Nat := [2, 1, 3, 1, 3, 1, 5, 4]
def baseStart_976328 : Nat := 118140960795 + 976328 * 2 ^ 59
def prefixEnd_976328 : Nat := 4983230072969 + 3 ^ 40 * 976328 * 2
def baseEnd_976328 : Nat := 148540900871988546936283

theorem tailTrace_976328 : CollatzResearch.WordTrace tailWord_976328 prefixEnd_976328 148540900871988546936283 := by
  unfold tailWord_976328
  simp only [CollatzResearch.WordTrace]
  refine ⟨17804803803468937196188819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23739738404625249594918425 17804803803468937196188819)
  ·
    refine ⟨26707205705203405794283229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17804803803468937196188819 26707205705203405794283229)
    ·
      refine ⟨10015202139451277172856211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26707205705203405794283229 10015202139451277172856211)
      ·
        refine ⟨15022803209176915759284317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10015202139451277172856211 15022803209176915759284317)
        ·
          refine ⟨5633551203441343409731619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15022803209176915759284317 5633551203441343409731619)
          ·
            refine ⟨8450326805162015114597429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633551203441343409731619 8450326805162015114597429)
            ·
              refine ⟨792218137983938916993509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8450326805162015114597429 792218137983938916993509)
              ·
                refine ⟨148540900871988546936283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 792218137983938916993509 148540900871988546936283)
                ·
                  rfl

theorem cell20_976328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_976328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976328 prefixEnd_976328 := by exact prefixLift 976328
  have htrace : WordTrace (prefixWord ++ tailWord_976328) baseStart_976328 baseEnd_976328 := by
    simpa [prefixWord, tailWord_976328, baseEnd_976328] using wordTrace_append hprefix tailTrace_976328
  have hstable : (prefixWord ++ tailWord_976328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976328).length < 2 ^ (prefixWord ++ tailWord_976328).sum := by decide
  have hdescent : baseEnd_976328 < baseStart_976328 := by decide
  rcases family_descends (prefixWord ++ tailWord_976328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976359 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 4]
def baseStart_976359 : Nat := 118140960795 + 976359 * 2 ^ 59
def prefixEnd_976359 : Nat := 4983230072969 + 3 ^ 40 * 976359 * 2
def baseEnd_976359 : Nat := 445636851860667310775389

theorem tailTrace_976359 : CollatzResearch.WordTrace tailWord_976359 prefixEnd_976359 445636851860667310775389 := by
  unfold tailWord_976359
  simp only [CollatzResearch.WordTrace]
  refine ⟨35610738269825566686756131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23740492179883711124504087 35610738269825566686756131)
  ·
    refine ⟨53416107404738350030134197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35610738269825566686756131 53416107404738350030134197)
    ·
      refine ⟨5007760069194220315325081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53416107404738350030134197 5007760069194220315325081)
      ·
        refine ⟨3755820051895665236493811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5007760069194220315325081 3755820051895665236493811)
        ·
          refine ⟨5633730077843497854740717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755820051895665236493811 5633730077843497854740717)
          ·
            refine ⟨2112648779191311695527769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5633730077843497854740717 2112648779191311695527769)
            ·
              refine ⟨1584486584393483771645827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2112648779191311695527769 1584486584393483771645827)
              ·
                refine ⟨2376729876590225657468741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584486584393483771645827 2376729876590225657468741)
                ·
                  refine ⟨445636851860667310775389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2376729876590225657468741 445636851860667310775389)
                  ·
                    rfl

theorem cell20_976359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_976359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976359 prefixEnd_976359 := by exact prefixLift 976359
  have htrace : WordTrace (prefixWord ++ tailWord_976359) baseStart_976359 baseEnd_976359 := by
    simpa [prefixWord, tailWord_976359, baseEnd_976359] using wordTrace_append hprefix tailTrace_976359
  have hstable : (prefixWord ++ tailWord_976359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976359).length < 2 ^ (prefixWord ++ tailWord_976359).sum := by decide
  have hdescent : baseEnd_976359 < baseStart_976359 := by decide
  rcases family_descends (prefixWord ++ tailWord_976359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976380 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_976380 : Nat := 118140960795 + 976380 * 2 ^ 59
def prefixEnd_976380 : Nat := 4983230072969 + 3 ^ 40 * 976380 * 2
def baseEnd_976380 : Nat := 445646436832884571075303

theorem tailTrace_976380 : CollatzResearch.WordTrace tailWord_976380 prefixEnd_976380 445646436832884571075303 := by
  unfold tailWord_976380
  simp only [CollatzResearch.WordTrace]
  refine ⟨17805752101374743636635297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23741002801832991515513729 17805752101374743636635297)
  ·
    refine ⟨13354314076031057727476473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17805752101374743636635297 13354314076031057727476473)
    ·
      refine ⟨10015735557023293295607355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13354314076031057727476473 10015735557023293295607355)
      ·
        refine ⟨15023603335534939943411033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10015735557023293295607355 15023603335534939943411033)
        ·
          refine ⟨11267702501651204957558275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15023603335534939943411033 11267702501651204957558275)
          ·
            refine ⟨16901553752476807436337413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11267702501651204957558275 16901553752476807436337413)
            ·
              refine ⟨3169041328589401394313265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16901553752476807436337413 3169041328589401394313265)
              ·
                refine ⟨2376780996442051045734949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3169041328589401394313265 2376780996442051045734949)
                ·
                  refine ⟨445646436832884571075303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2376780996442051045734949 445646436832884571075303)
                  ·
                    rfl

theorem cell20_976380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_976380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976380 prefixEnd_976380 := by exact prefixLift 976380
  have htrace : WordTrace (prefixWord ++ tailWord_976380) baseStart_976380 baseEnd_976380 := by
    simpa [prefixWord, tailWord_976380, baseEnd_976380] using wordTrace_append hprefix tailTrace_976380
  have hstable : (prefixWord ++ tailWord_976380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976380).length < 2 ^ (prefixWord ++ tailWord_976380).sum := by decide
  have hdescent : baseEnd_976380 < baseStart_976380 := by decide
  rcases family_descends (prefixWord ++ tailWord_976380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976424 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 3]
def baseStart_976424 : Nat := 118140960795 + 976424 * 2 ^ 59
def prefixEnd_976424 : Nat := 4983230072969 + 3 ^ 40 * 976424 * 2
def baseEnd_976424 : Nat := 445666519631815973608457

theorem tailTrace_976424 : CollatzResearch.WordTrace tailWord_976424 prefixEnd_976424 445666519631815973608457 := by
  unfold tailWord_976424
  simp only [CollatzResearch.WordTrace]
  refine ⟨17806554507295041393936163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23742072676393388525248217 17806554507295041393936163)
  ·
    refine ⟨26709831760942562090904245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17806554507295041393936163 26709831760942562090904245)
    ·
      refine ⟨2504046727588365196022273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26709831760942562090904245 2504046727588365196022273)
      ·
        refine ⟨1878035045691273897016705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2504046727588365196022273 1878035045691273897016705)
        ·
          refine ⟨1408526284268455422762529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1878035045691273897016705 1408526284268455422762529)
          ·
            refine ⟨1056394713201341567071897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1408526284268455422762529 1056394713201341567071897)
            ·
              refine ⟨792296034901006175303923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056394713201341567071897 792296034901006175303923)
              ·
                refine ⟨1188444052351509262955885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792296034901006175303923 1188444052351509262955885)
                ·
                  refine ⟨445666519631815973608457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188444052351509262955885 445666519631815973608457)
                  ·
                    rfl

theorem cell20_976424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_976424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976424 prefixEnd_976424 := by exact prefixLift 976424
  have htrace : WordTrace (prefixWord ++ tailWord_976424) baseStart_976424 baseEnd_976424 := by
    simpa [prefixWord, tailWord_976424, baseEnd_976424] using wordTrace_append hprefix tailTrace_976424
  have hstable : (prefixWord ++ tailWord_976424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976424).length < 2 ^ (prefixWord ++ tailWord_976424).sum := by decide
  have hdescent : baseEnd_976424 < baseStart_976424 := by decide
  rcases family_descends (prefixWord ++ tailWord_976424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976466 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_976466 : Nat := 118140960795 + 976466 * 2 ^ 59
def prefixEnd_976466 : Nat := 4983230072969 + 3 ^ 40 * 976466 * 2
def baseEnd_976466 : Nat := 445685689576250494208285

theorem tailTrace_976466 : CollatzResearch.WordTrace tailWord_976466 prefixEnd_976466 445685689576250494208285 := by
  unfold tailWord_976466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8903660220109480990225313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23743093920291949307267501 8903660220109480990225313)
  ·
    refine ⟨6677745165082110742668985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8903660220109480990225313 6677745165082110742668985)
    ·
      refine ⟨5008308873811583057001739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6677745165082110742668985 5008308873811583057001739)
      ·
        refine ⟨7512463310717374585502609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5008308873811583057001739 7512463310717374585502609)
        ·
          refine ⟨5634347483038030939126957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7512463310717374585502609 5634347483038030939126957)
          ·
            refine ⟨2112880306139261602172609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5634347483038030939126957 2112880306139261602172609)
            ·
              refine ⟨1584660229604446201629457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2112880306139261602172609 1584660229604446201629457)
              ·
                refine ⟨1188495172203334651222093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584660229604446201629457 1188495172203334651222093)
                ·
                  refine ⟨445685689576250494208285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188495172203334651222093 445685689576250494208285)
                  ·
                    rfl

theorem cell20_976466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_976466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976466 prefixEnd_976466 := by exact prefixLift 976466
  have htrace : WordTrace (prefixWord ++ tailWord_976466) baseStart_976466 baseEnd_976466 := by
    simpa [prefixWord, tailWord_976466, baseEnd_976466] using wordTrace_append hprefix tailTrace_976466
  have hstable : (prefixWord ++ tailWord_976466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976466).length < 2 ^ (prefixWord ++ tailWord_976466).sum := by decide
  have hdescent : baseEnd_976466 < baseStart_976466 := by decide
  rcases family_descends (prefixWord ++ tailWord_976466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976487 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 3]
def baseStart_976487 : Nat := 118140960795 + 976487 * 2 ^ 59
def prefixEnd_976487 : Nat := 4983230072969 + 3 ^ 40 * 976487 * 2
def baseEnd_976487 : Nat := 445695274548467754508199

theorem tailTrace_976487 : CollatzResearch.WordTrace tailWord_976487 prefixEnd_976487 445695274548467754508199 := by
  unfold tailWord_976487
  simp only [CollatzResearch.WordTrace]
  refine ⟨35615406813361844547415715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23743604542241229698277143 35615406813361844547415715)
  ·
    refine ⟨53423110220042766821123573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35615406813361844547415715 53423110220042766821123573)
    ·
      refine ⟨5008416583129009389480335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53423110220042766821123573 5008416583129009389480335)
      ·
        refine ⟨7512624874693514084220503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5008416583129009389480335 7512624874693514084220503)
        ·
          refine ⟨11268937312040271126330755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7512624874693514084220503 11268937312040271126330755)
          ·
            refine ⟨16903405968060406689496133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11268937312040271126330755 16903405968060406689496133)
            ·
              refine ⟨3169388619011326254280525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16903405968060406689496133 3169388619011326254280525)
              ·
                refine ⟨1188520732129247345355197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3169388619011326254280525 1188520732129247345355197)
                ·
                  refine ⟨445695274548467754508199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188520732129247345355197 445695274548467754508199)
                  ·
                    rfl

theorem cell20_976487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 3].length) (baseStart_976487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976487 prefixEnd_976487 := by exact prefixLift 976487
  have htrace : WordTrace (prefixWord ++ tailWord_976487) baseStart_976487 baseEnd_976487 := by
    simpa [prefixWord, tailWord_976487, baseEnd_976487] using wordTrace_append hprefix tailTrace_976487
  have hstable : (prefixWord ++ tailWord_976487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976487).length < 2 ^ (prefixWord ++ tailWord_976487).sum := by decide
  have hdescent : baseEnd_976487 < baseStart_976487 := by decide
  rcases family_descends (prefixWord ++ tailWord_976487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976508 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_976508 : Nat := 118140960795 + 976508 * 2 ^ 59
def prefixEnd_976508 : Nat := 4983230072969 + 3 ^ 40 * 976508 * 2
def baseEnd_976508 : Nat := 445704859520685014808113

theorem tailTrace_976508 : CollatzResearch.WordTrace tailWord_976508 prefixEnd_976508 445704859520685014808113 := by
  unfold tailWord_976508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17808086373142882566965089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23744115164190510089286785 17808086373142882566965089)
  ·
    refine ⟨13356064779857161925223817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17808086373142882566965089 13356064779857161925223817)
    ·
      refine ⟨10017048584892871443917863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13356064779857161925223817 10017048584892871443917863)
      ·
        refine ⟨15025572877339307165876795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10017048584892871443917863 15025572877339307165876795)
        ·
          refine ⟨22538359316008960748815193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15025572877339307165876795 22538359316008960748815193)
          ·
            refine ⟨16903769487006720561611395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22538359316008960748815193 16903769487006720561611395)
            ·
              refine ⟨25355654230510080842417093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16903769487006720561611395 25355654230510080842417093)
              ·
                refine ⟨4754185168220640157953205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25355654230510080842417093 4754185168220640157953205)
                ·
                  refine ⟨445704859520685014808113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4754185168220640157953205 445704859520685014808113)
                  ·
                    rfl

theorem cell20_976508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_976508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976508 prefixEnd_976508 := by exact prefixLift 976508
  have htrace : WordTrace (prefixWord ++ tailWord_976508) baseStart_976508 baseEnd_976508 := by
    simpa [prefixWord, tailWord_976508, baseEnd_976508] using wordTrace_append hprefix tailTrace_976508
  have hstable : (prefixWord ++ tailWord_976508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976508).length < 2 ^ (prefixWord ++ tailWord_976508).sum := by decide
  have hdescent : baseEnd_976508 < baseStart_976508 := by decide
  rcases family_descends (prefixWord ++ tailWord_976508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976515 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_976515 : Nat := 118140960795 + 976515 * 2 ^ 59
def prefixEnd_976515 : Nat := 4983230072969 + 3 ^ 40 * 976515 * 2
def baseEnd_976515 : Nat := 445708054511424101574751

theorem tailTrace_976515 : CollatzResearch.WordTrace tailWord_976515 prefixEnd_976515 445708054511424101574751 := by
  unfold tailWord_976515
  simp only [CollatzResearch.WordTrace]
  refine ⟨35616428057260405329434999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23744285371506936886289999 35616428057260405329434999)
  ·
    refine ⟨53424642085890607994152499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35616428057260405329434999 53424642085890607994152499)
    ·
      refine ⟨80136963128835911991228749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53424642085890607994152499 80136963128835911991228749)
      ·
        refine ⟨30051361173313466996710781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80136963128835911991228749 30051361173313466996710781)
        ·
          refine ⟨11269260439992550123766543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30051361173313466996710781 11269260439992550123766543)
          ·
            refine ⟨16903890659988825185649815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11269260439992550123766543 16903890659988825185649815)
            ·
              refine ⟨25355835989983237778474723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16903890659988825185649815 25355835989983237778474723)
              ·
                refine ⟨38033753984974856667712085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25355835989983237778474723 38033753984974856667712085)
                ·
                  refine ⟨445708054511424101574751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38033753984974856667712085 445708054511424101574751)
                  ·
                    rfl

theorem cell20_976515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_976515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976515 prefixEnd_976515 := by exact prefixLift 976515
  have htrace : WordTrace (prefixWord ++ tailWord_976515) baseStart_976515 baseEnd_976515 := by
    simpa [prefixWord, tailWord_976515, baseEnd_976515] using wordTrace_append hprefix tailTrace_976515
  have hstable : (prefixWord ++ tailWord_976515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976515).length < 2 ^ (prefixWord ++ tailWord_976515).sum := by decide
  have hdescent : baseEnd_976515 < baseStart_976515 := by decide
  rcases family_descends (prefixWord ++ tailWord_976515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976552 : List Nat := [2, 1, 7, 1, 1, 1, 1, 6]
def baseStart_976552 : Nat := 118140960795 + 976552 * 2 ^ 59
def prefixEnd_976552 : Nat := 4983230072969 + 3 ^ 40 * 976552 * 2
def baseEnd_976552 : Nat := 148574980773205472447089

theorem tailTrace_976552 : CollatzResearch.WordTrace tailWord_976552 prefixEnd_976552 148574980773205472447089 := by
  unfold tailWord_976552
  simp only [CollatzResearch.WordTrace]
  refine ⟨17808888779063180324265955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23745185038750907099021273 17808888779063180324265955)
  ·
    refine ⟨26713333168594770486398933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17808888779063180324265955 26713333168594770486398933)
    ·
      refine ⟨626093746138939933274975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26713333168594770486398933 626093746138939933274975)
      ·
        refine ⟨939140619208409899912463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626093746138939933274975 939140619208409899912463)
        ·
          refine ⟨1408710928812614849868695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939140619208409899912463 1408710928812614849868695)
          ·
            refine ⟨2113066393218922274803043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408710928812614849868695 2113066393218922274803043)
            ·
              refine ⟨3169599589828383412204565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113066393218922274803043 3169599589828383412204565)
              ·
                refine ⟨148574980773205472447089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3169599589828383412204565 148574980773205472447089)
                ·
                  rfl

theorem cell20_976552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_976552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976552 prefixEnd_976552 := by exact prefixLift 976552
  have htrace : WordTrace (prefixWord ++ tailWord_976552) baseStart_976552 baseEnd_976552 := by
    simpa [prefixWord, tailWord_976552, baseEnd_976552] using wordTrace_append hprefix tailTrace_976552
  have hstable : (prefixWord ++ tailWord_976552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976552).length < 2 ^ (prefixWord ++ tailWord_976552).sum := by decide
  have hdescent : baseEnd_976552 < baseStart_976552 := by decide
  rcases family_descends (prefixWord ++ tailWord_976552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976584 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_976584 : Nat := 118140960795 + 976584 * 2 ^ 59
def prefixEnd_976584 : Nat := 4983230072969 + 3 ^ 40 * 976584 * 2
def baseEnd_976584 : Nat := 445739547991566528274469

theorem tailTrace_976584 : CollatzResearch.WordTrace tailWord_976584 prefixEnd_976584 445739547991566528274469 := by
  unfold tailWord_976584
  simp only [CollatzResearch.WordTrace]
  refine ⟨17809472347005215056848403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23745963129340286742464537 17809472347005215056848403)
  ·
    refine ⟨26714208520507822585272605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17809472347005215056848403 26714208520507822585272605)
    ·
      refine ⟨10017828195190433469477227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26714208520507822585272605 10017828195190433469477227)
      ·
        refine ⟨15026742292785650204215841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10017828195190433469477227 15026742292785650204215841)
        ·
          refine ⟨11270056719589237653161881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15026742292785650204215841 11270056719589237653161881)
          ·
            refine ⟨8452542539691928239871411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11270056719589237653161881 8452542539691928239871411)
            ·
              refine ⟨12678813809537892359807117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8452542539691928239871411 12678813809537892359807117)
              ·
                refine ⟨4754555178576709634927669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12678813809537892359807117 4754555178576709634927669)
                ·
                  refine ⟨445739547991566528274469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4754555178576709634927669 445739547991566528274469)
                  ·
                    rfl

theorem cell20_976584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_976584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976584 prefixEnd_976584 := by exact prefixLift 976584
  have htrace : WordTrace (prefixWord ++ tailWord_976584) baseStart_976584 baseEnd_976584 := by
    simpa [prefixWord, tailWord_976584, baseEnd_976584] using wordTrace_append hprefix tailTrace_976584
  have hstable : (prefixWord ++ tailWord_976584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976584).length < 2 ^ (prefixWord ++ tailWord_976584).sum := by decide
  have hdescent : baseEnd_976584 < baseStart_976584 := by decide
  rcases family_descends (prefixWord ++ tailWord_976584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976594 : List Nat := [3, 2, 2, 2, 2, 2, 2, 5]
def baseStart_976594 : Nat := 118140960795 + 976594 * 2 ^ 59
def prefixEnd_976594 : Nat := 4983230072969 + 3 ^ 40 * 976594 * 2
def baseEnd_976594 : Nat := 148581370754683645980365

theorem tailTrace_976594 : CollatzResearch.WordTrace tailWord_976594 prefixEnd_976594 148581370754683645980365 := by
  unfold tailWord_976594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904827355993550455390209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23746206282649467881040557 8904827355993550455390209)
  ·
    refine ⟨6678620516995162841542657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8904827355993550455390209 6678620516995162841542657)
    ·
      refine ⟨5008965387746372131156993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6678620516995162841542657 5008965387746372131156993)
      ·
        refine ⟨3756724040809779098367745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5008965387746372131156993 3756724040809779098367745)
        ·
          refine ⟨2817543030607334323775809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3756724040809779098367745 2817543030607334323775809)
          ·
            refine ⟨2113157272955500742831857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2817543030607334323775809 2113157272955500742831857)
            ·
              refine ⟨1584867954716625557123893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2113157272955500742831857 1584867954716625557123893)
              ·
                refine ⟨148581370754683645980365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1584867954716625557123893 148581370754683645980365)
                ·
                  rfl

theorem cell20_976594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_976594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976594 prefixEnd_976594 := by exact prefixLift 976594
  have htrace : WordTrace (prefixWord ++ tailWord_976594) baseStart_976594 baseEnd_976594 := by
    simpa [prefixWord, tailWord_976594, baseEnd_976594] using wordTrace_append hprefix tailTrace_976594
  have hstable : (prefixWord ++ tailWord_976594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976594).length < 2 ^ (prefixWord ++ tailWord_976594).sum := by decide
  have hdescent : baseEnd_976594 < baseStart_976594 := by decide
  rcases family_descends (prefixWord ++ tailWord_976594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976601 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 3]
def baseStart_976601 : Nat := 118140960795 + 976601 * 2 ^ 59
def prefixEnd_976601 : Nat := 4983230072969 + 3 ^ 40 * 976601 * 2
def baseEnd_976601 : Nat := 445747307254790024707733

theorem tailTrace_976601 : CollatzResearch.WordTrace tailWord_976601 prefixEnd_976601 445747307254790024707733 := by
  unfold tailWord_976601
  simp only [CollatzResearch.WordTrace]
  refine ⟨35619564734948842017065657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23746376489965894678043771 35619564734948842017065657)
  ·
    refine ⟨26714673551211631512799243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35619564734948842017065657 26714673551211631512799243)
    ·
      refine ⟨40072010326817447269198865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26714673551211631512799243 40072010326817447269198865)
      ·
        refine ⟨30054007745113085451899149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40072010326817447269198865 30054007745113085451899149)
        ·
          refine ⟨11270252904417407044462181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30054007745113085451899149 11270252904417407044462181)
          ·
            refine ⟨2113172419578263820836659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11270252904417407044462181 2113172419578263820836659)
            ·
              refine ⟨3169758629367395731254989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113172419578263820836659 3169758629367395731254989)
              ·
                refine ⟨1188659486012773399220621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3169758629367395731254989 1188659486012773399220621)
                ·
                  refine ⟨445747307254790024707733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188659486012773399220621 445747307254790024707733)
                  ·
                    rfl

theorem cell20_976601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_976601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976601 prefixEnd_976601 := by exact prefixLift 976601
  have htrace : WordTrace (prefixWord ++ tailWord_976601) baseStart_976601 baseEnd_976601 := by
    simpa [prefixWord, tailWord_976601, baseEnd_976601] using wordTrace_append hprefix tailTrace_976601
  have hstable : (prefixWord ++ tailWord_976601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976601).length < 2 ^ (prefixWord ++ tailWord_976601).sum := by decide
  have hdescent : baseEnd_976601 < baseStart_976601 := by decide
  rcases family_descends (prefixWord ++ tailWord_976601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976638 : List Nat := [4, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_976638 : Nat := 118140960795 + 976638 * 2 ^ 59
def prefixEnd_976638 : Nat := 4983230072969 + 3 ^ 40 * 976638 * 2
def baseEnd_976638 : Nat := 445764195062982340474249

theorem tailTrace_976638 : CollatzResearch.WordTrace tailWord_976638 prefixEnd_976638 445764195062982340474249 := by
  unfold tailWord_976638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4452614279476849667020321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23747276157209864890775045 4452614279476849667020321)
  ·
    refine ⟨3339460709607637250265241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4452614279476849667020321 3339460709607637250265241)
    ·
      refine ⟨2504595532205727937698931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3339460709607637250265241 2504595532205727937698931)
      ·
        refine ⟨3756893298308591906548397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2504595532205727937698931 3756893298308591906548397)
        ·
          refine ⟨1408834986865721964955649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3756893298308591906548397 1408834986865721964955649)
          ·
            refine ⟨1056626240149291473716737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1408834986865721964955649 1056626240149291473716737)
            ·
              refine ⟨792469680111968605287553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056626240149291473716737 792469680111968605287553)
              ·
                refine ⟨594352260083976453965665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792469680111968605287553 594352260083976453965665)
                ·
                  refine ⟨445764195062982340474249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594352260083976453965665 445764195062982340474249)
                  ·
                    rfl

theorem cell20_976638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_976638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976638 prefixEnd_976638 := by exact prefixLift 976638
  have htrace : WordTrace (prefixWord ++ tailWord_976638) baseStart_976638 baseEnd_976638 := by
    simpa [prefixWord, tailWord_976638, baseEnd_976638] using wordTrace_append hprefix tailTrace_976638
  have hstable : (prefixWord ++ tailWord_976638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976638).length < 2 ^ (prefixWord ++ tailWord_976638).sum := by decide
  have hdescent : baseEnd_976638 < baseStart_976638 := by decide
  rcases family_descends (prefixWord ++ tailWord_976638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976642 : List Nat := [3, 4, 1, 1, 1, 1, 3, 4, 2]
def baseStart_976642 : Nat := 118140960795 + 976642 * 2 ^ 59
def prefixEnd_976642 : Nat := 4983230072969 + 3 ^ 40 * 976642 * 2
def baseEnd_976642 : Nat := 445766020771976104340899

theorem tailTrace_976642 : CollatzResearch.WordTrace tailWord_976642 prefixEnd_976642 445766020771976104340899 := by
  unfold tailWord_976642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8905265031950076504827045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23747373418533537346205453 8905265031950076504827045)
  ·
    refine ⟨1669737193490639344655071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8905265031950076504827045 1669737193490639344655071)
    ·
      refine ⟨2504605790235959016982607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1669737193490639344655071 2504605790235959016982607)
      ·
        refine ⟨3756908685353938525473911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2504605790235959016982607 3756908685353938525473911)
        ·
          refine ⟨5635363028030907788210867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756908685353938525473911 5635363028030907788210867)
          ·
            refine ⟨8453044542046361682316301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635363028030907788210867 8453044542046361682316301)
            ·
              refine ⟨3169891703267385630868613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8453044542046361682316301 3169891703267385630868613)
              ·
                refine ⟨594354694362634805787865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3169891703267385630868613 594354694362634805787865)
                ·
                  refine ⟨445766020771976104340899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594354694362634805787865 445766020771976104340899)
                  ·
                    rfl

theorem cell20_976642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_976642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976642 prefixEnd_976642 := by exact prefixLift 976642
  have htrace : WordTrace (prefixWord ++ tailWord_976642) baseStart_976642 baseEnd_976642 := by
    simpa [prefixWord, tailWord_976642, baseEnd_976642] using wordTrace_append hprefix tailTrace_976642
  have hstable : (prefixWord ++ tailWord_976642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976642).length < 2 ^ (prefixWord ++ tailWord_976642).sum := by decide
  have hdescent : baseEnd_976642 < baseStart_976642 := by decide
  rcases family_descends (prefixWord ++ tailWord_976642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976667 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 4]
def baseStart_976667 : Nat := 118140960795 + 976667 * 2 ^ 59
def prefixEnd_976667 : Nat := 4983230072969 + 3 ^ 40 * 976667 * 2
def baseEnd_976667 : Nat := 445777431453187128507463

theorem tailTrace_976667 : CollatzResearch.WordTrace tailWord_976667 prefixEnd_976667 445777431453187128507463 := by
  unfold tailWord_976667
  simp only [CollatzResearch.WordTrace]
  refine ⟨35621971952709735288968255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23747981301806490192645503 35621971952709735288968255)
  ·
    refine ⟨53432957929064602933452383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35621971952709735288968255 53432957929064602933452383)
    ·
      refine ⟨80149436893596904400178575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53432957929064602933452383 80149436893596904400178575)
      ·
        refine ⟨120224155340395356600267863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80149436893596904400178575 120224155340395356600267863)
        ·
          refine ⟨180336233010593034900401795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120224155340395356600267863 180336233010593034900401795)
          ·
            refine ⟨270504349515889552350602693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180336233010593034900401795 270504349515889552350602693)
            ·
              refine ⟨50719565534229291065738005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270504349515889552350602693 50719565534229291065738005)
              ·
                refine ⟨2377479634416998018706469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50719565534229291065738005 2377479634416998018706469)
                ·
                  refine ⟨445777431453187128507463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377479634416998018706469 445777431453187128507463)
                  ·
                    rfl

theorem cell20_976667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_976667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976667 prefixEnd_976667 := by exact prefixLift 976667
  have htrace : WordTrace (prefixWord ++ tailWord_976667) baseStart_976667 baseEnd_976667 := by
    simpa [prefixWord, tailWord_976667, baseEnd_976667] using wordTrace_append hprefix tailTrace_976667
  have hstable : (prefixWord ++ tailWord_976667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976667).length < 2 ^ (prefixWord ++ tailWord_976667).sum := by decide
  have hdescent : baseEnd_976667 < baseStart_976667 := by decide
  rcases family_descends (prefixWord ++ tailWord_976667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976680 : List Nat := [2, 1, 5, 1, 1, 3, 2, 3, 2]
def baseStart_976680 : Nat := 118140960795 + 976680 * 2 ^ 59
def prefixEnd_976680 : Nat := 4983230072969 + 3 ^ 40 * 976680 * 2
def baseEnd_976680 : Nat := 445783365007416861074077

theorem tailTrace_976680 : CollatzResearch.WordTrace tailWord_976680 prefixEnd_976680 445783365007416861074077 := by
  unfold tailWord_976680
  simp only [CollatzResearch.WordTrace]
  refine ⟨17811223050831319254595747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23748297401108425672794329 17811223050831319254595747)
  ·
    refine ⟨26716834576246978881893621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17811223050831319254595747 26716834576246978881893621)
    ·
      refine ⟨2504703241523154270177527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26716834576246978881893621 2504703241523154270177527)
      ·
        refine ⟨3757054862284731405266291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2504703241523154270177527 3757054862284731405266291)
        ·
          refine ⟨5635582293427097107899437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3757054862284731405266291 5635582293427097107899437)
          ·
            refine ⟨2113343360035161415462289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5635582293427097107899437 2113343360035161415462289)
            ·
              refine ⟨1585007520026371061596717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2113343360035161415462289 1585007520026371061596717)
              ·
                refine ⟨594377820009889148098769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1585007520026371061596717 594377820009889148098769)
                ·
                  refine ⟨445783365007416861074077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594377820009889148098769 445783365007416861074077)
                  ·
                    rfl

theorem cell20_976680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 2].length) (baseStart_976680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976680 prefixEnd_976680 := by exact prefixLift 976680
  have htrace : WordTrace (prefixWord ++ tailWord_976680) baseStart_976680 baseEnd_976680 := by
    simpa [prefixWord, tailWord_976680, baseEnd_976680] using wordTrace_append hprefix tailTrace_976680
  have hstable : (prefixWord ++ tailWord_976680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976680).length < 2 ^ (prefixWord ++ tailWord_976680).sum := by decide
  have hdescent : baseEnd_976680 < baseStart_976680 := by decide
  rcases family_descends (prefixWord ++ tailWord_976680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976691 : List Nat := [1, 1, 1, 2, 7, 1, 7]
def baseStart_976691 : Nat := 118140960795 + 976691 * 2 ^ 59
def prefixEnd_976691 : Nat := 4983230072969 + 3 ^ 40 * 976691 * 2
def baseEnd_976691 : Nat := 49532042856349967967485

theorem tailTrace_976691 : CollatzResearch.WordTrace tailWord_976691 prefixEnd_976691 49532042856349967967485 := by
  unfold tailWord_976691
  simp only [CollatzResearch.WordTrace]
  refine ⟨35622847304622787387841927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23748564869748524925227951 35622847304622787387841927)
  ·
    refine ⟨53434270956934181081762891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35622847304622787387841927 53434270956934181081762891)
    ·
      refine ⟨80151406435401271622644337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53434270956934181081762891 80151406435401271622644337)
      ·
        refine ⟨60113554826550953716983253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80151406435401271622644337 60113554826550953716983253)
        ·
          refine ⟨1408911441247287977741795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 60113554826550953716983253 1408911441247287977741795)
          ·
            refine ⟨2113367161870931966612693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408911441247287977741795 2113367161870931966612693)
            ·
              refine ⟨49532042856349967967485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2113367161870931966612693 49532042856349967967485)
              ·
                rfl

theorem cell20_976691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 7].length) (baseStart_976691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976691 prefixEnd_976691 := by exact prefixLift 976691
  have htrace : WordTrace (prefixWord ++ tailWord_976691) baseStart_976691 baseEnd_976691 := by
    simpa [prefixWord, tailWord_976691, baseEnd_976691] using wordTrace_append hprefix tailTrace_976691
  have hstable : (prefixWord ++ tailWord_976691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976691).length < 2 ^ (prefixWord ++ tailWord_976691).sum := by decide
  have hdescent : baseEnd_976691 < baseStart_976691 := by decide
  rcases family_descends (prefixWord ++ tailWord_976691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976694 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_976694 : Nat := 118140960795 + 976694 * 2 ^ 59
def prefixEnd_976694 : Nat := 4983230072969 + 3 ^ 40 * 976694 * 2
def baseEnd_976694 : Nat := 445789754988895034607353

theorem tailTrace_976694 : CollatzResearch.WordTrace tailWord_976694 prefixEnd_976694 445789754988895034607353 := by
  unfold tailWord_976694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2226434795225744931262571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23748637815741279266800757 2226434795225744931262571)
  ·
    refine ⟨3339652192838617396893857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2226434795225744931262571 3339652192838617396893857)
    ·
      refine ⟨2504739144628963047670393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3339652192838617396893857 2504739144628963047670393)
      ·
        refine ⟨1878554358471722285752795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2504739144628963047670393 1878554358471722285752795)
        ·
          refine ⟨2817831537707583428629193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878554358471722285752795 2817831537707583428629193)
          ·
            refine ⟨2113373653280687571471895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2817831537707583428629193 2113373653280687571471895)
            ·
              refine ⟨3170060479921031357207843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113373653280687571471895 3170060479921031357207843)
              ·
                refine ⟨4755090719881547035811765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3170060479921031357207843 4755090719881547035811765)
                ·
                  refine ⟨445789754988895034607353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4755090719881547035811765 445789754988895034607353)
                  ·
                    rfl

theorem cell20_976694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_976694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976694 prefixEnd_976694 := by exact prefixLift 976694
  have htrace : WordTrace (prefixWord ++ tailWord_976694) baseStart_976694 baseEnd_976694 := by
    simpa [prefixWord, tailWord_976694, baseEnd_976694] using wordTrace_append hprefix tailTrace_976694
  have hstable : (prefixWord ++ tailWord_976694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976694).length < 2 ^ (prefixWord ++ tailWord_976694).sum := by decide
  have hdescent : baseEnd_976694 < baseStart_976694 := by decide
  rcases family_descends (prefixWord ++ tailWord_976694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976701 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 4]
def baseStart_976701 : Nat := 118140960795 + 976701 * 2 ^ 59
def prefixEnd_976701 : Nat := 4983230072969 + 3 ^ 40 * 976701 * 2
def baseEnd_976701 : Nat := 445792949979634121373991

theorem tailTrace_976701 : CollatzResearch.WordTrace tailWord_976701 prefixEnd_976701 445792949979634121373991 := by
  unfold tailWord_976701
  simp only [CollatzResearch.WordTrace]
  refine ⟨35623212034586559095705957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23748808023057706063803971 35623212034586559095705957)
  ·
    refine ⟨6679352256484979830444867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35623212034586559095705957 6679352256484979830444867)
    ·
      refine ⟨10019028384727469745667301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6679352256484979830444867 10019028384727469745667301)
      ·
        refine ⟨1878567822136400577312619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10019028384727469745667301 1878567822136400577312619)
        ·
          refine ⟨2817851733204600865968929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878567822136400577312619 2817851733204600865968929)
          ·
            refine ⟨2113388799903450649476697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2817851733204600865968929 2113388799903450649476697)
            ·
              refine ⟨1585041599927587987107523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2113388799903450649476697 1585041599927587987107523)
              ·
                refine ⟨2377562399891381980661285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585041599927587987107523 2377562399891381980661285)
                ·
                  refine ⟨445792949979634121373991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377562399891381980661285 445792949979634121373991)
                  ·
                    rfl

theorem cell20_976701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_976701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976701 prefixEnd_976701 := by exact prefixLift 976701
  have htrace : WordTrace (prefixWord ++ tailWord_976701) baseStart_976701 baseEnd_976701 := by
    simpa [prefixWord, tailWord_976701, baseEnd_976701] using wordTrace_append hprefix tailTrace_976701
  have hstable : (prefixWord ++ tailWord_976701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976701).length < 2 ^ (prefixWord ++ tailWord_976701).sum := by decide
  have hdescent : baseEnd_976701 < baseStart_976701 := by decide
  rcases family_descends (prefixWord ++ tailWord_976701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976722 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_976722 : Nat := 118140960795 + 976722 * 2 ^ 59
def prefixEnd_976722 : Nat := 4983230072969 + 3 ^ 40 * 976722 * 2
def baseEnd_976722 : Nat := 445802534951851381673905

theorem tailTrace_976722 : CollatzResearch.WordTrace tailWord_976722 prefixEnd_976722 445802534951851381673905 := by
  unfold tailWord_976722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8905994491877619920555105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23749318645006986454813613 8905994491877619920555105)
  ·
    refine ⟨6679495868908214940416329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8905994491877619920555105 6679495868908214940416329)
    ·
      refine ⟨5009621901681161205312247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6679495868908214940416329 5009621901681161205312247)
      ·
        refine ⟨7514432852521741807968371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5009621901681161205312247 7514432852521741807968371)
        ·
          refine ⟨11271649278782612711952557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7514432852521741807968371 11271649278782612711952557)
          ·
            refine ⟨4226868479543479766982209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11271649278782612711952557 4226868479543479766982209)
            ·
              refine ⟨3170151359657609825236657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4226868479543479766982209 3170151359657609825236657)
              ·
                refine ⟨2377613519743207368927493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3170151359657609825236657 2377613519743207368927493)
                ·
                  refine ⟨445802534951851381673905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377613519743207368927493 445802534951851381673905)
                  ·
                    rfl

theorem cell20_976722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_976722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976722 prefixEnd_976722 := by exact prefixLift 976722
  have htrace : WordTrace (prefixWord ++ tailWord_976722) baseStart_976722 baseEnd_976722 := by
    simpa [prefixWord, tailWord_976722, baseEnd_976722] using wordTrace_append hprefix tailTrace_976722
  have hstable : (prefixWord ++ tailWord_976722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976722).length < 2 ^ (prefixWord ++ tailWord_976722).sum := by decide
  have hdescent : baseEnd_976722 < baseStart_976722 := by decide
  rcases family_descends (prefixWord ++ tailWord_976722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976736 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_976736 : Nat := 118140960795 + 976736 * 2 ^ 59
def prefixEnd_976736 : Nat := 4983230072969 + 3 ^ 40 * 976736 * 2
def baseEnd_976736 : Nat := 445808924933329555207181

theorem tailTrace_976736 : CollatzResearch.WordTrace tailWord_976736 prefixEnd_976736 445808924933329555207181 := by
  unfold tailWord_976736
  simp only [CollatzResearch.WordTrace]
  refine ⟨17812244294729880036615031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23749659059639840048820041 17812244294729880036615031)
  ·
    refine ⟨26718366442094820054922547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17812244294729880036615031 26718366442094820054922547)
    ·
      refine ⟨40077549663142230082383821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26718366442094820054922547 40077549663142230082383821)
      ·
        refine ⟨15029081123678336280893933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40077549663142230082383821 15029081123678336280893933)
        ·
          refine ⟨5635905421379376105335225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15029081123678336280893933 5635905421379376105335225)
          ·
            refine ⟨4226929066034532079001419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5635905421379376105335225 4226929066034532079001419)
            ·
              refine ⟨6340393599051798118502129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226929066034532079001419 6340393599051798118502129)
              ·
                refine ⟨4755295199288848588876597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6340393599051798118502129 4755295199288848588876597)
                ·
                  refine ⟨445808924933329555207181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4755295199288848588876597 445808924933329555207181)
                  ·
                    rfl

theorem cell20_976736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_976736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976736 prefixEnd_976736 := by exact prefixLift 976736
  have htrace : WordTrace (prefixWord ++ tailWord_976736) baseStart_976736 baseEnd_976736 := by
    simpa [prefixWord, tailWord_976736, baseEnd_976736] using wordTrace_append hprefix tailTrace_976736
  have hstable : (prefixWord ++ tailWord_976736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976736).length < 2 ^ (prefixWord ++ tailWord_976736).sum := by decide
  have hdescent : baseEnd_976736 < baseStart_976736 := by decide
  rcases family_descends (prefixWord ++ tailWord_976736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976766 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_976766 : Nat := 118140960795 + 976766 * 2 ^ 59
def prefixEnd_976766 : Nat := 4983230072969 + 3 ^ 40 * 976766 * 2
def baseEnd_976766 : Nat := 445822617750782784207059

theorem tailTrace_976766 : CollatzResearch.WordTrace tailWord_976766 prefixEnd_976766 445822617750782784207059 := by
  unfold tailWord_976766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453197847418884399602769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23750388519567383464548101 4453197847418884399602769)
  ·
    refine ⟨3339898385564163299702077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4453197847418884399602769 3339898385564163299702077)
    ·
      refine ⟨1252461894586561237388279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3339898385564163299702077 1252461894586561237388279)
      ·
        refine ⟨1878692841879841856082419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1252461894586561237388279 1878692841879841856082419)
        ·
          refine ⟨2818039262819762784123629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878692841879841856082419 2818039262819762784123629)
          ·
            refine ⟨1056764723557411044046361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2818039262819762784123629 1056764723557411044046361)
            ·
              refine ⟨792573542668058283034771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056764723557411044046361 792573542668058283034771)
              ·
                refine ⟨1188860314002087424552157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792573542668058283034771 1188860314002087424552157)
                ·
                  refine ⟨445822617750782784207059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188860314002087424552157 445822617750782784207059)
                  ·
                    rfl

theorem cell20_976766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_976766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976766 prefixEnd_976766 := by exact prefixLift 976766
  have htrace : WordTrace (prefixWord ++ tailWord_976766) baseStart_976766 baseEnd_976766 := by
    simpa [prefixWord, tailWord_976766, baseEnd_976766] using wordTrace_append hprefix tailTrace_976766
  have hstable : (prefixWord ++ tailWord_976766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976766).length < 2 ^ (prefixWord ++ tailWord_976766).sum := by decide
  have hdescent : baseEnd_976766 < baseStart_976766 := by decide
  rcases family_descends (prefixWord ++ tailWord_976766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976819 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 4]
def baseStart_976819 : Nat := 118140960795 + 976819 * 2 ^ 59
def prefixEnd_976819 : Nat := 4983230072969 + 3 ^ 40 * 976819 * 2
def baseEnd_976819 : Nat := 445846808394950155440175

theorem tailTrace_976819 : CollatzResearch.WordTrace tailWord_976819 prefixEnd_976819 445846808394950155440175 := by
  unfold tailWord_976819
  simp only [CollatzResearch.WordTrace]
  refine ⟨35627515848159065248501511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23751677232106043499001007 35627515848159065248501511)
  ·
    refine ⟨53441273772238597872752267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35627515848159065248501511 53441273772238597872752267)
    ·
      refine ⟨80161910658357896809128401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53441273772238597872752267 80161910658357896809128401)
      ·
        refine ⟨60121432993768422606846301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80161910658357896809128401 60121432993768422606846301)
        ·
          refine ⟨22545537372663158477567363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60121432993768422606846301 22545537372663158477567363)
          ·
            refine ⟨33818306058994737716351045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22545537372663158477567363 33818306058994737716351045)
            ·
              refine ⟨6340932386061513321815821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33818306058994737716351045 6340932386061513321815821)
              ·
                refine ⟨2377849644773067495680933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6340932386061513321815821 2377849644773067495680933)
                ·
                  refine ⟨445846808394950155440175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377849644773067495680933 445846808394950155440175)
                  ·
                    rfl

theorem cell20_976819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_976819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976819 prefixEnd_976819 := by exact prefixLift 976819
  have htrace : WordTrace (prefixWord ++ tailWord_976819) baseStart_976819 baseEnd_976819 := by
    simpa [prefixWord, tailWord_976819, baseEnd_976819] using wordTrace_append hprefix tailTrace_976819
  have hstable : (prefixWord ++ tailWord_976819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976819).length < 2 ^ (prefixWord ++ tailWord_976819).sum := by decide
  have hdescent : baseEnd_976819 < baseStart_976819 := by decide
  rcases family_descends (prefixWord ++ tailWord_976819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976826 : List Nat := [3, 1, 1, 1, 2, 1, 2, 9]
def baseStart_976826 : Nat := 118140960795 + 976826 * 2 ^ 59
def prefixEnd_976826 : Nat := 4983230072969 + 3 ^ 40 * 976826 * 2
def baseEnd_976826 : Nat := 148616667795229747402271

theorem tailTrace_976826 : CollatzResearch.WordTrace tailWord_976826 prefixEnd_976826 148616667795229747402271 := by
  unfold tailWord_976826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8906942789783426361001583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23751847439422470296004221 8906942789783426361001583)
  ·
    refine ⟨13360414184675139541502375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8906942789783426361001583 13360414184675139541502375)
    ·
      refine ⟨20040621277012709312253563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13360414184675139541502375 20040621277012709312253563)
      ·
        refine ⟨30060931915519063968380345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20040621277012709312253563 30060931915519063968380345)
        ·
          refine ⟨22545698936639297976285259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30060931915519063968380345 22545698936639297976285259)
          ·
            refine ⟨33818548404958946964427889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22545698936639297976285259 33818548404958946964427889)
            ·
              refine ⟨25363911303719210223320917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33818548404958946964427889 25363911303719210223320917)
              ·
                refine ⟨148616667795229747402271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25363911303719210223320917 148616667795229747402271)
                ·
                  rfl

theorem cell20_976826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_976826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976826 prefixEnd_976826 := by exact prefixLift 976826
  have htrace : WordTrace (prefixWord ++ tailWord_976826) baseStart_976826 baseEnd_976826 := by
    simpa [prefixWord, tailWord_976826, baseEnd_976826] using wordTrace_append hprefix tailTrace_976826
  have hstable : (prefixWord ++ tailWord_976826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976826).length < 2 ^ (prefixWord ++ tailWord_976826).sum := by decide
  have hdescent : baseEnd_976826 < baseStart_976826 := by decide
  rcases family_descends (prefixWord ++ tailWord_976826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976829 : List Nat := [1, 4, 1, 2, 3, 1, 2, 3, 3]
def baseStart_976829 : Nat := 118140960795 + 976829 * 2 ^ 59
def prefixEnd_976829 : Nat := 4983230072969 + 3 ^ 40 * 976829 * 2
def baseEnd_976829 : Nat := 445851372667434565106801

theorem tailTrace_976829 : CollatzResearch.WordTrace tailWord_976829 prefixEnd_976829 445851372667434565106801 := by
  unfold tailWord_976829
  simp only [CollatzResearch.WordTrace]
  refine ⟨35627880578122836956365541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23751920385415224637577027 35627880578122836956365541)
  ·
    refine ⟨6680227608398031929318539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35627880578122836956365541 6680227608398031929318539)
    ·
      refine ⟨10020341412597047893977809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6680227608398031929318539 10020341412597047893977809)
      ·
        refine ⟨7515256059447785920483357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10020341412597047893977809 7515256059447785920483357)
        ·
          refine ⟨2818221022292919720181259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7515256059447785920483357 2818221022292919720181259)
          ·
            refine ⟨4227331533439379580271889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818221022292919720181259 4227331533439379580271889)
            ·
              refine ⟨3170498650079534685203917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4227331533439379580271889 3170498650079534685203917)
              ·
                refine ⟨1188936993779825506951469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3170498650079534685203917 1188936993779825506951469)
                ·
                  refine ⟨445851372667434565106801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188936993779825506951469 445851372667434565106801)
                  ·
                    rfl

theorem cell20_976829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_976829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976829 prefixEnd_976829 := by exact prefixLift 976829
  have htrace : WordTrace (prefixWord ++ tailWord_976829) baseStart_976829 baseEnd_976829 := by
    simpa [prefixWord, tailWord_976829, baseEnd_976829] using wordTrace_append hprefix tailTrace_976829
  have hstable : (prefixWord ++ tailWord_976829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976829).length < 2 ^ (prefixWord ++ tailWord_976829).sum := by decide
  have hdescent : baseEnd_976829 < baseStart_976829 := by decide
  rcases family_descends (prefixWord ++ tailWord_976829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976843 : List Nat := [1, 1, 1, 1, 3, 4, 5, 4]
def baseStart_976843 : Nat := 118140960795 + 976843 * 2 ^ 59
def prefixEnd_976843 : Nat := 4983230072969 + 3 ^ 40 * 976843 * 2
def baseEnd_976843 : Nat := 148619254216304246213359

theorem tailTrace_976843 : CollatzResearch.WordTrace tailWord_976843 prefixEnd_976843 148619254216304246213359 := by
  unfold tailWord_976843
  simp only [CollatzResearch.WordTrace]
  refine ⟨35628391200072117347375183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23752260800048078231583455 35628391200072117347375183)
  ·
    refine ⟨53442586800108176021062775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35628391200072117347375183 53442586800108176021062775)
    ·
      refine ⟨80163880200162264031594163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53442586800108176021062775 80163880200162264031594163)
      ·
        refine ⟨120245820300243396047391245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80163880200162264031594163 120245820300243396047391245)
        ·
          refine ⟨45092182612591273517771717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120245820300243396047391245 45092182612591273517771717)
          ·
            refine ⟨8454784239860863784582197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45092182612591273517771717 8454784239860863784582197)
            ·
              refine ⟨792636022486955979804581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8454784239860863784582197 792636022486955979804581)
              ·
                refine ⟨148619254216304246213359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 792636022486955979804581 148619254216304246213359)
                ·
                  rfl

theorem cell20_976843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 4].length) (baseStart_976843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976843 prefixEnd_976843 := by exact prefixLift 976843
  have htrace : WordTrace (prefixWord ++ tailWord_976843) baseStart_976843 baseEnd_976843 := by
    simpa [prefixWord, tailWord_976843, baseEnd_976843] using wordTrace_append hprefix tailTrace_976843
  have hstable : (prefixWord ++ tailWord_976843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976843).length < 2 ^ (prefixWord ++ tailWord_976843).sum := by decide
  have hdescent : baseEnd_976843 < baseStart_976843 := by decide
  rcases family_descends (prefixWord ++ tailWord_976843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976853 : List Nat := [1, 3, 2, 3, 2, 1, 1, 5, 2]
def baseStart_976853 : Nat := 118140960795 + 976853 * 2 ^ 59
def prefixEnd_976853 : Nat := 4983230072969 + 3 ^ 40 * 976853 * 2
def baseEnd_976853 : Nat := 445862326921397148306703

theorem tailTrace_976853 : CollatzResearch.WordTrace tailWord_976853 prefixEnd_976853 445862326921397148306703 := by
  unfold tailWord_976853
  simp only [CollatzResearch.WordTrace]
  refine ⟨35628755930035889055239213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23752503953357259370159475 35628755930035889055239213)
  ·
    refine ⟨13360783473763458395714705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35628755930035889055239213 13360783473763458395714705)
    ·
      refine ⟨10020587605322593796786029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13360783473763458395714705 10020587605322593796786029)
      ·
        refine ⟨3757720351995972673794761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10020587605322593796786029 3757720351995972673794761)
        ·
          refine ⟨2818290263996979505346071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3757720351995972673794761 2818290263996979505346071)
          ·
            refine ⟨4227435395995469258019107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818290263996979505346071 4227435395995469258019107)
            ·
              refine ⟨6341153093993203887028661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4227435395995469258019107 6341153093993203887028661)
              ·
                refine ⟨594483102561862864408937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6341153093993203887028661 594483102561862864408937)
                ·
                  refine ⟨445862326921397148306703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594483102561862864408937 445862326921397148306703)
                  ·
                    rfl

theorem cell20_976853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_976853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976853 prefixEnd_976853 := by exact prefixLift 976853
  have htrace : WordTrace (prefixWord ++ tailWord_976853) baseStart_976853 baseEnd_976853 := by
    simpa [prefixWord, tailWord_976853, baseEnd_976853] using wordTrace_append hprefix tailTrace_976853
  have hstable : (prefixWord ++ tailWord_976853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976853).length < 2 ^ (prefixWord ++ tailWord_976853).sum := by decide
  have hdescent : baseEnd_976853 < baseStart_976853 := by decide
  rcases family_descends (prefixWord ++ tailWord_976853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976867 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 3]
def baseStart_976867 : Nat := 118140960795 + 976867 * 2 ^ 59
def prefixEnd_976867 : Nat := 4983230072969 + 3 ^ 40 * 976867 * 2
def baseEnd_976867 : Nat := 445868716902875321839979

theorem tailTrace_976867 : CollatzResearch.WordTrace tailWord_976867 prefixEnd_976867 445868716902875321839979 := by
  unfold tailWord_976867
  simp only [CollatzResearch.WordTrace]
  refine ⟨35629266551985169446248855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23752844367990112964165903 35629266551985169446248855)
  ·
    refine ⟨53443899827977754169373283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35629266551985169446248855 53443899827977754169373283)
    ·
      refine ⟨80165849741966631254059925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53443899827977754169373283 80165849741966631254059925)
      ·
        refine ⟨3757774206654685840034059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80165849741966631254059925 3757774206654685840034059)
        ·
          refine ⟨5636661309982028760051089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3757774206654685840034059 5636661309982028760051089)
          ·
            refine ⟨4227495982486521570038317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5636661309982028760051089 4227495982486521570038317)
            ·
              refine ⟨1585310993432445588764369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4227495982486521570038317 1585310993432445588764369)
              ·
                refine ⟨1188983245074334191573277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585310993432445588764369 1188983245074334191573277)
                ·
                  refine ⟨445868716902875321839979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1188983245074334191573277 445868716902875321839979)
                  ·
                    rfl

theorem cell20_976867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 3].length) (baseStart_976867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976867 prefixEnd_976867 := by exact prefixLift 976867
  have htrace : WordTrace (prefixWord ++ tailWord_976867) baseStart_976867 baseEnd_976867 := by
    simpa [prefixWord, tailWord_976867, baseEnd_976867] using wordTrace_append hprefix tailTrace_976867
  have hstable : (prefixWord ++ tailWord_976867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976867).length < 2 ^ (prefixWord ++ tailWord_976867).sum := by decide
  have hdescent : baseEnd_976867 < baseStart_976867 := by decide
  rcases family_descends (prefixWord ++ tailWord_976867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976874 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_976874 : Nat := 118140960795 + 976874 * 2 ^ 59
def prefixEnd_976874 : Nat := 4983230072969 + 3 ^ 40 * 976874 * 2
def baseEnd_976874 : Nat := 445871911893614408606617

theorem tailTrace_976874 : CollatzResearch.WordTrace tailWord_976874 prefixEnd_976874 445871911893614408606617 := by
  unfold tailWord_976874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8907380465739952410438419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23753014575306539761169117 8907380465739952410438419)
  ·
    refine ⟨13361070698609928615657629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8907380465739952410438419 13361070698609928615657629)
    ·
      refine ⟨5010401511978723230871611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13361070698609928615657629 5010401511978723230871611)
      ·
        refine ⟨7515602267968084846307417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5010401511978723230871611 7515602267968084846307417)
        ·
          refine ⟨5636701700976063634730563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7515602267968084846307417 5636701700976063634730563)
          ·
            refine ⟨8455052551464095452095845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5636701700976063634730563 8455052551464095452095845)
            ·
              refine ⟨1585322353399517897267971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8455052551464095452095845 1585322353399517897267971)
              ·
                refine ⟨2377983530099276845901957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585322353399517897267971 2377983530099276845901957)
                ·
                  refine ⟨445871911893614408606617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377983530099276845901957 445871911893614408606617)
                  ·
                    rfl

theorem cell20_976874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_976874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976874 prefixEnd_976874 := by exact prefixLift 976874
  have htrace : WordTrace (prefixWord ++ tailWord_976874) baseStart_976874 baseEnd_976874 := by
    simpa [prefixWord, tailWord_976874, baseEnd_976874] using wordTrace_append hprefix tailTrace_976874
  have hstable : (prefixWord ++ tailWord_976874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976874).length < 2 ^ (prefixWord ++ tailWord_976874).sum := by decide
  have hdescent : baseEnd_976874 < baseStart_976874 := by decide
  rcases family_descends (prefixWord ++ tailWord_976874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976888 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 3]
def baseStart_976888 : Nat := 118140960795 + 976888 * 2 ^ 59
def prefixEnd_976888 : Nat := 4983230072969 + 3 ^ 40 * 976888 * 2
def baseEnd_976888 : Nat := 445878301875092582139893

theorem tailTrace_976888 : CollatzResearch.WordTrace tailWord_976888 prefixEnd_976888 445878301875092582139893 := by
  unfold tailWord_976888
  simp only [CollatzResearch.WordTrace]
  refine ⟨17815016242454545016381659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23753354989939393355175545 17815016242454545016381659)
  ·
    refine ⟨26722524363681817524572489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17815016242454545016381659 26722524363681817524572489)
    ·
      refine ⟨20041893272761363143429367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26722524363681817524572489 20041893272761363143429367)
      ·
        refine ⟨30062839909142044715144051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20041893272761363143429367 30062839909142044715144051)
        ·
          refine ⟨45094259863713067072716077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30062839909142044715144051 45094259863713067072716077)
          ·
            refine ⟨16910347448892400152268529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45094259863713067072716077 16910347448892400152268529)
            ·
              refine ⟨12682760586669300114201397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16910347448892400152268529 12682760586669300114201397)
              ·
                refine ⟨1189008805000246885706381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12682760586669300114201397 1189008805000246885706381)
                ·
                  refine ⟨445878301875092582139893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189008805000246885706381 445878301875092582139893)
                  ·
                    rfl

theorem cell20_976888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_976888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976888 prefixEnd_976888 := by exact prefixLift 976888
  have htrace : WordTrace (prefixWord ++ tailWord_976888) baseStart_976888 baseEnd_976888 := by
    simpa [prefixWord, tailWord_976888, baseEnd_976888] using wordTrace_append hprefix tailTrace_976888
  have hstable : (prefixWord ++ tailWord_976888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976888).length < 2 ^ (prefixWord ++ tailWord_976888).sum := by decide
  have hdescent : baseEnd_976888 < baseStart_976888 := by decide
  rcases family_descends (prefixWord ++ tailWord_976888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976929 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 4]
def baseStart_976929 : Nat := 118140960795 + 976929 * 2 ^ 59
def prefixEnd_976929 : Nat := 4983230072969 + 3 ^ 40 * 976929 * 2
def baseEnd_976929 : Nat := 445897015392278661773059

theorem tailTrace_976929 : CollatzResearch.WordTrace tailWord_976929 prefixEnd_976929 445897015392278661773059 := by
  unfold tailWord_976929
  simp only [CollatzResearch.WordTrace]
  refine ⟨35631527877760554035005841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23754351918507036023337227 35631527877760554035005841)
  ·
    refine ⟨26723645908320415526254381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35631527877760554035005841 26723645908320415526254381)
    ·
      refine ⟨10021367215620155822345393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26723645908320415526254381 10021367215620155822345393)
      ·
        refine ⟨7516025411715116866759045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10021367215620155822345393 7516025411715116866759045)
        ·
          refine ⟨1409254764696584412517321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7516025411715116866759045 1409254764696584412517321)
          ·
            refine ⟨1056941073522438309387991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1409254764696584412517321 1056941073522438309387991)
            ·
              refine ⟨1585411610283657464081987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056941073522438309387991 1585411610283657464081987)
              ·
                refine ⟨2378117415425486196122981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585411610283657464081987 2378117415425486196122981)
                ·
                  refine ⟨445897015392278661773059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2378117415425486196122981 445897015392278661773059)
                  ·
                    rfl

theorem cell20_976929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_976929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976929 prefixEnd_976929 := by exact prefixLift 976929
  have htrace : WordTrace (prefixWord ++ tailWord_976929) baseStart_976929 baseEnd_976929 := by
    simpa [prefixWord, tailWord_976929, baseEnd_976929] using wordTrace_append hprefix tailTrace_976929
  have hstable : (prefixWord ++ tailWord_976929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976929).length < 2 ^ (prefixWord ++ tailWord_976929).sum := by decide
  have hdescent : baseEnd_976929 < baseStart_976929 := by decide
  rcases family_descends (prefixWord ++ tailWord_976929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976950 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_976950 : Nat := 118140960795 + 976950 * 2 ^ 59
def prefixEnd_976950 : Nat := 4983230072969 + 3 ^ 40 * 976950 * 2
def baseEnd_976950 : Nat := 445906600364495922072973

theorem tailTrace_976950 : CollatzResearch.WordTrace tailWord_976950 prefixEnd_976950 445906600364495922072973 := by
  unfold tailWord_976950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2227018363167779663845019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23754862540456316414346869 2227018363167779663845019)
  ·
    refine ⟨3340527544751669495767529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2227018363167779663845019 3340527544751669495767529)
    ·
      refine ⟨2505395658563752121825647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3340527544751669495767529 2505395658563752121825647)
      ·
        refine ⟨3758093487845628182738471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505395658563752121825647 3758093487845628182738471)
        ·
          refine ⟨5637140231768442274107707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758093487845628182738471 5637140231768442274107707)
          ·
            refine ⟨8455710347652663411161561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637140231768442274107707 8455710347652663411161561)
            ·
              refine ⟨6341782760739497558371171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8455710347652663411161561 6341782760739497558371171)
              ·
                refine ⟨9512674141109246337556757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341782760739497558371171 9512674141109246337556757)
                ·
                  refine ⟨445906600364495922072973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9512674141109246337556757 445906600364495922072973)
                  ·
                    rfl

theorem cell20_976950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_976950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976950 prefixEnd_976950 := by exact prefixLift 976950
  have htrace : WordTrace (prefixWord ++ tailWord_976950) baseStart_976950 baseEnd_976950 := by
    simpa [prefixWord, tailWord_976950, baseEnd_976950] using wordTrace_append hprefix tailTrace_976950
  have hstable : (prefixWord ++ tailWord_976950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976950).length < 2 ^ (prefixWord ++ tailWord_976950).sum := by decide
  have hdescent : baseEnd_976950 < baseStart_976950 := by decide
  rcases family_descends (prefixWord ++ tailWord_976950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976978 : List Nat := [3, 2, 2, 1, 12]
def baseStart_976978 : Nat := 118140960795 + 976978 * 2 ^ 59
def prefixEnd_976978 : Nat := 4983230072969 + 3 ^ 40 * 976978 * 2
def baseEnd_976978 : Nat := 5505177534906818137525

theorem tailTrace_976978 : CollatzResearch.WordTrace tailWord_976978 prefixEnd_976978 5505177534906818137525 := by
  unfold tailWord_976978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8908328763645758850884897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23755543369722023602359725 8908328763645758850884897)
  ·
    refine ⟨6681246572734319138163673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8908328763645758850884897 6681246572734319138163673)
    ·
      refine ⟨5010934929550739353622755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6681246572734319138163673 5010934929550739353622755)
      ·
        refine ⟨7516402394326109030434133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5010934929550739353622755 7516402394326109030434133)
        ·
          refine ⟨5505177534906818137525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7516402394326109030434133 5505177534906818137525)
          ·
            rfl

theorem cell20_976978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 12].length) (baseStart_976978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976978 prefixEnd_976978 := by exact prefixLift 976978
  have htrace : WordTrace (prefixWord ++ tailWord_976978) baseStart_976978 baseEnd_976978 := by
    simpa [prefixWord, tailWord_976978, baseEnd_976978] using wordTrace_append hprefix tailTrace_976978
  have hstable : (prefixWord ++ tailWord_976978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976978).length < 2 ^ (prefixWord ++ tailWord_976978).sum := by decide
  have hdescent : baseEnd_976978 < baseStart_976978 := by decide
  rcases family_descends (prefixWord ++ tailWord_976978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976981 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 3]
def baseStart_976981 : Nat := 118140960795 + 976981 * 2 ^ 59
def prefixEnd_976981 : Nat := 4983230072969 + 3 ^ 40 * 976981 * 2
def baseEnd_976981 : Nat := 445920749609197592039513

theorem tailTrace_976981 : CollatzResearch.WordTrace tailWord_976981 prefixEnd_976981 445920749609197592039513 := by
  unfold tailWord_976981
  simp only [CollatzResearch.WordTrace]
  refine ⟨35633424473572166915898797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23755616315714777943932531 35633424473572166915898797)
  ·
    refine ⟨13362534177589562593462049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35633424473572166915898797 13362534177589562593462049)
    ·
      refine ⟨10021900633192171945096537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13362534177589562593462049 10021900633192171945096537)
      ·
        refine ⟨7516425474894128958822403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10021900633192171945096537 7516425474894128958822403)
        ·
          refine ⟨11274638212341193438233605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7516425474894128958822403 11274638212341193438233605)
          ·
            refine ⟨2113994664813973769668801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11274638212341193438233605 2113994664813973769668801)
            ·
              refine ⟨1585495998610480327251601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2113994664813973769668801 1585495998610480327251601)
              ·
                refine ⟨1189121998957860245438701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585495998610480327251601 1189121998957860245438701)
                ·
                  refine ⟨445920749609197592039513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189121998957860245438701 445920749609197592039513)
                  ·
                    rfl

theorem cell20_976981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_976981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976981 prefixEnd_976981 := by exact prefixLift 976981
  have htrace : WordTrace (prefixWord ++ tailWord_976981) baseStart_976981 baseEnd_976981 := by
    simpa [prefixWord, tailWord_976981, baseEnd_976981] using wordTrace_append hprefix tailTrace_976981
  have hstable : (prefixWord ++ tailWord_976981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976981).length < 2 ^ (prefixWord ++ tailWord_976981).sum := by decide
  have hdescent : baseEnd_976981 < baseStart_976981 := by decide
  rcases family_descends (prefixWord ++ tailWord_976981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976984 : List Nat := [2, 1, 2, 2, 1, 6, 2, 2, 2]
def baseStart_976984 : Nat := 118140960795 + 976984 * 2 ^ 59
def prefixEnd_976984 : Nat := 4983230072969 + 3 ^ 40 * 976984 * 2
def baseEnd_976984 : Nat := 445922118890942914939501

theorem tailTrace_976984 : CollatzResearch.WordTrace tailWord_976984 prefixEnd_976984 445922118890942914939501 := by
  unfold tailWord_976984
  simp only [CollatzResearch.WordTrace]
  refine ⟨17816766946280649214129003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23755689261707532285505337 17816766946280649214129003)
  ·
    refine ⟨26725150419420973821193505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17816766946280649214129003 26725150419420973821193505)
    ·
      refine ⟨20043862814565730365895129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26725150419420973821193505 20043862814565730365895129)
      ·
        refine ⟨15032897110924297774421347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20043862814565730365895129 15032897110924297774421347)
        ·
          refine ⟨22549345666386446661632021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15032897110924297774421347 22549345666386446661632021)
          ·
            refine ⟨1057000578111864687264001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22549345666386446661632021 1057000578111864687264001)
            ·
              refine ⟨792750433583898515448001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057000578111864687264001 792750433583898515448001)
              ·
                refine ⟨594562825187923886586001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792750433583898515448001 594562825187923886586001)
                ·
                  refine ⟨445922118890942914939501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594562825187923886586001 445922118890942914939501)
                  ·
                    rfl

theorem cell20_976984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 2].length) (baseStart_976984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_976984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_976984 prefixEnd_976984 := by exact prefixLift 976984
  have htrace : WordTrace (prefixWord ++ tailWord_976984) baseStart_976984 baseEnd_976984 := by
    simpa [prefixWord, tailWord_976984, baseEnd_976984] using wordTrace_append hprefix tailTrace_976984
  have hstable : (prefixWord ++ tailWord_976984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976984).length < 2 ^ (prefixWord ++ tailWord_976984).sum := by decide
  have hdescent : baseEnd_976984 < baseStart_976984 := by decide
  rcases family_descends (prefixWord ++ tailWord_976984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977009 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 4]
def baseStart_977009 : Nat := 118140960795 + 977009 * 2 ^ 59
def prefixEnd_977009 : Nat := 4983230072969 + 3 ^ 40 * 977009 * 2
def baseEnd_977009 : Nat := 445933529572153939106065

theorem tailTrace_977009 : CollatzResearch.WordTrace tailWord_977009 prefixEnd_977009 445933529572153939106065 := by
  unfold tailWord_977009
  simp only [CollatzResearch.WordTrace]
  refine ⟨35634445717470727697918081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23756297144980485131945387 35634445717470727697918081)
  ·
    refine ⟨26725834288103045773438561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35634445717470727697918081 26725834288103045773438561)
    ·
      refine ⟨20044375716077284330078921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26725834288103045773438561 20044375716077284330078921)
      ·
        refine ⟨15033281787057963247559191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20044375716077284330078921 15033281787057963247559191)
        ·
          refine ⟨22549922680586944871338787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15033281787057963247559191 22549922680586944871338787)
          ·
            refine ⟨33824884020880417307008181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22549922680586944871338787 33824884020880417307008181)
            ·
              refine ⟨3171082876957539122532017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33824884020880417307008181 3171082876957539122532017)
              ·
                refine ⟨2378312157718154341899013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3171082876957539122532017 2378312157718154341899013)
                ·
                  refine ⟨445933529572153939106065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2378312157718154341899013 445933529572153939106065)
                  ·
                    rfl

theorem cell20_977009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_977009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977009 prefixEnd_977009 := by exact prefixLift 977009
  have htrace : WordTrace (prefixWord ++ tailWord_977009) baseStart_977009 baseEnd_977009 := by
    simpa [prefixWord, tailWord_977009, baseEnd_977009] using wordTrace_append hprefix tailTrace_977009
  have hstable : (prefixWord ++ tailWord_977009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977009).length < 2 ^ (prefixWord ++ tailWord_977009).sum := by decide
  have hdescent : baseEnd_977009 < baseStart_977009 := by decide
  rcases family_descends (prefixWord ++ tailWord_977009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977077 : List Nat := [1, 3, 3, 4, 1, 2, 1, 3, 2]
def baseStart_977077 : Nat := 118140960795 + 977077 * 2 ^ 59
def prefixEnd_977077 : Nat := 4983230072969 + 3 ^ 40 * 977077 * 2
def baseEnd_977077 : Nat := 445964566625047924839121

theorem tailTrace_977077 : CollatzResearch.WordTrace tailWord_977077 prefixEnd_977077 445964566625047924839121 := by
  unfold tailWord_977077
  simp only [CollatzResearch.WordTrace]
  refine ⟨35636925881224375311393485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23757950587482916874262323 35636925881224375311393485)
  ·
    refine ⟨13363847205459140741772557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35636925881224375311393485 13363847205459140741772557)
    ·
      refine ⟨5011442702047177778164709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13363847205459140741772557 5011442702047177778164709)
      ·
        refine ⟨939645506633845833405883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5011442702047177778164709 939645506633845833405883)
        ·
          refine ⟨1409468259950768750108825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939645506633845833405883 1409468259950768750108825)
          ·
            refine ⟨1057101194963076562581619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1409468259950768750108825 1057101194963076562581619)
            ·
              refine ⟨1585651792444614843872429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057101194963076562581619 1585651792444614843872429)
              ·
                refine ⟨594619422166730566452161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1585651792444614843872429 594619422166730566452161)
                ·
                  refine ⟨445964566625047924839121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594619422166730566452161 445964566625047924839121)
                  ·
                    rfl

theorem cell20_977077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_977077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977077 prefixEnd_977077 := by exact prefixLift 977077
  have htrace : WordTrace (prefixWord ++ tailWord_977077) baseStart_977077 baseEnd_977077 := by
    simpa [prefixWord, tailWord_977077, baseEnd_977077] using wordTrace_append hprefix tailTrace_977077
  have hstable : (prefixWord ++ tailWord_977077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977077).length < 2 ^ (prefixWord ++ tailWord_977077).sum := by decide
  have hdescent : baseEnd_977077 < baseStart_977077 := by decide
  rcases family_descends (prefixWord ++ tailWord_977077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977099 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_977099 : Nat := 118140960795 + 977099 * 2 ^ 59
def prefixEnd_977099 : Nat := 4983230072969 + 3 ^ 40 * 977099 * 2
def baseEnd_977099 : Nat := 445974608024513626105697

theorem tailTrace_977099 : CollatzResearch.WordTrace tailWord_977099 prefixEnd_977099 445974608024513626105697 := by
  unfold tailWord_977099
  simp only [CollatzResearch.WordTrace]
  refine ⟨35637728287144673068694351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23758485524763115379129567 35637728287144673068694351)
  ·
    refine ⟨53456592430717009603041527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35637728287144673068694351 53456592430717009603041527)
    ·
      refine ⟨80184888646075514404562291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53456592430717009603041527 80184888646075514404562291)
      ·
        refine ⟨120277332969113271606843437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80184888646075514404562291 120277332969113271606843437)
        ·
          refine ⟨45103999863417476852566289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120277332969113271606843437 45103999863417476852566289)
          ·
            refine ⟨33827999897563107639424717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45103999863417476852566289 33827999897563107639424717)
            ·
              refine ⟨12685499961586165364784269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33827999897563107639424717 12685499961586165364784269)
              ·
                refine ⟨4757062485594812011794101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12685499961586165364784269 4757062485594812011794101)
                ·
                  refine ⟨445974608024513626105697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4757062485594812011794101 445974608024513626105697)
                  ·
                    rfl

theorem cell20_977099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_977099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977099 prefixEnd_977099 := by exact prefixLift 977099
  have htrace : WordTrace (prefixWord ++ tailWord_977099) baseStart_977099 baseEnd_977099 := by
    simpa [prefixWord, tailWord_977099, baseEnd_977099] using wordTrace_append hprefix tailTrace_977099
  have hstable : (prefixWord ++ tailWord_977099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977099).length < 2 ^ (prefixWord ++ tailWord_977099).sum := by decide
  have hdescent : baseEnd_977099 < baseStart_977099 := by decide
  rcases family_descends (prefixWord ++ tailWord_977099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977102 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_977102 : Nat := 118140960795 + 977102 * 2 ^ 59
def prefixEnd_977102 : Nat := 4983230072969 + 3 ^ 40 * 977102 * 2
def baseEnd_977102 : Nat := 445975977306258949005685

theorem tailTrace_977102 : CollatzResearch.WordTrace tailWord_977102 prefixEnd_977102 445975977306258949005685 := by
  unfold tailWord_977102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4454729713266725572631695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23758558470755869720702373 4454729713266725572631695)
  ·
    refine ⟨6682094569900088358947543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4454729713266725572631695 6682094569900088358947543)
    ·
      refine ⟨10023141854850132538421315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6682094569900088358947543 10023141854850132538421315)
      ·
        refine ⟨15034712782275198807631973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10023141854850132538421315 15034712782275198807631973)
        ·
          refine ⟨2819008646676599776430995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15034712782275198807631973 2819008646676599776430995)
          ·
            refine ⟨4228512970014899664646493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819008646676599776430995 4228512970014899664646493)
            ·
              refine ⟨1585692363755587374242435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4228512970014899664646493 1585692363755587374242435)
              ·
                refine ⟨2378538545633381061363653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585692363755587374242435 2378538545633381061363653)
                ·
                  refine ⟨445975977306258949005685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2378538545633381061363653 445975977306258949005685)
                  ·
                    rfl

theorem cell20_977102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_977102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977102 prefixEnd_977102 := by exact prefixLift 977102
  have htrace : WordTrace (prefixWord ++ tailWord_977102) baseStart_977102 baseEnd_977102 := by
    simpa [prefixWord, tailWord_977102, baseEnd_977102] using wordTrace_append hprefix tailTrace_977102
  have hstable : (prefixWord ++ tailWord_977102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977102).length < 2 ^ (prefixWord ++ tailWord_977102).sum := by decide
  have hdescent : baseEnd_977102 < baseStart_977102 := by decide
  rcases family_descends (prefixWord ++ tailWord_977102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977112 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 3]
def baseStart_977112 : Nat := 118140960795 + 977112 * 2 ^ 59
def prefixEnd_977112 : Nat := 4983230072969 + 3 ^ 40 * 977112 * 2
def baseEnd_977112 : Nat := 445980541578743358672311

theorem tailTrace_977112 : CollatzResearch.WordTrace tailWord_977112 prefixEnd_977112 445980541578743358672311 := by
  unfold tailWord_977112
  simp only [CollatzResearch.WordTrace]
  refine ⟨17819101218048788144458795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23758801624065050859278393 17819101218048788144458795)
  ·
    refine ⟨26728651827073182216688193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17819101218048788144458795 26728651827073182216688193)
    ·
      refine ⟨20046488870304886662516145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26728651827073182216688193 20046488870304886662516145)
      ·
        refine ⟨15034866652728664996887109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20046488870304886662516145 15034866652728664996887109)
        ·
          refine ⟨2819037497386624686916333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15034866652728664996887109 2819037497386624686916333)
          ·
            refine ⟨1057139061519984257593625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2819037497386624686916333 1057139061519984257593625)
            ·
              refine ⟨792854296139988193195219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057139061519984257593625 792854296139988193195219)
              ·
                refine ⟨1189281444209982289792829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792854296139988193195219 1189281444209982289792829)
                ·
                  refine ⟨445980541578743358672311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189281444209982289792829 445980541578743358672311)
                  ·
                    rfl

theorem cell20_977112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_977112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977112 prefixEnd_977112 := by exact prefixLift 977112
  have htrace : WordTrace (prefixWord ++ tailWord_977112) baseStart_977112 baseEnd_977112 := by
    simpa [prefixWord, tailWord_977112, baseEnd_977112] using wordTrace_append hprefix tailTrace_977112
  have hstable : (prefixWord ++ tailWord_977112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977112).length < 2 ^ (prefixWord ++ tailWord_977112).sum := by decide
  have hdescent : baseEnd_977112 < baseStart_977112 := by decide
  rcases family_descends (prefixWord ++ tailWord_977112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977130 : List Nat := [3, 1, 3, 1, 1, 2, 1, 8]
def baseStart_977130 : Nat := 118140960795 + 977130 * 2 ^ 59
def prefixEnd_977130 : Nat := 4983230072969 + 3 ^ 40 * 977130 * 2
def baseEnd_977130 : Nat := 148662919089738432024079

theorem tailTrace_977130 : CollatzResearch.WordTrace tailWord_977130 prefixEnd_977130 148662919089738432024079 := by
  unfold tailWord_977130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8909714737508091340768211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23759239300021576908715229 8909714737508091340768211)
  ·
    refine ⟨13364572106262137011152317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8909714737508091340768211 13364572106262137011152317)
    ·
      refine ⟨5011714539848301379182119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13364572106262137011152317 5011714539848301379182119)
      ·
        refine ⟨7517571809772452068773179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5011714539848301379182119 7517571809772452068773179)
        ·
          refine ⟨11276357714658678103159769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7517571809772452068773179 11276357714658678103159769)
          ·
            refine ⟨8457268285994008577369827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11276357714658678103159769 8457268285994008577369827)
            ·
              refine ⟨12685902428991012866054741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8457268285994008577369827 12685902428991012866054741)
              ·
                refine ⟨148662919089738432024079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12685902428991012866054741 148662919089738432024079)
                ·
                  rfl

theorem cell20_977130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_977130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977130 prefixEnd_977130 := by exact prefixLift 977130
  have htrace : WordTrace (prefixWord ++ tailWord_977130) baseStart_977130 baseEnd_977130 := by
    simpa [prefixWord, tailWord_977130, baseEnd_977130] using wordTrace_append hprefix tailTrace_977130
  have hstable : (prefixWord ++ tailWord_977130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977130).length < 2 ^ (prefixWord ++ tailWord_977130).sum := by decide
  have hdescent : baseEnd_977130 < baseStart_977130 := by decide
  rcases family_descends (prefixWord ++ tailWord_977130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977137 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_977137 : Nat := 118140960795 + 977137 * 2 ^ 59
def prefixEnd_977137 : Nat := 4983230072969 + 3 ^ 40 * 977137 * 2
def baseEnd_977137 : Nat := 445991952259954382838875

theorem tailTrace_977137 : CollatzResearch.WordTrace tailWord_977137 prefixEnd_977137 445991952259954382838875 := by
  unfold tailWord_977137
  simp only [CollatzResearch.WordTrace]
  refine ⟨35639114261007005558577665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23759409507338003705718443 35639114261007005558577665)
  ·
    refine ⟨26729335695755254168933249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35639114261007005558577665 26729335695755254168933249)
    ·
      refine ⟨20047001771816440626699937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26729335695755254168933249 20047001771816440626699937)
      ·
        refine ⟨15035251328862330470024953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20047001771816440626699937 15035251328862330470024953)
        ·
          refine ⟨11276438496646747852518715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15035251328862330470024953 11276438496646747852518715)
          ·
            refine ⟨16914657744970121778778073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11276438496646747852518715 16914657744970121778778073)
            ·
              refine ⟨12685993308727591334083555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16914657744970121778778073 12685993308727591334083555)
              ·
                refine ⟨19028989963091387001125333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12685993308727591334083555 19028989963091387001125333)
                ·
                  refine ⟨445991952259954382838875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19028989963091387001125333 445991952259954382838875)
                  ·
                    rfl

theorem cell20_977137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_977137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977137 prefixEnd_977137 := by exact prefixLift 977137
  have htrace : WordTrace (prefixWord ++ tailWord_977137) baseStart_977137 baseEnd_977137 := by
    simpa [prefixWord, tailWord_977137, baseEnd_977137] using wordTrace_append hprefix tailTrace_977137
  have hstable : (prefixWord ++ tailWord_977137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977137).length < 2 ^ (prefixWord ++ tailWord_977137).sum := by decide
  have hdescent : baseEnd_977137 < baseStart_977137 := by decide
  rcases family_descends (prefixWord ++ tailWord_977137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977178 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_977178 : Nat := 118140960795 + 977178 * 2 ^ 59
def prefixEnd_977178 : Nat := 4983230072969 + 3 ^ 40 * 977178 * 2
def baseEnd_977178 : Nat := 446010665777140462472041

theorem tailTrace_977178 : CollatzResearch.WordTrace tailWord_977178 prefixEnd_977178 446010665777140462472041 := by
  unfold tailWord_977178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8910152413464617390205047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23760406435905646373880125 8910152413464617390205047)
  ·
    refine ⟨13365228620196926085307571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8910152413464617390205047 13365228620196926085307571)
    ·
      refine ⟨20047842930295389127961357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13365228620196926085307571 20047842930295389127961357)
      ·
        refine ⟨7517941098860770922985509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20047842930295389127961357 7517941098860770922985509)
        ·
          refine ⟨1409613956036394548059783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7517941098860770922985509 1409613956036394548059783)
          ·
            refine ⟨2114420934054591822089675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409613956036394548059783 2114420934054591822089675)
            ·
              refine ⟨3171631401081887733134513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114420934054591822089675 3171631401081887733134513)
              ·
                refine ⟨2378723550811415799850885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3171631401081887733134513 2378723550811415799850885)
                ·
                  refine ⟨446010665777140462472041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2378723550811415799850885 446010665777140462472041)
                  ·
                    rfl

theorem cell20_977178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_977178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977178 prefixEnd_977178 := by exact prefixLift 977178
  have htrace : WordTrace (prefixWord ++ tailWord_977178) baseStart_977178 baseEnd_977178 := by
    simpa [prefixWord, tailWord_977178, baseEnd_977178] using wordTrace_append hprefix tailTrace_977178
  have hstable : (prefixWord ++ tailWord_977178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977178).length < 2 ^ (prefixWord ++ tailWord_977178).sum := by decide
  have hdescent : baseEnd_977178 < baseStart_977178 := by decide
  rcases family_descends (prefixWord ++ tailWord_977178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977209 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 3]
def baseStart_977209 : Nat := 118140960795 + 977209 * 2 ^ 59
def prefixEnd_977209 : Nat := 4983230072969 + 3 ^ 40 * 977209 * 2
def baseEnd_977209 : Nat := 446024815021842132438581

theorem tailTrace_977209 : CollatzResearch.WordTrace tailWord_977209 prefixEnd_977209 446024815021842132438581 := by
  unfold tailWord_977209
  simp only [CollatzResearch.WordTrace]
  refine ⟨35641740316746161855198681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23761160211164107903465787 35641740316746161855198681)
  ·
    refine ⟨26731305237559621391399011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35641740316746161855198681 26731305237559621391399011)
    ·
      refine ⟨40096957856339432087098517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26731305237559621391399011 40096957856339432087098517)
      ·
        refine ⟨1879544899515910879082743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40096957856339432087098517 1879544899515910879082743)
        ·
          refine ⟨2819317349273866318624115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1879544899515910879082743 2819317349273866318624115)
          ·
            refine ⟨4228976023910799477936173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819317349273866318624115 4228976023910799477936173)
            ·
              refine ⟨1585866008966549804226065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4228976023910799477936173 1585866008966549804226065)
              ·
                refine ⟨1189399506724912353169549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585866008966549804226065 1189399506724912353169549)
                ·
                  refine ⟨446024815021842132438581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1189399506724912353169549 446024815021842132438581)
                  ·
                    rfl

theorem cell20_977209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_977209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977209 prefixEnd_977209 := by exact prefixLift 977209
  have htrace : WordTrace (prefixWord ++ tailWord_977209) baseStart_977209 baseEnd_977209 := by
    simpa [prefixWord, tailWord_977209, baseEnd_977209] using wordTrace_append hprefix tailTrace_977209
  have hstable : (prefixWord ++ tailWord_977209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977209).length < 2 ^ (prefixWord ++ tailWord_977209).sum := by decide
  have hdescent : baseEnd_977209 < baseStart_977209 := by decide
  rcases family_descends (prefixWord ++ tailWord_977209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977250 : List Nat := [3, 3, 2, 1, 1, 4, 1, 3, 2]
def baseStart_977250 : Nat := 118140960795 + 977250 * 2 ^ 59
def prefixEnd_977250 : Nat := 4983230072969 + 3 ^ 40 * 977250 * 2
def baseEnd_977250 : Nat := 446043528539028212071747

theorem tailTrace_977250 : CollatzResearch.WordTrace tailWord_977250 prefixEnd_977250 446043528539028212071747 := by
  unfold tailWord_977250
  simp only [CollatzResearch.WordTrace]
  refine ⟨8910808927399406464360301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23762157139731750571627469 8910808927399406464360301)
  ·
    refine ⟨3341553347774777424135113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8910808927399406464360301 3341553347774777424135113)
    ·
      refine ⟨2506165010831083068101335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3341553347774777424135113 2506165010831083068101335)
      ·
        refine ⟨3759247516246624602152003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2506165010831083068101335 3759247516246624602152003)
        ·
          refine ⟨5638871274369936903228005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3759247516246624602152003 5638871274369936903228005)
          ·
            refine ⟨1057288363944363169355251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5638871274369936903228005 1057288363944363169355251)
            ·
              refine ⟨1585932545916544754032877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057288363944363169355251 1585932545916544754032877)
              ·
                refine ⟨594724704718704282762329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1585932545916544754032877 594724704718704282762329)
                ·
                  refine ⟨446043528539028212071747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594724704718704282762329 446043528539028212071747)
                  ·
                    rfl

theorem cell20_977250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_977250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977250 prefixEnd_977250 := by exact prefixLift 977250
  have htrace : WordTrace (prefixWord ++ tailWord_977250) baseStart_977250 baseEnd_977250 := by
    simpa [prefixWord, tailWord_977250, baseEnd_977250] using wordTrace_append hprefix tailTrace_977250
  have hstable : (prefixWord ++ tailWord_977250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977250).length < 2 ^ (prefixWord ++ tailWord_977250).sum := by decide
  have hdescent : baseEnd_977250 < baseStart_977250 := by decide
  rcases family_descends (prefixWord ++ tailWord_977250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977251 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_977251 : Nat := 118140960795 + 977251 * 2 ^ 59
def prefixEnd_977251 : Nat := 4983230072969 + 3 ^ 40 * 977251 * 2
def baseEnd_977251 : Nat := 446043984966276653038409

theorem tailTrace_977251 : CollatzResearch.WordTrace tailWord_977251 prefixEnd_977251 446043984966276653038409 := by
  unfold tailWord_977251
  simp only [CollatzResearch.WordTrace]
  refine ⟨35643272182594003028227607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23762181455062668685485071 35643272182594003028227607)
  ·
    refine ⟨53464908273891004542341411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35643272182594003028227607 53464908273891004542341411)
    ·
      refine ⟨80197362410836506813512117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53464908273891004542341411 80197362410836506813512117)
      ·
        refine ⟨7518502726015922513766761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80197362410836506813512117 7518502726015922513766761)
        ·
          refine ⟨5638877044511941885325071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7518502726015922513766761 5638877044511941885325071)
          ·
            refine ⟨8458315566767912827987607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5638877044511941885325071 8458315566767912827987607)
            ·
              refine ⟨12687473350151869241981411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458315566767912827987607 12687473350151869241981411)
              ·
                refine ⟨19031210025227803862972117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12687473350151869241981411 19031210025227803862972117)
                ·
                  refine ⟨446043984966276653038409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19031210025227803862972117 446043984966276653038409)
                  ·
                    rfl

theorem cell20_977251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_977251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977251 prefixEnd_977251 := by exact prefixLift 977251
  have htrace : WordTrace (prefixWord ++ tailWord_977251) baseStart_977251 baseEnd_977251 := by
    simpa [prefixWord, tailWord_977251, baseEnd_977251] using wordTrace_append hprefix tailTrace_977251
  have hstable : (prefixWord ++ tailWord_977251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977251).length < 2 ^ (prefixWord ++ tailWord_977251).sum := by decide
  have hdescent : baseEnd_977251 < baseStart_977251 := by decide
  rcases family_descends (prefixWord ++ tailWord_977251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977275 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 4]
def baseStart_977275 : Nat := 118140960795 + 977275 * 2 ^ 59
def prefixEnd_977275 : Nat := 4983230072969 + 3 ^ 40 * 977275 * 2
def baseEnd_977275 : Nat := 446054939220239236238311

theorem tailTrace_977275 : CollatzResearch.WordTrace tailWord_977275 prefixEnd_977275 446054939220239236238311 := by
  unfold tailWord_977275
  simp only [CollatzResearch.WordTrace]
  refine ⟨35644147534507055127101279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23762765023004703418067519 35644147534507055127101279)
  ·
    refine ⟨53466221301760582690651919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35644147534507055127101279 53466221301760582690651919)
    ·
      refine ⟨80199331952640874035977879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53466221301760582690651919 80199331952640874035977879)
      ·
        refine ⟨120298997928961311053966819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80199331952640874035977879 120298997928961311053966819)
        ·
          refine ⟨180448496893441966580950229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120298997928961311053966819 180448496893441966580950229)
          ·
            refine ⟨4229261645940046091741021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 180448496893441966580950229 4229261645940046091741021)
            ·
              refine ⟨1585973117227517284402883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4229261645940046091741021 1585973117227517284402883)
              ·
                refine ⟨2378959675841275926604325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585973117227517284402883 2378959675841275926604325)
                ·
                  refine ⟨446054939220239236238311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2378959675841275926604325 446054939220239236238311)
                  ·
                    rfl

theorem cell20_977275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_977275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977275 prefixEnd_977275 := by exact prefixLift 977275
  have htrace : WordTrace (prefixWord ++ tailWord_977275) baseStart_977275 baseEnd_977275 := by
    simpa [prefixWord, tailWord_977275, baseEnd_977275] using wordTrace_append hprefix tailTrace_977275
  have hstable : (prefixWord ++ tailWord_977275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977275).length < 2 ^ (prefixWord ++ tailWord_977275).sum := by decide
  have hdescent : baseEnd_977275 < baseStart_977275 := by decide
  rcases family_descends (prefixWord ++ tailWord_977275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977330 : List Nat := [3, 2, 1, 1, 1, 1, 5, 4, 2]
def baseStart_977330 : Nat := 118140960795 + 977330 * 2 ^ 59
def prefixEnd_977330 : Nat := 4983230072969 + 3 ^ 40 * 977330 * 2
def baseEnd_977330 : Nat := 446080042718903489404753

theorem tailTrace_977330 : CollatzResearch.WordTrace tailWord_977330 prefixEnd_977330 446080042718903489404753 := by
  unfold tailWord_977330
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911538387326949880088361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23764102366205199680235629 8911538387326949880088361)
  ·
    refine ⟨6683653790495212410066271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8911538387326949880088361 6683653790495212410066271)
    ·
      refine ⟨10025480685742818615099407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6683653790495212410066271 10025480685742818615099407)
      ·
        refine ⟨15038221028614227922649111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10025480685742818615099407 15038221028614227922649111)
        ·
          refine ⟨22557331542921341883973667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15038221028614227922649111 22557331542921341883973667)
          ·
            refine ⟨33835997314382012825960501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22557331542921341883973667 33835997314382012825960501)
            ·
              refine ⟨3172124748223313702433797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33835997314382012825960501 3172124748223313702433797)
              ·
                refine ⟨594773390291871319206337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3172124748223313702433797 594773390291871319206337)
                ·
                  refine ⟨446080042718903489404753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594773390291871319206337 446080042718903489404753)
                  ·
                    rfl

theorem cell20_977330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_977330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977330 prefixEnd_977330 := by exact prefixLift 977330
  have htrace : WordTrace (prefixWord ++ tailWord_977330) baseStart_977330 baseEnd_977330 := by
    simpa [prefixWord, tailWord_977330, baseEnd_977330] using wordTrace_append hprefix tailTrace_977330
  have hstable : (prefixWord ++ tailWord_977330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977330).length < 2 ^ (prefixWord ++ tailWord_977330).sum := by decide
  have hdescent : baseEnd_977330 < baseStart_977330 := by decide
  rcases family_descends (prefixWord ++ tailWord_977330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977337 : List Nat := [1, 2, 1, 4, 3, 3, 1, 5]
def baseStart_977337 : Nat := 118140960795 + 977337 * 2 ^ 59
def prefixEnd_977337 : Nat := 4983230072969 + 3 ^ 40 * 977337 * 2
def baseEnd_977337 : Nat := 148694412569880858723797

theorem tailTrace_977337 : CollatzResearch.WordTrace tailWord_977337 prefixEnd_977337 148694412569880858723797 := by
  unfold tailWord_977337
  simp only [CollatzResearch.WordTrace]
  refine ⟨35646408860282439715858265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23764272573521626477238843 35646408860282439715858265)
  ·
    refine ⟨26734806645211829786893699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35646408860282439715858265 26734806645211829786893699)
    ·
      refine ⟨40102209967817744680340549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26734806645211829786893699 40102209967817744680340549)
      ·
        refine ⟨7519164368965827127563853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40102209967817744680340549 7519164368965827127563853)
        ·
          refine ⟨2819686638362185172836445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7519164368965827127563853 2819686638362185172836445)
          ·
            refine ⟨1057382489385819439813667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2819686638362185172836445 1057382489385819439813667)
            ·
              refine ⟨1586073734078729159720501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057382489385819439813667 1586073734078729159720501)
              ·
                refine ⟨148694412569880858723797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1586073734078729159720501 148694412569880858723797)
                ·
                  rfl

theorem cell20_977337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 5].length) (baseStart_977337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977337 prefixEnd_977337 := by exact prefixLift 977337
  have htrace : WordTrace (prefixWord ++ tailWord_977337) baseStart_977337 baseEnd_977337 := by
    simpa [prefixWord, tailWord_977337, baseEnd_977337] using wordTrace_append hprefix tailTrace_977337
  have hstable : (prefixWord ++ tailWord_977337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977337).length < 2 ^ (prefixWord ++ tailWord_977337).sum := by decide
  have hdescent : baseEnd_977337 < baseStart_977337 := by decide
  rcases family_descends (prefixWord ++ tailWord_977337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977351 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 4]
def baseStart_977351 : Nat := 118140960795 + 977351 * 2 ^ 59
def prefixEnd_977351 : Nat := 4983230072969 + 3 ^ 40 * 977351 * 2
def baseEnd_977351 : Nat := 446089627691120749704667

theorem tailTrace_977351 : CollatzResearch.WordTrace tailWord_977351 prefixEnd_977351 446089627691120749704667 := by
  unfold tailWord_977351
  simp only [CollatzResearch.WordTrace]
  refine ⟨35646919482231720106867907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23764612988154480071245271 35646919482231720106867907)
  ·
    refine ⟨53470379223347580160301861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35646919482231720106867907 53470379223347580160301861)
    ·
      refine ⟨10025696104377671280056599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53470379223347580160301861 10025696104377671280056599)
      ·
        refine ⟨15038544156566506920084899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10025696104377671280056599 15038544156566506920084899)
        ·
          refine ⟨22557816234849760380127349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15038544156566506920084899 22557816234849760380127349)
          ·
            refine ⟨2114795272017165035636939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22557816234849760380127349 2114795272017165035636939)
            ·
              refine ⟨3172192908025747553455409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114795272017165035636939 3172192908025747553455409)
              ·
                refine ⟨2379144681019310665091557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3172192908025747553455409 2379144681019310665091557)
                ·
                  refine ⟨446089627691120749704667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2379144681019310665091557 446089627691120749704667)
                  ·
                    rfl

theorem cell20_977351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_977351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977351 prefixEnd_977351 := by exact prefixLift 977351
  have htrace : WordTrace (prefixWord ++ tailWord_977351) baseStart_977351 baseEnd_977351 := by
    simpa [prefixWord, tailWord_977351, baseEnd_977351] using wordTrace_append hprefix tailTrace_977351
  have hstable : (prefixWord ++ tailWord_977351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977351).length < 2 ^ (prefixWord ++ tailWord_977351).sum := by decide
  have hdescent : baseEnd_977351 < baseStart_977351 := by decide
  rcases family_descends (prefixWord ++ tailWord_977351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977378 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_977378 : Nat := 118140960795 + 977378 * 2 ^ 59
def prefixEnd_977378 : Nat := 4983230072969 + 3 ^ 40 * 977378 * 2
def baseEnd_977378 : Nat := 446101951226828655804557

theorem tailTrace_977378 : CollatzResearch.WordTrace tailWord_977378 prefixEnd_977378 446101951226828655804557 := by
  unfold tailWord_977378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911976063283475929525197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23765269502089269145400525 8911976063283475929525197)
  ·
    refine ⟨3341991023731303473571949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8911976063283475929525197 3341991023731303473571949)
    ·
      refine ⟨1253246633899238802589481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3341991023731303473571949 1253246633899238802589481)
      ·
        refine ⟨939934975424429101942111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1253246633899238802589481 939934975424429101942111)
        ·
          refine ⟨1409902463136643652913167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939934975424429101942111 1409902463136643652913167)
          ·
            refine ⟨2114853694704965479369751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409902463136643652913167 2114853694704965479369751)
            ·
              refine ⟨3172280542057448219054627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114853694704965479369751 3172280542057448219054627)
              ·
                refine ⟨4758420813086172328581941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172280542057448219054627 4758420813086172328581941)
                ·
                  refine ⟨446101951226828655804557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4758420813086172328581941 446101951226828655804557)
                  ·
                    rfl

theorem cell20_977378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_977378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977378 prefixEnd_977378 := by exact prefixLift 977378
  have htrace : WordTrace (prefixWord ++ tailWord_977378) baseStart_977378 baseEnd_977378 := by
    simpa [prefixWord, tailWord_977378, baseEnd_977378] using wordTrace_append hprefix tailTrace_977378
  have hstable : (prefixWord ++ tailWord_977378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977378).length < 2 ^ (prefixWord ++ tailWord_977378).sum := by decide
  have hdescent : baseEnd_977378 < baseStart_977378 := by decide
  rcases family_descends (prefixWord ++ tailWord_977378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977440 : List Nat := [2, 1, 1, 6, 2, 1, 3, 2, 2]
def baseStart_977440 : Nat := 118140960795 + 977440 * 2 ^ 59
def prefixEnd_977440 : Nat := 4983230072969 + 3 ^ 40 * 977440 * 2
def baseEnd_977440 : Nat := 446130249716231995737637

theorem tailTrace_977440 : CollatzResearch.WordTrace tailWord_977440 prefixEnd_977440 446130249716231995737637 := by
  unfold tailWord_977440
  simp only [CollatzResearch.WordTrace]
  refine ⟨17825082789454644153428887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23766777052606192204571849 17825082789454644153428887)
  ·
    refine ⟨26737624184181966230143331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17825082789454644153428887 26737624184181966230143331)
    ·
      refine ⟨40106436276272949345214997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26737624184181966230143331 40106436276272949345214997)
      ·
        refine ⟨1879989200450294500556953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40106436276272949345214997 1879989200450294500556953)
        ·
          refine ⟨1409991900337720875417715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1879989200450294500556953 1409991900337720875417715)
          ·
            refine ⟨2114987850506581313126573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409991900337720875417715 2114987850506581313126573)
            ·
              refine ⟨793120443939967992422465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2114987850506581313126573 793120443939967992422465)
              ·
                refine ⟨594840332954975994316849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793120443939967992422465 594840332954975994316849)
                ·
                  refine ⟨446130249716231995737637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594840332954975994316849 446130249716231995737637)
                  ·
                    rfl

theorem cell20_977440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 2].length) (baseStart_977440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977440 prefixEnd_977440 := by exact prefixLift 977440
  have htrace : WordTrace (prefixWord ++ tailWord_977440) baseStart_977440 baseEnd_977440 := by
    simpa [prefixWord, tailWord_977440, baseEnd_977440] using wordTrace_append hprefix tailTrace_977440
  have hstable : (prefixWord ++ tailWord_977440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977440).length < 2 ^ (prefixWord ++ tailWord_977440).sum := by decide
  have hdescent : baseEnd_977440 < baseStart_977440 := by decide
  rcases family_descends (prefixWord ++ tailWord_977440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977441 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_977441 : Nat := 118140960795 + 977441 * 2 ^ 59
def prefixEnd_977441 : Nat := 4983230072969 + 3 ^ 40 * 977441 * 2
def baseEnd_977441 : Nat := 446130706143480436704299

theorem tailTrace_977441 : CollatzResearch.WordTrace tailWord_977441 prefixEnd_977441 446130706143480436704299 := by
  unfold tailWord_977441
  simp only [CollatzResearch.WordTrace]
  refine ⟨35650202051905665477644177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23766801367937110318429451 35650202051905665477644177)
  ·
    refine ⟨26737651538929249108233133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35650202051905665477644177 26737651538929249108233133)
    ·
      refine ⟨10026619327098468415587425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26737651538929249108233133 10026619327098468415587425)
      ·
        refine ⟨7519964495323851311690569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10026619327098468415587425 7519964495323851311690569)
        ·
          refine ⟨5639973371492888483767927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7519964495323851311690569 5639973371492888483767927)
          ·
            refine ⟨8459960057239332725651891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639973371492888483767927 8459960057239332725651891)
            ·
              refine ⟨12689940085858999088477837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8459960057239332725651891 12689940085858999088477837)
              ·
                refine ⟨4758727532197124658179189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12689940085858999088477837 4758727532197124658179189)
                ·
                  refine ⟨446130706143480436704299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4758727532197124658179189 446130706143480436704299)
                  ·
                    rfl

theorem cell20_977441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_977441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977441 prefixEnd_977441 := by exact prefixLift 977441
  have htrace : WordTrace (prefixWord ++ tailWord_977441) baseStart_977441 baseEnd_977441 := by
    simpa [prefixWord, tailWord_977441, baseEnd_977441] using wordTrace_append hprefix tailTrace_977441
  have hstable : (prefixWord ++ tailWord_977441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977441).length < 2 ^ (prefixWord ++ tailWord_977441).sum := by decide
  have hdescent : baseEnd_977441 < baseStart_977441 := by decide
  rcases family_descends (prefixWord ++ tailWord_977441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977502 : List Nat := [4, 4, 1, 2, 1, 2, 1, 5]
def baseStart_977502 : Nat := 118140960795 + 977502 * 2 ^ 59
def prefixEnd_977502 : Nat := 4983230072969 + 3 ^ 40 * 977502 * 2
def baseEnd_977502 : Nat := 148719516068545111890239

theorem tailTrace_977502 : CollatzResearch.WordTrace tailWord_977502 prefixEnd_977502 148719516068545111890239 := by
  unfold tailWord_977502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456553363085584111951845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23768284603123115263743173 4456553363085584111951845)
  ·
    refine ⟨835603755578547020990971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4456553363085584111951845 835603755578547020990971)
    ·
      refine ⟨1253405633367820531486457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 835603755578547020990971 1253405633367820531486457)
      ·
        refine ⟨940054225025865398614843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1253405633367820531486457 940054225025865398614843)
        ·
          refine ⟨1410081337538798097922265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940054225025865398614843 1410081337538798097922265)
          ·
            refine ⟨1057561003154098573441699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1410081337538798097922265 1057561003154098573441699)
            ·
              refine ⟨1586341504731147860162549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057561003154098573441699 1586341504731147860162549)
              ·
                refine ⟨148719516068545111890239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1586341504731147860162549 148719516068545111890239)
                ·
                  rfl

theorem cell20_977502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_977502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977502 prefixEnd_977502 := by exact prefixLift 977502
  have htrace : WordTrace (prefixWord ++ tailWord_977502) baseStart_977502 baseEnd_977502 := by
    simpa [prefixWord, tailWord_977502, baseEnd_977502] using wordTrace_append hprefix tailTrace_977502
  have hstable : (prefixWord ++ tailWord_977502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977502).length < 2 ^ (prefixWord ++ tailWord_977502).sum := by decide
  have hdescent : baseEnd_977502 < baseStart_977502 := by decide
  rcases family_descends (prefixWord ++ tailWord_977502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977578 : List Nat := [3, 1, 5, 2, 2, 1, 2, 4]
def baseStart_977578 : Nat := 118140960795 + 977578 * 2 ^ 59
def prefixEnd_977578 : Nat := 4983230072969 + 3 ^ 40 * 977578 * 2
def baseEnd_977578 : Nat := 148731078892172283045691

theorem tailTrace_977578 : CollatzResearch.WordTrace tailWord_977578 prefixEnd_977578 148731078892172283045691 := by
  unfold tailWord_977578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8913799713102334468845347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23770132568272891916920925 8913799713102334468845347)
  ·
    refine ⟨13370699569653501703268021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8913799713102334468845347 13370699569653501703268021)
    ·
      refine ⟨1253503084655015784681377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13370699569653501703268021 1253503084655015784681377)
      ·
        refine ⟨940127313491261838511033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1253503084655015784681377 940127313491261838511033)
        ·
          refine ⟨705095485118446378883275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 940127313491261838511033 705095485118446378883275)
          ·
            refine ⟨1057643227677669568324913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705095485118446378883275 1057643227677669568324913)
            ·
              refine ⟨793232420758252176243685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057643227677669568324913 793232420758252176243685)
              ·
                refine ⟨148731078892172283045691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793232420758252176243685 148731078892172283045691)
                ·
                  rfl

theorem cell20_977578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_977578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977578 prefixEnd_977578 := by exact prefixLift 977578
  have htrace : WordTrace (prefixWord ++ tailWord_977578) baseStart_977578 baseEnd_977578 := by
    simpa [prefixWord, tailWord_977578, baseEnd_977578] using wordTrace_append hprefix tailTrace_977578
  have hstable : (prefixWord ++ tailWord_977578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977578).length < 2 ^ (prefixWord ++ tailWord_977578).sum := by decide
  have hdescent : baseEnd_977578 < baseStart_977578 := by decide
  rcases family_descends (prefixWord ++ tailWord_977578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977582 : List Nat := [4, 1, 4, 1, 1, 1, 4, 4]
def baseStart_977582 : Nat := 118140960795 + 977582 * 2 ^ 59
def prefixEnd_977582 : Nat := 4983230072969 + 3 ^ 40 * 977582 * 2
def baseEnd_977582 : Nat := 148731687461836871001241

theorem tailTrace_977582 : CollatzResearch.WordTrace tailWord_977582 prefixEnd_977582 148731687461836871001241 := by
  unfold tailWord_977582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456918093049355819815875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23770229829596564372351333 4456918093049355819815875)
  ·
    refine ⟨6685377139574033729723813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4456918093049355819815875 6685377139574033729723813)
    ·
      refine ⟨1253508213670131324323215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6685377139574033729723813 1253508213670131324323215)
      ·
        refine ⟨1880262320505196986484823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1253508213670131324323215 1880262320505196986484823)
        ·
          refine ⟨2820393480757795479727235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1880262320505196986484823 2820393480757795479727235)
          ·
            refine ⟨4230590221136693219590853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820393480757795479727235 4230590221136693219590853)
            ·
              refine ⟨793235666463129978673285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4230590221136693219590853 793235666463129978673285)
              ·
                refine ⟨148731687461836871001241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793235666463129978673285 148731687461836871001241)
                ·
                  rfl

theorem cell20_977582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_977582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977582 prefixEnd_977582 := by exact prefixLift 977582
  have htrace : WordTrace (prefixWord ++ tailWord_977582) baseStart_977582 baseEnd_977582 := by
    simpa [prefixWord, tailWord_977582, baseEnd_977582] using wordTrace_append hprefix tailTrace_977582
  have hstable : (prefixWord ++ tailWord_977582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977582).length < 2 ^ (prefixWord ++ tailWord_977582).sum := by decide
  have hdescent : baseEnd_977582 < baseStart_977582 := by decide
  rcases family_descends (prefixWord ++ tailWord_977582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977624 : List Nat := [2, 1, 2, 2, 3, 3, 2, 5]
def baseStart_977624 : Nat := 118140960795 + 977624 * 2 ^ 59
def prefixEnd_977624 : Nat := 4983230072969 + 3 ^ 40 * 977624 * 2
def baseEnd_977624 : Nat := 148738077443315044534517

theorem tailTrace_977624 : CollatzResearch.WordTrace tailWord_977624 prefixEnd_977624 148738077443315044534517 := by
  unfold tailWord_977624
  simp only [CollatzResearch.WordTrace]
  refine ⟨17828438305121343865777963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23771251073495125154370617 17828438305121343865777963)
  ·
    refine ⟨26742657457682015798666945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17828438305121343865777963 26742657457682015798666945)
    ·
      refine ⟨20056993093261511849000209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26742657457682015798666945 20056993093261511849000209)
      ·
        refine ⟨15042744819946133886750157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20056993093261511849000209 15042744819946133886750157)
        ·
          refine ⟨5641029307479800207531309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15042744819946133886750157 5641029307479800207531309)
          ·
            refine ⟨2115385990304925077824241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5641029307479800207531309 2115385990304925077824241)
            ·
              refine ⟨1586539492728693808368181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2115385990304925077824241 1586539492728693808368181)
              ·
                refine ⟨148738077443315044534517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1586539492728693808368181 148738077443315044534517)
                ·
                  rfl

theorem cell20_977624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_977624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977624 prefixEnd_977624 := by exact prefixLift 977624
  have htrace : WordTrace (prefixWord ++ tailWord_977624) baseStart_977624 baseEnd_977624 := by
    simpa [prefixWord, tailWord_977624, baseEnd_977624] using wordTrace_append hprefix tailTrace_977624
  have hstable : (prefixWord ++ tailWord_977624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977624).length < 2 ^ (prefixWord ++ tailWord_977624).sum := by decide
  have hdescent : baseEnd_977624 < baseStart_977624 := by decide
  rcases family_descends (prefixWord ++ tailWord_977624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977655 : List Nat := [1, 1, 3, 1, 1, 1, 3, 7, 2]
def baseStart_977655 : Nat := 118140960795 + 977655 * 2 ^ 59
def prefixEnd_977655 : Nat := 4983230072969 + 3 ^ 40 * 977655 * 2
def baseEnd_977655 : Nat := 446228381574646803570091

theorem tailTrace_977655 : CollatzResearch.WordTrace tailWord_977655 prefixEnd_977655 446228381574646803570091 := by
  unfold tailWord_977655
  simp only [CollatzResearch.WordTrace]
  refine ⟨35658007273130380025934419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23772004848753586683956279 35658007273130380025934419)
  ·
    refine ⟨53487010909695570038901629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35658007273130380025934419 53487010909695570038901629)
    ·
      refine ⟨20057629091135838764588111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53487010909695570038901629 20057629091135838764588111)
      ·
        refine ⟨30086443636703758146882167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20057629091135838764588111 30086443636703758146882167)
        ·
          refine ⟨45129665455055637220323251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30086443636703758146882167 45129665455055637220323251)
          ·
            refine ⟨67694498182583455830484877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45129665455055637220323251 67694498182583455830484877)
            ·
              refine ⟨25385436818468795936431829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67694498182583455830484877 25385436818468795936431829)
              ·
                refine ⟨594971175432862404760121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25385436818468795936431829 594971175432862404760121)
                ·
                  refine ⟨446228381574646803570091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594971175432862404760121 446228381574646803570091)
                  ·
                    rfl

theorem cell20_977655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 2].length) (baseStart_977655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977655 prefixEnd_977655 := by exact prefixLift 977655
  have htrace : WordTrace (prefixWord ++ tailWord_977655) baseStart_977655 baseEnd_977655 := by
    simpa [prefixWord, tailWord_977655, baseEnd_977655] using wordTrace_append hprefix tailTrace_977655
  have hstable : (prefixWord ++ tailWord_977655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977655).length < 2 ^ (prefixWord ++ tailWord_977655).sum := by decide
  have hdescent : baseEnd_977655 < baseStart_977655 := by decide
  rcases family_descends (prefixWord ++ tailWord_977655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977662 : List Nat := [4, 2, 2, 1, 2, 9]
def baseStart_977662 : Nat := 118140960795 + 977662 * 2 ^ 59
def prefixEnd_977662 : Nat := 4983230072969 + 3 ^ 40 * 977662 * 2
def baseEnd_977662 : Nat := 16527095428347625568027

theorem tailTrace_977662 : CollatzResearch.WordTrace tailWord_977662 prefixEnd_977662 16527095428347625568027 := by
  unfold tailWord_977662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4457282823013127527679905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23772175056070013480959493 4457282823013127527679905)
  ·
    refine ⟨3342962117259845645759929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4457282823013127527679905 3342962117259845645759929)
    ·
      refine ⟨2507221587944884234319947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3342962117259845645759929 2507221587944884234319947)
      ·
        refine ⟨3760832381917326351479921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507221587944884234319947 3760832381917326351479921)
        ·
          refine ⟨2820624286437994763609941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3760832381917326351479921 2820624286437994763609941)
          ·
            refine ⟨16527095428347625568027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2820624286437994763609941 16527095428347625568027)
            ·
              rfl

theorem cell20_977662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 9].length) (baseStart_977662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977662 prefixEnd_977662 := by exact prefixLift 977662
  have htrace : WordTrace (prefixWord ++ tailWord_977662) baseStart_977662 baseEnd_977662 := by
    simpa [prefixWord, tailWord_977662, baseEnd_977662] using wordTrace_append hprefix tailTrace_977662
  have hstable : (prefixWord ++ tailWord_977662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977662).length < 2 ^ (prefixWord ++ tailWord_977662).sum := by decide
  have hdescent : baseEnd_977662 < baseStart_977662 := by decide
  rcases family_descends (prefixWord ++ tailWord_977662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977672 : List Nat := [2, 1, 3, 2, 2, 3, 1, 4, 2]
def baseStart_977672 : Nat := 118140960795 + 977672 * 2 ^ 59
def prefixEnd_977672 : Nat := 4983230072969 + 3 ^ 40 * 977672 * 2
def baseEnd_977672 : Nat := 446236140837870300003355

theorem tailTrace_977672 : CollatzResearch.WordTrace tailWord_977672 prefixEnd_977672 446236140837870300003355 := by
  unfold tailWord_977672
  simp only [CollatzResearch.WordTrace]
  refine ⟨17829313657034395964651635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23772418209379194619535513 17829313657034395964651635)
  ·
    refine ⟨26743970485551593946977453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17829313657034395964651635 26743970485551593946977453)
    ·
      refine ⟨10028988932081847730116545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26743970485551593946977453 10028988932081847730116545)
      ·
        refine ⟨7521741699061385797587409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10028988932081847730116545 7521741699061385797587409)
        ·
          refine ⟨5641306274296039348190557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7521741699061385797587409 5641306274296039348190557)
          ·
            refine ⟨2115489852861014755571459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5641306274296039348190557 2115489852861014755571459)
            ·
              refine ⟨3173234779291522133357189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115489852861014755571459 3173234779291522133357189)
              ·
                refine ⟨594981521117160400004473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3173234779291522133357189 594981521117160400004473)
                ·
                  refine ⟨446236140837870300003355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 594981521117160400004473 446236140837870300003355)
                  ·
                    rfl

theorem cell20_977672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 2].length) (baseStart_977672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977672 prefixEnd_977672 := by exact prefixLift 977672
  have htrace : WordTrace (prefixWord ++ tailWord_977672) baseStart_977672 baseEnd_977672 := by
    simpa [prefixWord, tailWord_977672, baseEnd_977672] using wordTrace_append hprefix tailTrace_977672
  have hstable : (prefixWord ++ tailWord_977672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977672).length < 2 ^ (prefixWord ++ tailWord_977672).sum := by decide
  have hdescent : baseEnd_977672 < baseStart_977672 := by decide
  rcases family_descends (prefixWord ++ tailWord_977672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977676 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_977676 : Nat := 118140960795 + 977676 * 2 ^ 59
def prefixEnd_977676 : Nat := 4983230072969 + 3 ^ 40 * 977676 * 2
def baseEnd_977676 : Nat := 446237966546864063870005

theorem tailTrace_977676 : CollatzResearch.WordTrace tailWord_977676 prefixEnd_977676 446237966546864063870005 := by
  unfold tailWord_977676
  simp only [CollatzResearch.WordTrace]
  refine ⟨17829386603027150306224441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23772515470702867074965921 17829386603027150306224441)
  ·
    refine ⟨13372039952270362729668331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17829386603027150306224441 13372039952270362729668331)
    ·
      refine ⟨20058059928405544094502497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13372039952270362729668331 20058059928405544094502497)
      ·
        refine ⟨15043544946304158070876873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20058059928405544094502497 15043544946304158070876873)
        ·
          refine ⟨11282658709728118553157655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15043544946304158070876873 11282658709728118553157655)
          ·
            refine ⟨16923988064592177829736483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11282658709728118553157655 16923988064592177829736483)
            ·
              refine ⟨25385982096888266744604725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16923988064592177829736483 25385982096888266744604725)
              ·
                refine ⟨2379935821583275007306693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25385982096888266744604725 2379935821583275007306693)
                ·
                  refine ⟨446237966546864063870005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2379935821583275007306693 446237966546864063870005)
                  ·
                    rfl

theorem cell20_977676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_977676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977676 prefixEnd_977676 := by exact prefixLift 977676
  have htrace : WordTrace (prefixWord ++ tailWord_977676) baseStart_977676 baseEnd_977676 := by
    simpa [prefixWord, tailWord_977676, baseEnd_977676] using wordTrace_append hprefix tailTrace_977676
  have hstable : (prefixWord ++ tailWord_977676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977676).length < 2 ^ (prefixWord ++ tailWord_977676).sum := by decide
  have hdescent : baseEnd_977676 < baseStart_977676 := by decide
  rcases family_descends (prefixWord ++ tailWord_977676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977706 : List Nat := [3, 1, 4, 3, 1, 1, 2, 3, 2]
def baseStart_977706 : Nat := 118140960795 + 977706 * 2 ^ 59
def prefixEnd_977706 : Nat := 4983230072969 + 3 ^ 40 * 977706 * 2
def baseEnd_977706 : Nat := 446251659364317292869883

theorem tailTrace_977706 : CollatzResearch.WordTrace tailWord_977706 prefixEnd_977706 446251659364317292869883 := by
  unfold tailWord_977706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8914966848986403934010243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23773244930630410490693981 8914966848986403934010243)
  ·
    refine ⟨13372450273479605901015365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8914966848986403934010243 13372450273479605901015365)
    ·
      refine ⟨2507334426277426106440381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13372450273479605901015365 2507334426277426106440381)
      ·
        refine ⟨940250409854034789915143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2507334426277426106440381 940250409854034789915143)
        ·
          refine ⟨1410375614781052184872715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940250409854034789915143 1410375614781052184872715)
          ·
            refine ⟨2115563422171578277309073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410375614781052184872715 2115563422171578277309073)
            ·
              refine ⟨1586672566628683707981805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2115563422171578277309073 1586672566628683707981805)
              ·
                refine ⟨595002212485756390493177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1586672566628683707981805 595002212485756390493177)
                ·
                  refine ⟨446251659364317292869883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595002212485756390493177 446251659364317292869883)
                  ·
                    rfl

theorem cell20_977706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_977706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977706 prefixEnd_977706 := by exact prefixLift 977706
  have htrace : WordTrace (prefixWord ++ tailWord_977706) baseStart_977706 baseEnd_977706 := by
    simpa [prefixWord, tailWord_977706, baseEnd_977706] using wordTrace_append hprefix tailTrace_977706
  have hstable : (prefixWord ++ tailWord_977706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977706).length < 2 ^ (prefixWord ++ tailWord_977706).sum := by decide
  have hdescent : baseEnd_977706 < baseStart_977706 := by decide
  rcases family_descends (prefixWord ++ tailWord_977706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977714 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_977714 : Nat := 118140960795 + 977714 * 2 ^ 59
def prefixEnd_977714 : Nat := 4983230072969 + 3 ^ 40 * 977714 * 2
def baseEnd_977714 : Nat := 446255310782304820603183

theorem tailTrace_977714 : CollatzResearch.WordTrace tailWord_977714 prefixEnd_977714 446255310782304820603183 := by
  unfold tailWord_977714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915039794979158275583049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23773439453277755401554797 8915039794979158275583049)
  ·
    refine ⟨6686279846234368706687287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8915039794979158275583049 6686279846234368706687287)
    ·
      refine ⟨10029419769351553060030931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6686279846234368706687287 10029419769351553060030931)
      ·
        refine ⟨15044129654027329590046397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10029419769351553060030931 15044129654027329590046397)
        ·
          refine ⟨5641548620260248596267399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15044129654027329590046397 5641548620260248596267399)
          ·
            refine ⟨8462322930390372894401099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5641548620260248596267399 8462322930390372894401099)
            ·
              refine ⟨12693484395585559341601649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8462322930390372894401099 12693484395585559341601649)
              ·
                refine ⟨9520113296689169506201237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12693484395585559341601649 9520113296689169506201237)
                ·
                  refine ⟨446255310782304820603183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9520113296689169506201237 446255310782304820603183)
                  ·
                    rfl

theorem cell20_977714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_977714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977714 prefixEnd_977714 := by exact prefixLift 977714
  have htrace : WordTrace (prefixWord ++ tailWord_977714) baseStart_977714 baseEnd_977714 := by
    simpa [prefixWord, tailWord_977714, baseEnd_977714] using wordTrace_append hprefix tailTrace_977714
  have hstable : (prefixWord ++ tailWord_977714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977714).length < 2 ^ (prefixWord ++ tailWord_977714).sum := by decide
  have hdescent : baseEnd_977714 < baseStart_977714 := by decide
  rcases family_descends (prefixWord ++ tailWord_977714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977731 : List Nat := [1, 1, 1, 3, 1, 4, 1, 6, 2]
def baseStart_977731 : Nat := 118140960795 + 977731 * 2 ^ 59
def prefixEnd_977731 : Nat := 4983230072969 + 3 ^ 40 * 977731 * 2
def baseEnd_977731 : Nat := 446263070045528317036447

theorem tailTrace_977731 : CollatzResearch.WordTrace tailWord_977731 prefixEnd_977731 446263070045528317036447 := by
  unfold tailWord_977731
  simp only [CollatzResearch.WordTrace]
  refine ⟨35660779220855045005701047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23773852813903363337134031 35660779220855045005701047)
  ·
    refine ⟨53491168831282567508551571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35660779220855045005701047 53491168831282567508551571)
    ·
      refine ⟨80236753246923851262827357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53491168831282567508551571 80236753246923851262827357)
      ·
        refine ⟨30088782467596444223560259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80236753246923851262827357 30088782467596444223560259)
        ·
          refine ⟨45133173701394666335340389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30088782467596444223560259 45133173701394666335340389)
          ·
            refine ⟨8462470069011499937876323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45133173701394666335340389 8462470069011499937876323)
            ·
              refine ⟨12693705103517249906814485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8462470069011499937876323 12693705103517249906814485)
              ·
                refine ⟨595017426727371089381929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12693705103517249906814485 595017426727371089381929)
                ·
                  refine ⟨446263070045528317036447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595017426727371089381929 446263070045528317036447)
                  ·
                    rfl

theorem cell20_977731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 2].length) (baseStart_977731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977731 prefixEnd_977731 := by exact prefixLift 977731
  have htrace : WordTrace (prefixWord ++ tailWord_977731) baseStart_977731 baseEnd_977731 := by
    simpa [prefixWord, tailWord_977731, baseEnd_977731] using wordTrace_append hprefix tailTrace_977731
  have hstable : (prefixWord ++ tailWord_977731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977731).length < 2 ^ (prefixWord ++ tailWord_977731).sum := by decide
  have hdescent : baseEnd_977731 < baseStart_977731 := by decide
  rcases family_descends (prefixWord ++ tailWord_977731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977759 : List Nat := [1, 1, 2, 3, 1, 3, 3, 6]
def baseStart_977759 : Nat := 118140960795 + 977759 * 2 ^ 59
def prefixEnd_977759 : Nat := 4983230072969 + 3 ^ 40 * 977759 * 2
def baseEnd_977759 : Nat := 148758616669494888034333

theorem tailTrace_977759 : CollatzResearch.WordTrace tailWord_977759 prefixEnd_977759 148758616669494888034333 := by
  unfold tailWord_977759
  simp only [CollatzResearch.WordTrace]
  refine ⟨35661800464753605787720331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23774533643169070525146887 35661800464753605787720331)
  ·
    refine ⟨53492700697130408681580497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35661800464753605787720331 53492700697130408681580497)
    ·
      refine ⟨40119525522847806511185373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53492700697130408681580497 40119525522847806511185373)
      ·
        refine ⟨15044822071067927441694515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40119525522847806511185373 15044822071067927441694515)
        ·
          refine ⟨22567233106601891162541773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15044822071067927441694515 22567233106601891162541773)
          ·
            refine ⟨8462712414975709185953165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22567233106601891162541773 8462712414975709185953165)
            ·
              refine ⟨3173517155615890944732437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8462712414975709185953165 3173517155615890944732437)
              ·
                refine ⟨148758616669494888034333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3173517155615890944732437 148758616669494888034333)
                ·
                  rfl

theorem cell20_977759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_977759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977759 prefixEnd_977759 := by exact prefixLift 977759
  have htrace : WordTrace (prefixWord ++ tailWord_977759) baseStart_977759 baseEnd_977759 := by
    simpa [prefixWord, tailWord_977759, baseEnd_977759] using wordTrace_append hprefix tailTrace_977759
  have hstable : (prefixWord ++ tailWord_977759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977759).length < 2 ^ (prefixWord ++ tailWord_977759).sum := by decide
  have hdescent : baseEnd_977759 < baseStart_977759 := by decide
  rcases family_descends (prefixWord ++ tailWord_977759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977782 : List Nat := [5, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_977782 : Nat := 118140960795 + 977782 * 2 ^ 59
def prefixEnd_977782 : Nat := 4983230072969 + 3 ^ 40 * 977782 * 2
def baseEnd_977782 : Nat := 446286347835198806336239

theorem tailTrace_977782 : CollatzResearch.WordTrace tailWord_977782 prefixEnd_977782 446286347835198806336239 := by
  unfold tailWord_977782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2228914958979392544737975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23775092895780187143871733 2228914958979392544737975)
  ·
    refine ⟨3343372438469088817106963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2228914958979392544737975 3343372438469088817106963)
    ·
      refine ⟨5015058657703633225660445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3343372438469088817106963 5015058657703633225660445)
      ·
        refine ⟨1880646996638862459622667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5015058657703633225660445 1880646996638862459622667)
        ·
          refine ⟨2820970494958293689434001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1880646996638862459622667 2820970494958293689434001)
          ·
            refine ⟨2115727871218720267075501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2820970494958293689434001 2115727871218720267075501)
            ·
              refine ⟨793397951707020100153313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2115727871218720267075501 793397951707020100153313)
              ·
                refine ⟨595048463780265075114985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793397951707020100153313 595048463780265075114985)
                ·
                  refine ⟨446286347835198806336239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595048463780265075114985 446286347835198806336239)
                  ·
                    rfl

theorem cell20_977782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_977782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977782 prefixEnd_977782 := by exact prefixLift 977782
  have htrace : WordTrace (prefixWord ++ tailWord_977782) baseStart_977782 baseEnd_977782 := by
    simpa [prefixWord, tailWord_977782, baseEnd_977782] using wordTrace_append hprefix tailTrace_977782
  have hstable : (prefixWord ++ tailWord_977782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977782).length < 2 ^ (prefixWord ++ tailWord_977782).sum := by decide
  have hdescent : baseEnd_977782 < baseStart_977782 := by decide
  rcases family_descends (prefixWord ++ tailWord_977782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977797 : List Nat := [1, 3, 1, 1, 3, 3, 1, 7]
def baseStart_977797 : Nat := 118140960795 + 977797 * 2 ^ 59
def prefixEnd_977797 : Nat := 4983230072969 + 3 ^ 40 * 977797 * 2
def baseEnd_977797 : Nat := 148764398081308473612059

theorem tailTrace_977797 : CollatzResearch.WordTrace tailWord_977797 prefixEnd_977797 148764398081308473612059 := by
  unfold tailWord_977797
  simp only [CollatzResearch.WordTrace]
  refine ⟨35663186438615938277603645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23775457625743958851735763 35663186438615938277603645)
  ·
    refine ⟨13373694914480976854101367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35663186438615938277603645 13373694914480976854101367)
    ·
      refine ⟨20060542371721465281152051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13373694914480976854101367 20060542371721465281152051)
      ·
        refine ⟨30090813557582197921728077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20060542371721465281152051 30090813557582197921728077)
        ·
          refine ⟨11284055084093324220648029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30090813557582197921728077 11284055084093324220648029)
          ·
            refine ⟨4231520656534996582743011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11284055084093324220648029 4231520656534996582743011)
            ·
              refine ⟨6347280984802494874114517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231520656534996582743011 6347280984802494874114517)
              ·
                refine ⟨148764398081308473612059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6347280984802494874114517 148764398081308473612059)
                ·
                  rfl

theorem cell20_977797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_977797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977797 prefixEnd_977797 := by exact prefixLift 977797
  have htrace : WordTrace (prefixWord ++ tailWord_977797) baseStart_977797 baseEnd_977797 := by
    simpa [prefixWord, tailWord_977797, baseEnd_977797] using wordTrace_append hprefix tailTrace_977797
  have hstable : (prefixWord ++ tailWord_977797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977797).length < 2 ^ (prefixWord ++ tailWord_977797).sum := by decide
  have hdescent : baseEnd_977797 < baseStart_977797 := by decide
  rcases family_descends (prefixWord ++ tailWord_977797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977800 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 3]
def baseStart_977800 : Nat := 118140960795 + 977800 * 2 ^ 59
def prefixEnd_977800 : Nat := 4983230072969 + 3 ^ 40 * 977800 * 2
def baseEnd_977800 : Nat := 446294563525670743736165

theorem tailTrace_977800 : CollatzResearch.WordTrace tailWord_977800 prefixEnd_977800 446294563525670743736165 := by
  unfold tailWord_977800
  simp only [CollatzResearch.WordTrace]
  refine ⟨17831647928802534894981427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23775530571736713193308569 17831647928802534894981427)
  ·
    refine ⟨26747471893203802342472141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17831647928802534894981427 26747471893203802342472141)
    ·
      refine ⟨10030301959951425878427053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26747471893203802342472141 10030301959951425878427053)
      ·
        refine ⟨3761363234981784704410145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10030301959951425878427053 3761363234981784704410145)
        ·
          refine ⟨2821022426236338528307609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3761363234981784704410145 2821022426236338528307609)
          ·
            refine ⟨2115766819677253896230707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821022426236338528307609 2115766819677253896230707)
            ·
              refine ⟨3173650229515880844346061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115766819677253896230707 3173650229515880844346061)
              ·
                refine ⟨1190118836068455316629773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3173650229515880844346061 1190118836068455316629773)
                ·
                  refine ⟨446294563525670743736165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190118836068455316629773 446294563525670743736165)
                  ·
                    rfl

theorem cell20_977800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_977800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977800 prefixEnd_977800 := by exact prefixLift 977800
  have htrace : WordTrace (prefixWord ++ tailWord_977800) baseStart_977800 baseEnd_977800 := by
    simpa [prefixWord, tailWord_977800, baseEnd_977800] using wordTrace_append hprefix tailTrace_977800
  have hstable : (prefixWord ++ tailWord_977800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977800).length < 2 ^ (prefixWord ++ tailWord_977800).sum := by decide
  have hdescent : baseEnd_977800 < baseStart_977800 := by decide
  rcases family_descends (prefixWord ++ tailWord_977800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977837 : List Nat := [1, 5, 2, 3, 1, 2, 2, 2, 2]
def baseStart_977837 : Nat := 118140960795 + 977837 * 2 ^ 59
def prefixEnd_977837 : Nat := 4983230072969 + 3 ^ 40 * 977837 * 2
def baseEnd_977837 : Nat := 446311451333863059502681

theorem tailTrace_977837 : CollatzResearch.WordTrace tailWord_977837 prefixEnd_977837 446311451333863059502681 := by
  unfold tailWord_977837
  simp only [CollatzResearch.WordTrace]
  refine ⟨35664645358471025109059765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23776430238980683406039843 35664645358471025109059765)
  ·
    refine ⟨3343560502356658603974353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35664645358471025109059765 3343560502356658603974353)
    ·
      refine ⟨2507670376767493952980765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3343560502356658603974353 2507670376767493952980765)
      ·
        refine ⟨940376391287810232367787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2507670376767493952980765 940376391287810232367787)
        ·
          refine ⟨1410564586931715348551681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940376391287810232367787 1410564586931715348551681)
          ·
            refine ⟨1057923440198786511413761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1410564586931715348551681 1057923440198786511413761)
            ·
              refine ⟨793442580149089883560321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057923440198786511413761 793442580149089883560321)
              ·
                refine ⟨595081935111817412670241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793442580149089883560321 595081935111817412670241)
                ·
                  refine ⟨446311451333863059502681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595081935111817412670241 446311451333863059502681)
                  ·
                    rfl

theorem cell20_977837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_977837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977837 prefixEnd_977837 := by exact prefixLift 977837
  have htrace : WordTrace (prefixWord ++ tailWord_977837) baseStart_977837 baseEnd_977837 := by
    simpa [prefixWord, tailWord_977837, baseEnd_977837] using wordTrace_append hprefix tailTrace_977837
  have hstable : (prefixWord ++ tailWord_977837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977837).length < 2 ^ (prefixWord ++ tailWord_977837).sum := by decide
  have hdescent : baseEnd_977837 < baseStart_977837 := by decide
  rcases family_descends (prefixWord ++ tailWord_977837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977928 : List Nat := [2, 1, 3, 2, 1, 3, 4, 4]
def baseStart_977928 : Nat := 118140960795 + 977928 * 2 ^ 59
def prefixEnd_977928 : Nat := 4983230072969 + 3 ^ 40 * 977928 * 2
def baseEnd_977928 : Nat := 148784328737823729156325

theorem tailTrace_977928 : CollatzResearch.WordTrace tailWord_977928 prefixEnd_977928 148784328737823729156325 := by
  unfold tailWord_977928
  simp only [CollatzResearch.WordTrace]
  refine ⟨17833982200570673825311219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23778642934094231767081625 17833982200570673825311219)
  ·
    refine ⟨26750973300856010737966829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17833982200570673825311219 26750973300856010737966829)
    ·
      refine ⟨10031614987821004026737561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26750973300856010737966829 10031614987821004026737561)
      ·
        refine ⟨7523711240865753020053171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10031614987821004026737561 7523711240865753020053171)
        ·
          refine ⟨11285566861298629530079757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7523711240865753020053171 11285566861298629530079757)
          ·
            refine ⟨4232087572986986073779909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11285566861298629530079757 4232087572986986073779909)
            ·
              refine ⟨793516419935059888833733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4232087572986986073779909 793516419935059888833733)
              ·
                refine ⟨148784328737823729156325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793516419935059888833733 148784328737823729156325)
                ·
                  rfl

theorem cell20_977928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_977928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977928 prefixEnd_977928 := by exact prefixLift 977928
  have htrace : WordTrace (prefixWord ++ tailWord_977928) baseStart_977928 baseEnd_977928 := by
    simpa [prefixWord, tailWord_977928, baseEnd_977928] using wordTrace_append hprefix tailTrace_977928
  have hstable : (prefixWord ++ tailWord_977928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977928).length < 2 ^ (prefixWord ++ tailWord_977928).sum := by decide
  have hdescent : baseEnd_977928 < baseStart_977928 := by decide
  rcases family_descends (prefixWord ++ tailWord_977928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977966 : List Nat := [4, 1, 3, 1, 1, 1, 4, 5]
def baseStart_977966 : Nat := 118140960795 + 977966 * 2 ^ 59
def prefixEnd_977966 : Nat := 4983230072969 + 3 ^ 40 * 977966 * 2
def baseEnd_977966 : Nat := 148790110149637314734051

theorem tailTrace_977966 : CollatzResearch.WordTrace tailWord_977966 prefixEnd_977966 148790110149637314734051 := by
  unfold tailWord_977966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4458668796875460017563219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23779566916669120093670501 4458668796875460017563219)
  ·
    refine ⟨6688003195313190026344829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4458668796875460017563219 6688003195313190026344829)
    ·
      refine ⟨2508001198242446259879311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6688003195313190026344829 2508001198242446259879311)
      ·
        refine ⟨3762001797363669389818967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2508001198242446259879311 3762001797363669389818967)
        ·
          refine ⟨5643002696045504084728451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3762001797363669389818967 5643002696045504084728451)
          ·
            refine ⟨8464504044068256127092677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5643002696045504084728451 8464504044068256127092677)
            ·
              refine ⟨1587094508262798023829877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8464504044068256127092677 1587094508262798023829877)
              ·
                refine ⟨148790110149637314734051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1587094508262798023829877 148790110149637314734051)
                ·
                  rfl

theorem cell20_977966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_977966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977966 prefixEnd_977966 := by exact prefixLift 977966
  have htrace : WordTrace (prefixWord ++ tailWord_977966) baseStart_977966 baseEnd_977966 := by
    simpa [prefixWord, tailWord_977966, baseEnd_977966] using wordTrace_append hprefix tailTrace_977966
  have hstable : (prefixWord ++ tailWord_977966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977966).length < 2 ^ (prefixWord ++ tailWord_977966).sum := by decide
  have hdescent : baseEnd_977966 < baseStart_977966 := by decide
  rcases family_descends (prefixWord ++ tailWord_977966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977994 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_977994 : Nat := 118140960795 + 977994 * 2 ^ 59
def prefixEnd_977994 : Nat := 4983230072969 + 3 ^ 40 * 977994 * 2
def baseEnd_977994 : Nat := 446383110411868291268705

theorem tailTrace_977994 : CollatzResearch.WordTrace tailWord_977994 prefixEnd_977994 446383110411868291268705 := by
  unfold tailWord_977994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8917592904725560230631259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23780247745934827281683357 8917592904725560230631259)
  ·
    refine ⟨13376389357088340345946889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8917592904725560230631259 13376389357088340345946889)
    ·
      refine ⟨10032292017816255259460167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13376389357088340345946889 10032292017816255259460167)
      ·
        refine ⟨15048438026724382889190251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10032292017816255259460167 15048438026724382889190251)
        ·
          refine ⟨22572657040086574333785377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15048438026724382889190251 22572657040086574333785377)
          ·
            refine ⟨16929492780064930750339033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22572657040086574333785377 16929492780064930750339033)
            ·
              refine ⟨12697119585048698062754275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16929492780064930750339033 12697119585048698062754275)
              ·
                refine ⟨19045679377573047094131413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12697119585048698062754275 19045679377573047094131413)
                ·
                  refine ⟨446383110411868291268705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19045679377573047094131413 446383110411868291268705)
                  ·
                    rfl

theorem cell20_977994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_977994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_977994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_977994 prefixEnd_977994 := by exact prefixLift 977994
  have htrace : WordTrace (prefixWord ++ tailWord_977994) baseStart_977994 baseEnd_977994 := by
    simpa [prefixWord, tailWord_977994, baseEnd_977994] using wordTrace_append hprefix tailTrace_977994
  have hstable : (prefixWord ++ tailWord_977994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977994).length < 2 ^ (prefixWord ++ tailWord_977994).sum := by decide
  have hdescent : baseEnd_977994 < baseStart_977994 := by decide
  rcases family_descends (prefixWord ++ tailWord_977994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978006 : List Nat := [5, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_978006 : Nat := 118140960795 + 978006 * 2 ^ 59
def prefixEnd_978006 : Nat := 4983230072969 + 3 ^ 40 * 978006 * 2
def baseEnd_978006 : Nat := 446388587538849582868657

theorem tailTrace_978006 : CollatzResearch.WordTrace tailWord_978006 prefixEnd_978006 446388587538849582868657 := by
  unfold tailWord_978006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229425580928672935747617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23780539529905844647974581 2229425580928672935747617)
  ·
    refine ⟨1672069185696504701810713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2229425580928672935747617 1672069185696504701810713)
    ·
      refine ⟨1254051889272378526358035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1672069185696504701810713 1254051889272378526358035)
      ·
        refine ⟨1881077833908567789537053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254051889272378526358035 1881077833908567789537053)
        ·
          refine ⟨705404187715712921076395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1881077833908567789537053 705404187715712921076395)
          ·
            refine ⟨1058106281573569381614593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705404187715712921076395 1058106281573569381614593)
            ·
              refine ⟨793579711180177036210945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058106281573569381614593 793579711180177036210945)
              ·
                refine ⟨595184783385132777158209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793579711180177036210945 595184783385132777158209)
                ·
                  refine ⟨446388587538849582868657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595184783385132777158209 446388587538849582868657)
                  ·
                    rfl

theorem cell20_978006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_978006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978006 prefixEnd_978006 := by exact prefixLift 978006
  have htrace : WordTrace (prefixWord ++ tailWord_978006) baseStart_978006 baseEnd_978006 := by
    simpa [prefixWord, tailWord_978006, baseEnd_978006] using wordTrace_append hprefix tailTrace_978006
  have hstable : (prefixWord ++ tailWord_978006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978006).length < 2 ^ (prefixWord ++ tailWord_978006).sum := by decide
  have hdescent : baseEnd_978006 < baseStart_978006 := by decide
  rcases family_descends (prefixWord ++ tailWord_978006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978025 : List Nat := [1, 2, 1, 1, 1, 6, 3, 5]
def baseStart_978025 : Nat := 118140960795 + 978025 * 2 ^ 59
def prefixEnd_978025 : Nat := 4983230072969 + 3 ^ 40 * 978025 * 2
def baseEnd_978025 : Nat := 148799086552189987078415

theorem tailTrace_978025 : CollatzResearch.WordTrace tailWord_978025 prefixEnd_978025 148799086552189987078415 := by
  unfold tailWord_978025
  simp only [CollatzResearch.WordTrace]
  refine ⟨35671502281789933216903529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23781001521193288811269019 35671502281789933216903529)
  ·
    refine ⟨26753626711342449912677647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35671502281789933216903529 26753626711342449912677647)
    ·
      refine ⟨40130440067013674869016471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26753626711342449912677647 40130440067013674869016471)
      ·
        refine ⟨60195660100520512303524707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40130440067013674869016471 60195660100520512303524707)
        ·
          refine ⟨90293490150780768455287061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60195660100520512303524707 90293490150780768455287061)
          ·
            refine ⟨4232507350817848521341581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90293490150780768455287061 4232507350817848521341581)
            ·
              refine ⟨1587190256556693195503093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4232507350817848521341581 1587190256556693195503093)
              ·
                refine ⟨148799086552189987078415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1587190256556693195503093 148799086552189987078415)
                ·
                  rfl

theorem cell20_978025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_978025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978025 prefixEnd_978025 := by exact prefixLift 978025
  have htrace : WordTrace (prefixWord ++ tailWord_978025) baseStart_978025 baseEnd_978025 := by
    simpa [prefixWord, tailWord_978025, baseEnd_978025] using wordTrace_append hprefix tailTrace_978025
  have hstable : (prefixWord ++ tailWord_978025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978025).length < 2 ^ (prefixWord ++ tailWord_978025).sum := by decide
  have hdescent : baseEnd_978025 < baseStart_978025 := by decide
  rcases family_descends (prefixWord ++ tailWord_978025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978052 : List Nat := [2, 3, 2, 1, 2, 3, 2, 3, 2]
def baseStart_978052 : Nat := 118140960795 + 978052 * 2 ^ 59
def prefixEnd_978052 : Nat := 4983230072969 + 3 ^ 40 * 978052 * 2
def baseEnd_978052 : Nat := 446409583192277867335135

theorem tailTrace_978052 : CollatzResearch.WordTrace tailWord_978052 prefixEnd_978052 446409583192277867335135 := by
  unfold tailWord_978052
  simp only [CollatzResearch.WordTrace]
  refine ⟨17836243526346058414068205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23781658035128077885424273 17836243526346058414068205)
  ·
    refine ⟨6688591322379771905275577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17836243526346058414068205 6688591322379771905275577)
    ·
      refine ⟨5016443491784828928956683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6688591322379771905275577 5016443491784828928956683)
      ·
        refine ⟨7524665237677243393435025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5016443491784828928956683 7524665237677243393435025)
        ·
          refine ⟨5643498928257932545076269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7524665237677243393435025 5643498928257932545076269)
          ·
            refine ⟨2116312098096724704403601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5643498928257932545076269 2116312098096724704403601)
            ·
              refine ⟨1587234073572543528302701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116312098096724704403601 1587234073572543528302701)
              ·
                refine ⟨595212777589703823113513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1587234073572543528302701 595212777589703823113513)
                ·
                  refine ⟨446409583192277867335135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595212777589703823113513 446409583192277867335135)
                  ·
                    rfl

theorem cell20_978052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_978052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978052 prefixEnd_978052 := by exact prefixLift 978052
  have htrace : WordTrace (prefixWord ++ tailWord_978052) baseStart_978052 baseEnd_978052 := by
    simpa [prefixWord, tailWord_978052, baseEnd_978052] using wordTrace_append hprefix tailTrace_978052
  have hstable : (prefixWord ++ tailWord_978052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978052).length < 2 ^ (prefixWord ++ tailWord_978052).sum := by decide
  have hdescent : baseEnd_978052 < baseStart_978052 := by decide
  rcases family_descends (prefixWord ++ tailWord_978052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978066 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_978066 : Nat := 118140960795 + 978066 * 2 ^ 59
def prefixEnd_978066 : Nat := 4983230072969 + 3 ^ 40 * 978066 * 2
def baseEnd_978066 : Nat := 446415973173756040868411

theorem tailTrace_978066 : CollatzResearch.WordTrace tailWord_978066 prefixEnd_978066 446415973173756040868411 := by
  unfold tailWord_978066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8918249418660349304786513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23781998449760931479430701 8918249418660349304786513)
  ·
    refine ⟨6688687063995261978589885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8918249418660349304786513 6688687063995261978589885)
    ·
      refine ⟨2508257648998223241971207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6688687063995261978589885 2508257648998223241971207)
      ·
        refine ⟨3762386473497334862956811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2508257648998223241971207 3762386473497334862956811)
        ·
          refine ⟨5643579710246002294435217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3762386473497334862956811 5643579710246002294435217)
          ·
            refine ⟨4232684782684501720826413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5643579710246002294435217 4232684782684501720826413)
            ·
              refine ⟨1587256793506688145309905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4232684782684501720826413 1587256793506688145309905)
              ·
                refine ⟨1190442595130016108982429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587256793506688145309905 1190442595130016108982429)
                ·
                  refine ⟨446415973173756040868411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190442595130016108982429 446415973173756040868411)
                  ·
                    rfl

theorem cell20_978066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_978066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978066 prefixEnd_978066 := by exact prefixLift 978066
  have htrace : WordTrace (prefixWord ++ tailWord_978066) baseStart_978066 baseEnd_978066 := by
    simpa [prefixWord, tailWord_978066, baseEnd_978066] using wordTrace_append hprefix tailTrace_978066
  have hstable : (prefixWord ++ tailWord_978066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978066).length < 2 ^ (prefixWord ++ tailWord_978066).sum := by decide
  have hdescent : baseEnd_978066 < baseStart_978066 := by decide
  rcases family_descends (prefixWord ++ tailWord_978066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978097 : List Nat := [1, 2, 2, 5, 1, 3, 2, 4]
def baseStart_978097 : Nat := 118140960795 + 978097 * 2 ^ 59
def prefixEnd_978097 : Nat := 4983230072969 + 3 ^ 40 * 978097 * 2
def baseEnd_978097 : Nat := 148810040806152570278317

theorem tailTrace_978097 : CollatzResearch.WordTrace tailWord_978097 prefixEnd_978097 148810040806152570278317 := by
  unfold tailWord_978097
  simp only [CollatzResearch.WordTrace]
  refine ⟨35674128337529089513524545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23782752225019393009016363 35674128337529089513524545)
  ·
    refine ⟨26755596253146817135143409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35674128337529089513524545 26755596253146817135143409)
    ·
      refine ⟨20066697189860112851357557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26755596253146817135143409 20066697189860112851357557)
      ·
        refine ⟨1881252861549385579814771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20066697189860112851357557 1881252861549385579814771)
        ·
          refine ⟨2821879292324078369722157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881252861549385579814771 2821879292324078369722157)
          ·
            refine ⟨1058204734621529388645809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2821879292324078369722157 1058204734621529388645809)
            ·
              refine ⟨793653550966147041484357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058204734621529388645809 793653550966147041484357)
              ·
                refine ⟨148810040806152570278317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793653550966147041484357 148810040806152570278317)
                ·
                  rfl

theorem cell20_978097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 4].length) (baseStart_978097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978097 prefixEnd_978097 := by exact prefixLift 978097
  have htrace : WordTrace (prefixWord ++ tailWord_978097) baseStart_978097 baseEnd_978097 := by
    simpa [prefixWord, tailWord_978097, baseEnd_978097] using wordTrace_append hprefix tailTrace_978097
  have hstable : (prefixWord ++ tailWord_978097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978097).length < 2 ^ (prefixWord ++ tailWord_978097).sum := by decide
  have hdescent : baseEnd_978097 < baseStart_978097 := by decide
  rcases family_descends (prefixWord ++ tailWord_978097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978111 : List Nat := [1, 1, 2, 2, 2, 2, 5, 3, 2]
def baseStart_978111 : Nat := 118140960795 + 978111 * 2 ^ 59
def prefixEnd_978111 : Nat := 4983230072969 + 3 ^ 40 * 978111 * 2
def baseEnd_978111 : Nat := 446436512399935884368227

theorem tailTrace_978111 : CollatzResearch.WordTrace tailWord_978111 prefixEnd_978111 446436512399935884368227 := by
  unfold tailWord_978111
  simp only [CollatzResearch.WordTrace]
  refine ⟨35674638959478369904534187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23783092639652246603022791 35674638959478369904534187)
  ·
    refine ⟨53511958439217554856801281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35674638959478369904534187 53511958439217554856801281)
    ·
      refine ⟨40133968829413166142600961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53511958439217554856801281 40133968829413166142600961)
      ·
        refine ⟨30100476622059874606950721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40133968829413166142600961 30100476622059874606950721)
        ·
          refine ⟨22575357466544905955213041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30100476622059874606950721 22575357466544905955213041)
          ·
            refine ⟨16931518099908679466409781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22575357466544905955213041 16931518099908679466409781)
            ·
              refine ⟨1587329821866438699975917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16931518099908679466409781 1587329821866438699975917)
              ·
                refine ⟨595248683199914512490969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1587329821866438699975917 595248683199914512490969)
                ·
                  refine ⟨446436512399935884368227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595248683199914512490969 446436512399935884368227)
                  ·
                    rfl

theorem cell20_978111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 2].length) (baseStart_978111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978111 prefixEnd_978111 := by exact prefixLift 978111
  have htrace : WordTrace (prefixWord ++ tailWord_978111) baseStart_978111 baseEnd_978111 := by
    simpa [prefixWord, tailWord_978111, baseEnd_978111] using wordTrace_append hprefix tailTrace_978111
  have hstable : (prefixWord ++ tailWord_978111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978111).length < 2 ^ (prefixWord ++ tailWord_978111).sum := by decide
  have hdescent : baseEnd_978111 < baseStart_978111 := by decide
  rcases family_descends (prefixWord ++ tailWord_978111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978114 : List Nat := [3, 5, 1, 1, 2, 2, 6]
def baseStart_978114 : Nat := 118140960795 + 978114 * 2 ^ 59
def prefixEnd_978114 : Nat := 4983230072969 + 3 ^ 40 * 978114 * 2
def baseEnd_978114 : Nat := 49604209075742356363135

theorem tailTrace_978114 : CollatzResearch.WordTrace tailWord_978114 prefixEnd_978114 49604209075742356363135 := by
  unfold tailWord_978114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8918687094616875354223349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23783165585645000944595597 8918687094616875354223349)
  ·
    refine ⟨836126915120332064458439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8918687094616875354223349 836126915120332064458439)
    ·
      refine ⟨1254190372680498096687659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836126915120332064458439 1254190372680498096687659)
      ·
        refine ⟨1881285559020747145031489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254190372680498096687659 1881285559020747145031489)
        ·
          refine ⟨1410964169265560358773617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1881285559020747145031489 1410964169265560358773617)
          ·
            refine ⟨1058223126949170269080213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1410964169265560358773617 1058223126949170269080213)
            ·
              refine ⟨49604209075742356363135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1058223126949170269080213 49604209075742356363135)
              ·
                rfl

theorem cell20_978114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 6].length) (baseStart_978114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978114 prefixEnd_978114 := by exact prefixLift 978114
  have htrace : WordTrace (prefixWord ++ tailWord_978114) baseStart_978114 baseEnd_978114 := by
    simpa [prefixWord, tailWord_978114, baseEnd_978114] using wordTrace_append hprefix tailTrace_978114
  have hstable : (prefixWord ++ tailWord_978114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978114).length < 2 ^ (prefixWord ++ tailWord_978114).sum := by decide
  have hdescent : baseEnd_978114 < baseStart_978114 := by decide
  rcases family_descends (prefixWord ++ tailWord_978114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978180 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 3]
def baseStart_978180 : Nat := 118140960795 + 978180 * 2 ^ 59
def prefixEnd_978180 : Nat := 4983230072969 + 3 ^ 40 * 978180 * 2
def baseEnd_978180 : Nat := 446468005880078311067945

theorem tailTrace_978180 : CollatzResearch.WordTrace tailWord_978180 prefixEnd_978180 446468005880078311067945 := by
  unfold tailWord_978180
  simp only [CollatzResearch.WordTrace]
  refine ⟨17838577798114197344397997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23784770397485596459197329 17838577798114197344397997)
  ·
    refine ⟨6689466674292824004149249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17838577798114197344397997 6689466674292824004149249)
    ·
      refine ⟨5017100005719618003111937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6689466674292824004149249 5017100005719618003111937)
      ·
        refine ⟨3762825004289713502333953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5017100005719618003111937 3762825004289713502333953)
        ·
          refine ⟨2822118753217285126750465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3762825004289713502333953 2822118753217285126750465)
          ·
            refine ⟨2116589064912963845062849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2822118753217285126750465 2116589064912963845062849)
            ·
              refine ⟨1587441798684722883797137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116589064912963845062849 1587441798684722883797137)
              ·
                refine ⟨1190581349013542162847853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587441798684722883797137 1190581349013542162847853)
                ·
                  refine ⟨446468005880078311067945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190581349013542162847853 446468005880078311067945)
                  ·
                    rfl

theorem cell20_978180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_978180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978180 prefixEnd_978180 := by exact prefixLift 978180
  have htrace : WordTrace (prefixWord ++ tailWord_978180) baseStart_978180 baseEnd_978180 := by
    simpa [prefixWord, tailWord_978180, baseEnd_978180] using wordTrace_append hprefix tailTrace_978180
  have hstable : (prefixWord ++ tailWord_978180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978180).length < 2 ^ (prefixWord ++ tailWord_978180).sum := by decide
  have hdescent : baseEnd_978180 < baseStart_978180 := by decide
  rcases family_descends (prefixWord ++ tailWord_978180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978187 : List Nat := [1, 1, 1, 1, 5, 4, 1, 4, 2]
def baseStart_978187 : Nat := 118140960795 + 978187 * 2 ^ 59
def prefixEnd_978187 : Nat := 4983230072969 + 3 ^ 40 * 978187 * 2
def baseEnd_978187 : Nat := 446471200870817397834583

theorem tailTrace_978187 : CollatzResearch.WordTrace tailWord_978187 prefixEnd_978187 446471200870817397834583 := by
  unfold tailWord_978187
  simp only [CollatzResearch.WordTrace]
  refine ⟨35677410907203034884300815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23784940604802023256200543 35677410907203034884300815)
  ·
    refine ⟨53516116360804552326451223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35677410907203034884300815 53516116360804552326451223)
    ·
      refine ⟨80274174541206828489676835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53516116360804552326451223 80274174541206828489676835)
      ·
        refine ⟨120411261811810242734515253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80274174541206828489676835 120411261811810242734515253)
        ·
          refine ⟨11288555794857210256360805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120411261811810242734515253 11288555794857210256360805)
          ·
            refine ⟨2116604211535726923067651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11288555794857210256360805 2116604211535726923067651)
            ·
              refine ⟨3174906317303590384601477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116604211535726923067651 3174906317303590384601477)
              ·
                refine ⟨595294934494423197112777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3174906317303590384601477 595294934494423197112777)
                ·
                  refine ⟨446471200870817397834583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595294934494423197112777 446471200870817397834583)
                  ·
                    rfl

theorem cell20_978187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 2].length) (baseStart_978187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978187 prefixEnd_978187 := by exact prefixLift 978187
  have htrace : WordTrace (prefixWord ++ tailWord_978187) baseStart_978187 baseEnd_978187 := by
    simpa [prefixWord, tailWord_978187, baseEnd_978187] using wordTrace_append hprefix tailTrace_978187
  have hstable : (prefixWord ++ tailWord_978187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978187).length < 2 ^ (prefixWord ++ tailWord_978187).sum := by decide
  have hdescent : baseEnd_978187 < baseStart_978187 := by decide
  rcases family_descends (prefixWord ++ tailWord_978187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978221 : List Nat := [1, 5, 3, 1, 1, 2, 2, 3, 2]
def baseStart_978221 : Nat := 118140960795 + 978221 * 2 ^ 59
def prefixEnd_978221 : Nat := 4983230072969 + 3 ^ 40 * 978221 * 2
def baseEnd_978221 : Nat := 446486719397264390701111

theorem tailTrace_978221 : CollatzResearch.WordTrace tailWord_978221 prefixEnd_978221 446486719397264390701111 := by
  unfold tailWord_978221
  simp only [CollatzResearch.WordTrace]
  refine ⟨35678650989079858691038517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23785767326053239127359011 35678650989079858691038517)
  ·
    refine ⟨3344873530226236752284861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35678650989079858691038517 3344873530226236752284861)
    ·
      refine ⟨1254327573834838782106823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3344873530226236752284861 1254327573834838782106823)
      ·
        refine ⟨1881491360752258173160235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254327573834838782106823 1881491360752258173160235)
        ·
          refine ⟨2822237041128387259740353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881491360752258173160235 2822237041128387259740353)
          ·
            refine ⟨2116677780846290444805265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2822237041128387259740353 2116677780846290444805265)
            ·
              refine ⟨1587508335634717833603949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116677780846290444805265 1587508335634717833603949)
              ·
                refine ⟨595315625863019187601481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1587508335634717833603949 595315625863019187601481)
                ·
                  refine ⟨446486719397264390701111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595315625863019187601481 446486719397264390701111)
                  ·
                    rfl

theorem cell20_978221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_978221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978221 prefixEnd_978221 := by exact prefixLift 978221
  have htrace : WordTrace (prefixWord ++ tailWord_978221) baseStart_978221 baseEnd_978221 := by
    simpa [prefixWord, tailWord_978221, baseEnd_978221] using wordTrace_append hprefix tailTrace_978221
  have hstable : (prefixWord ++ tailWord_978221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978221).length < 2 ^ (prefixWord ++ tailWord_978221).sum := by decide
  have hdescent : baseEnd_978221 < baseStart_978221 := by decide
  rcases family_descends (prefixWord ++ tailWord_978221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978225 : List Nat := [1, 2, 2, 3, 3, 1, 1, 5, 2]
def baseStart_978225 : Nat := 118140960795 + 978225 * 2 ^ 59
def prefixEnd_978225 : Nat := 4983230072969 + 3 ^ 40 * 978225 * 2
def baseEnd_978225 : Nat := 446488545106258154567761

theorem tailTrace_978225 : CollatzResearch.WordTrace tailWord_978225 prefixEnd_978225 446488545106258154567761 := by
  unfold tailWord_978225
  simp only [CollatzResearch.WordTrace]
  refine ⟨35678796881065367374184129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23785864587376911582789419 35678796881065367374184129)
  ·
    refine ⟨26759097660799025530638097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35678796881065367374184129 26759097660799025530638097)
    ·
      refine ⟨20069323245599269147978573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26759097660799025530638097 20069323245599269147978573)
      ·
        refine ⟨7525996217099725930491965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20069323245599269147978573 7525996217099725930491965)
        ·
          refine ⟨2822248581412397223934487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7525996217099725930491965 2822248581412397223934487)
          ·
            refine ⟨4233372872118595835901731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822248581412397223934487 4233372872118595835901731)
            ·
              refine ⟨6350059308177893753852597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233372872118595835901731 6350059308177893753852597)
              ·
                refine ⟨595318060141677539423681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6350059308177893753852597 595318060141677539423681)
                ·
                  refine ⟨446488545106258154567761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595318060141677539423681 446488545106258154567761)
                  ·
                    rfl

theorem cell20_978225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 5, 2].length) (baseStart_978225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978225 prefixEnd_978225 := by exact prefixLift 978225
  have htrace : WordTrace (prefixWord ++ tailWord_978225) baseStart_978225 baseEnd_978225 := by
    simpa [prefixWord, tailWord_978225, baseEnd_978225] using wordTrace_append hprefix tailTrace_978225
  have hstable : (prefixWord ++ tailWord_978225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978225).length < 2 ^ (prefixWord ++ tailWord_978225).sum := by decide
  have hdescent : baseEnd_978225 < baseStart_978225 := by decide
  rcases family_descends (prefixWord ++ tailWord_978225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978239 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 3]
def baseStart_978239 : Nat := 118140960795 + 978239 * 2 ^ 59
def prefixEnd_978239 : Nat := 4983230072969 + 3 ^ 40 * 978239 * 2
def baseEnd_978239 : Nat := 446494935087736328101037

theorem tailTrace_978239 : CollatzResearch.WordTrace tailWord_978239 prefixEnd_978239 446494935087736328101037 := by
  unfold tailWord_978239
  simp only [CollatzResearch.WordTrace]
  refine ⟨35679307503014647765193771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23786205002009765176795847 35679307503014647765193771)
  ·
    refine ⟨53518961254521971647790657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35679307503014647765193771 53518961254521971647790657)
    ·
      refine ⟨40139220940891478735842993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53518961254521971647790657 40139220940891478735842993)
      ·
        refine ⟨30104415705668609051882245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40139220940891478735842993 30104415705668609051882245)
        ·
          refine ⟨5644577944812864197227921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30104415705668609051882245 5644577944812864197227921)
          ·
            refine ⟨4233433458609648147920941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5644577944812864197227921 4233433458609648147920941)
            ·
              refine ⟨1587537546978618055470353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4233433458609648147920941 1587537546978618055470353)
              ·
                refine ⟨1190653160233963541602765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587537546978618055470353 1190653160233963541602765)
                ·
                  refine ⟨446494935087736328101037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190653160233963541602765 446494935087736328101037)
                  ·
                    rfl

theorem cell20_978239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 3].length) (baseStart_978239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978239 prefixEnd_978239 := by exact prefixLift 978239
  have htrace : WordTrace (prefixWord ++ tailWord_978239) baseStart_978239 baseEnd_978239 := by
    simpa [prefixWord, tailWord_978239, baseEnd_978239] using wordTrace_append hprefix tailTrace_978239
  have hstable : (prefixWord ++ tailWord_978239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978239).length < 2 ^ (prefixWord ++ tailWord_978239).sum := by decide
  have hdescent : baseEnd_978239 < baseStart_978239 := by decide
  rcases family_descends (prefixWord ++ tailWord_978239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978262 : List Nat := [5, 2, 3, 1, 1, 2, 2, 4]
def baseStart_978262 : Nat := 118140960795 + 978262 * 2 ^ 59
def prefixEnd_978262 : Nat := 4983230072969 + 3 ^ 40 * 978262 * 2
def baseEnd_978262 : Nat := 148835144304816823444759

theorem tailTrace_978262 : CollatzResearch.WordTrace tailWord_978262 prefixEnd_978262 148835144304816823444759 := by
  unfold tailWord_978262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230009148870707668330065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23786764254620881795520693 2230009148870707668330065)
  ·
    refine ⟨1672506861653030751247549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2230009148870707668330065 1672506861653030751247549)
    ·
      refine ⟨627190073119886531717831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1672506861653030751247549 627190073119886531717831)
      ·
        refine ⟨940785109679829797576747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627190073119886531717831 940785109679829797576747)
        ·
          refine ⟨1411177664519744696365121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940785109679829797576747 1411177664519744696365121)
          ·
            refine ⟨1058383248389808522273841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411177664519744696365121 1058383248389808522273841)
            ·
              refine ⟨793787436292356391705381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058383248389808522273841 793787436292356391705381)
              ·
                refine ⟨148835144304816823444759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793787436292356391705381 148835144304816823444759)
                ·
                  rfl

theorem cell20_978262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_978262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978262 prefixEnd_978262 := by exact prefixLift 978262
  have htrace : WordTrace (prefixWord ++ tailWord_978262) baseStart_978262 baseEnd_978262 := by
    simpa [prefixWord, tailWord_978262, baseEnd_978262] using wordTrace_append hprefix tailTrace_978262
  have hstable : (prefixWord ++ tailWord_978262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978262).length < 2 ^ (prefixWord ++ tailWord_978262).sum := by decide
  have hdescent : baseEnd_978262 < baseStart_978262 := by decide
  rcases family_descends (prefixWord ++ tailWord_978262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978350 : List Nat := [4, 1, 15]
def baseStart_978350 : Nat := 118140960795 + 978350 * 2 ^ 59
def prefixEnd_978350 : Nat := 4983230072969 + 3 ^ 40 * 978350 * 2
def baseEnd_978350 : Nat := 612545402623200652127

theorem tailTrace_978350 : CollatzResearch.WordTrace tailWord_978350 prefixEnd_978350 612545402623200652127 := by
  unfold tailWord_978350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4460419500701564215310563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23788904003741675814989669 4460419500701564215310563)
  ·
    refine ⟨6690629251052346322965845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4460419500701564215310563 6690629251052346322965845)
    ·
      refine ⟨612545402623200652127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 6690629251052346322965845 612545402623200652127)
      ·
        rfl

theorem cell20_978350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 15].length) (baseStart_978350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978350 prefixEnd_978350 := by exact prefixLift 978350
  have htrace : WordTrace (prefixWord ++ tailWord_978350) baseStart_978350 baseEnd_978350 := by
    simpa [prefixWord, tailWord_978350, baseEnd_978350] using wordTrace_append hprefix tailTrace_978350
  have hstable : (prefixWord ++ tailWord_978350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978350).length < 2 ^ (prefixWord ++ tailWord_978350).sum := by decide
  have hdescent : baseEnd_978350 < baseStart_978350 := by decide
  rcases family_descends (prefixWord ++ tailWord_978350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978353 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 3]
def baseStart_978353 : Nat := 118140960795 + 978353 * 2 ^ 59
def prefixEnd_978353 : Nat := 4983230072969 + 3 ^ 40 * 978353 * 2
def baseEnd_978353 : Nat := 446546967794058598300571

theorem tailTrace_978353 : CollatzResearch.WordTrace tailWord_978353 prefixEnd_978353 446546967794058598300571 := by
  unfold tailWord_978353
  simp only [CollatzResearch.WordTrace]
  refine ⟨35683465424601645234843713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23788976949734430156562475 35683465424601645234843713)
  ·
    refine ⟨26762599068451233926132785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35683465424601645234843713 26762599068451233926132785)
    ·
      refine ⟨20071949301338425444599589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26762599068451233926132785 20071949301338425444599589)
      ·
        refine ⟨3763490494000954770862423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20071949301338425444599589 3763490494000954770862423)
        ·
          refine ⟨5645235741001432156293635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763490494000954770862423 5645235741001432156293635)
          ·
            refine ⟨8467853611502148234440453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5645235741001432156293635 8467853611502148234440453)
            ·
              refine ⟨1587722552156652793957585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8467853611502148234440453 1587722552156652793957585)
              ·
                refine ⟨1190791914117489595468189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587722552156652793957585 1190791914117489595468189)
                ·
                  refine ⟨446546967794058598300571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190791914117489595468189 446546967794058598300571)
                  ·
                    rfl

theorem cell20_978353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_978353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978353 prefixEnd_978353 := by exact prefixLift 978353
  have htrace : WordTrace (prefixWord ++ tailWord_978353) baseStart_978353 baseEnd_978353 := by
    simpa [prefixWord, tailWord_978353, baseEnd_978353] using wordTrace_append hprefix tailTrace_978353
  have hstable : (prefixWord ++ tailWord_978353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978353).length < 2 ^ (prefixWord ++ tailWord_978353).sum := by decide
  have hdescent : baseEnd_978353 < baseStart_978353 := by decide
  rcases family_descends (prefixWord ++ tailWord_978353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978395 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_978395 : Nat := 118140960795 + 978395 * 2 ^ 59
def prefixEnd_978395 : Nat := 4983230072969 + 3 ^ 40 * 978395 * 2
def baseEnd_978395 : Nat := 446566137738493118900399

theorem tailTrace_978395 : CollatzResearch.WordTrace tailWord_978395 prefixEnd_978395 446566137738493118900399 := by
  unfold tailWord_978395
  simp only [CollatzResearch.WordTrace]
  refine ⟨35684997290449486407872639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23789998193632990938581759 35684997290449486407872639)
  ·
    refine ⟨53527495935674229611808959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35684997290449486407872639 53527495935674229611808959)
    ·
      refine ⟨80291243903511344417713439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53527495935674229611808959 80291243903511344417713439)
      ·
        refine ⟨120436865855267016626570159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80291243903511344417713439 120436865855267016626570159)
        ·
          refine ⟨180655298782900524939855239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120436865855267016626570159 180655298782900524939855239)
          ·
            refine ⟨270982948174350787409782859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180655298782900524939855239 270982948174350787409782859)
            ·
              refine ⟨406474422261526181114674289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270982948174350787409782859 406474422261526181114674289)
              ·
                refine ⟨304855816696144635836005717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406474422261526181114674289 304855816696144635836005717)
                ·
                  refine ⟨446566137738493118900399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 304855816696144635836005717 446566137738493118900399)
                  ·
                    rfl

theorem cell20_978395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_978395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978395 prefixEnd_978395 := by exact prefixLift 978395
  have htrace : WordTrace (prefixWord ++ tailWord_978395) baseStart_978395 baseEnd_978395 := by
    simpa [prefixWord, tailWord_978395, baseEnd_978395] using wordTrace_append hprefix tailTrace_978395
  have hstable : (prefixWord ++ tailWord_978395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978395).length < 2 ^ (prefixWord ++ tailWord_978395).sum := by decide
  have hdescent : baseEnd_978395 < baseStart_978395 := by decide
  rcases family_descends (prefixWord ++ tailWord_978395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978405 : List Nat := [1, 3, 1, 5, 1, 2, 7]
def baseStart_978405 : Nat := 118140960795 + 978405 * 2 ^ 59
def prefixEnd_978405 : Nat := 4983230072969 + 3 ^ 40 * 978405 * 2
def baseEnd_978405 : Nat := 49618966890108614285225

theorem tailTrace_978405 : CollatzResearch.WordTrace tailWord_978405 prefixEnd_978405 49618966890108614285225 := by
  unfold tailWord_978405
  simp only [CollatzResearch.WordTrace]
  refine ⟨35685362020413258115736669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23790241346942172077157779 35685362020413258115736669)
  ·
    refine ⟨13382010757654971793401251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35685362020413258115736669 13382010757654971793401251)
    ·
      refine ⟨20073016136482457690101877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13382010757654971793401251 20073016136482457690101877)
      ·
        refine ⟨1881845262795230408447051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20073016136482457690101877 1881845262795230408447051)
        ·
          refine ⟨2822767894192845612670577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881845262795230408447051 2822767894192845612670577)
          ·
            refine ⟨2117075920644634209502933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2822767894192845612670577 2117075920644634209502933)
            ·
              refine ⟨49618966890108614285225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2117075920644634209502933 49618966890108614285225)
              ·
                rfl

theorem cell20_978405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 7].length) (baseStart_978405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978405 prefixEnd_978405 := by exact prefixLift 978405
  have htrace : WordTrace (prefixWord ++ tailWord_978405) baseStart_978405 baseEnd_978405 := by
    simpa [prefixWord, tailWord_978405, baseEnd_978405] using wordTrace_append hprefix tailTrace_978405
  have hstable : (prefixWord ++ tailWord_978405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978405).length < 2 ^ (prefixWord ++ tailWord_978405).sum := by decide
  have hdescent : baseEnd_978405 < baseStart_978405 := by decide
  rcases family_descends (prefixWord ++ tailWord_978405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978412 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 3]
def baseStart_978412 : Nat := 118140960795 + 978412 * 2 ^ 59
def prefixEnd_978412 : Nat := 4983230072969 + 3 ^ 40 * 978412 * 2
def baseEnd_978412 : Nat := 446573897001716615333663

theorem tailTrace_978412 : CollatzResearch.WordTrace tailWord_978412 prefixEnd_978412 446573897001716615333663 := by
  unfold tailWord_978412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17842808665693949155620745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23790411554258598874160993 17842808665693949155620745)
  ·
    refine ⟨13382106499270461866715559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17842808665693949155620745 13382106499270461866715559)
    ·
      refine ⟨20073159748905692800073339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13382106499270461866715559 20073159748905692800073339)
      ·
        refine ⟨30109739623358539200110009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20073159748905692800073339 30109739623358539200110009)
        ·
          refine ⟨22582304717518904400082507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30109739623358539200110009 22582304717518904400082507)
          ·
            refine ⟨33873457076278356600123761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22582304717518904400082507 33873457076278356600123761)
            ·
              refine ⟨25405092807208767450092821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33873457076278356600123761 25405092807208767450092821)
              ·
                refine ⟨1190863725337910974223101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25405092807208767450092821 1190863725337910974223101)
                ·
                  refine ⟨446573897001716615333663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190863725337910974223101 446573897001716615333663)
                  ·
                    rfl

theorem cell20_978412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_978412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978412 prefixEnd_978412 := by exact prefixLift 978412
  have htrace : WordTrace (prefixWord ++ tailWord_978412) baseStart_978412 baseEnd_978412 := by
    simpa [prefixWord, tailWord_978412, baseEnd_978412] using wordTrace_append hprefix tailTrace_978412
  have hstable : (prefixWord ++ tailWord_978412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978412).length < 2 ^ (prefixWord ++ tailWord_978412).sum := by decide
  have hdescent : baseEnd_978412 < baseStart_978412 := by decide
  rcases family_descends (prefixWord ++ tailWord_978412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978426 : List Nat := [3, 1, 1, 1, 1, 2, 4, 7]
def baseStart_978426 : Nat := 118140960795 + 978426 * 2 ^ 59
def prefixEnd_978426 : Nat := 4983230072969 + 3 ^ 40 * 978426 * 2
def baseEnd_978426 : Nat := 148860095661064929622313

theorem tailTrace_978426 : CollatzResearch.WordTrace tailWord_978426 prefixEnd_978426 148860095661064929622313 := by
  unfold tailWord_978426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8921531988334294675562783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23790751968891452468167421 8921531988334294675562783)
  ·
    refine ⟨13382297982501442013344175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8921531988334294675562783 13382297982501442013344175)
    ·
      refine ⟨20073446973752163020016263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13382297982501442013344175 20073446973752163020016263)
      ·
        refine ⟨30110170460628244530024395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20073446973752163020016263 30110170460628244530024395)
        ·
          refine ⟨45165255690942366795036593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30110170460628244530024395 45165255690942366795036593)
          ·
            refine ⟨33873941768206775096277445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45165255690942366795036593 33873941768206775096277445)
            ·
              refine ⟨6351364081538770330552021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33873941768206775096277445 6351364081538770330552021)
              ·
                refine ⟨148860095661064929622313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6351364081538770330552021 148860095661064929622313)
                ·
                  rfl

theorem cell20_978426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_978426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978426 prefixEnd_978426 := by exact prefixLift 978426
  have htrace : WordTrace (prefixWord ++ tailWord_978426) baseStart_978426 baseEnd_978426 := by
    simpa [prefixWord, tailWord_978426, baseEnd_978426] using wordTrace_append hprefix tailTrace_978426
  have hstable : (prefixWord ++ tailWord_978426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978426).length < 2 ^ (prefixWord ++ tailWord_978426).sum := by decide
  have hdescent : baseEnd_978426 < baseStart_978426 := by decide
  rcases family_descends (prefixWord ++ tailWord_978426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978443 : List Nat := [1, 1, 1, 1, 8, 1, 1, 6]
def baseStart_978443 : Nat := 118140960795 + 978443 * 2 ^ 59
def prefixEnd_978443 : Nat := 4983230072969 + 3 ^ 40 * 978443 * 2
def baseEnd_978443 : Nat := 148862682082139428433401

theorem tailTrace_978443 : CollatzResearch.WordTrace tailWord_978443 prefixEnd_978443 148862682082139428433401 := by
  unfold tailWord_978443
  simp only [CollatzResearch.WordTrace]
  refine ⟨35686747994275590605619983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23791165329517060403746655 35686747994275590605619983)
  ·
    refine ⟨53530121991413385908429975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35686747994275590605619983 53530121991413385908429975)
    ·
      refine ⟨80295182987120078862644963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53530121991413385908429975 80295182987120078862644963)
      ·
        refine ⟨120442774480680118293967445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80295182987120078862644963 120442774480680118293967445)
        ·
          refine ⟨1411438763445470136257431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 120442774480680118293967445 1411438763445470136257431)
          ·
            refine ⟨2117158145168205204386147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411438763445470136257431 2117158145168205204386147)
            ·
              refine ⟨3175737217752307806579221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117158145168205204386147 3175737217752307806579221)
              ·
                refine ⟨148862682082139428433401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3175737217752307806579221 148862682082139428433401)
                ·
                  rfl

theorem cell20_978443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 6].length) (baseStart_978443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978443 prefixEnd_978443 := by exact prefixLift 978443
  have htrace : WordTrace (prefixWord ++ tailWord_978443) baseStart_978443 baseEnd_978443 := by
    simpa [prefixWord, tailWord_978443, baseEnd_978443] using wordTrace_append hprefix tailTrace_978443
  have hstable : (prefixWord ++ tailWord_978443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978443).length < 2 ^ (prefixWord ++ tailWord_978443).sum := by decide
  have hdescent : baseEnd_978443 < baseStart_978443 := by decide
  rcases family_descends (prefixWord ++ tailWord_978443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978445 : List Nat := [1, 7, 1, 1, 3, 1, 1, 3, 2]
def baseStart_978445 : Nat := 118140960795 + 978445 * 2 ^ 59
def prefixEnd_978445 : Nat := 4983230072969 + 3 ^ 40 * 978445 * 2
def baseEnd_978445 : Nat := 446588959100915167233529

theorem tailTrace_978445 : CollatzResearch.WordTrace tailWord_978445 prefixEnd_978445 446588959100915167233529 := by
  unfold tailWord_978445
  simp only [CollatzResearch.WordTrace]
  refine ⟨35686820940268344947192789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23791213960178896631461859 35686820940268344947192789)
  ·
    refine ⟨836409865787539334699831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 35686820940268344947192789 836409865787539334699831)
    ·
      refine ⟨1254614798681309002049747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836409865787539334699831 1254614798681309002049747)
      ·
        refine ⟨1881922198021963503074621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254614798681309002049747 1881922198021963503074621)
        ·
          refine ⟨705720824258236313652983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1881922198021963503074621 705720824258236313652983)
          ·
            refine ⟨1058581236387354470479475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705720824258236313652983 1058581236387354470479475)
            ·
              refine ⟨1587871854581031705719213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058581236387354470479475 1587871854581031705719213)
              ·
                refine ⟨595451945467886889644705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1587871854581031705719213 595451945467886889644705)
                ·
                  refine ⟨446588959100915167233529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595451945467886889644705 446588959100915167233529)
                  ·
                    rfl

theorem cell20_978445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_978445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978445 prefixEnd_978445 := by exact prefixLift 978445
  have htrace : WordTrace (prefixWord ++ tailWord_978445) baseStart_978445 baseEnd_978445 := by
    simpa [prefixWord, tailWord_978445, baseEnd_978445] using wordTrace_append hprefix tailTrace_978445
  have hstable : (prefixWord ++ tailWord_978445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978445).length < 2 ^ (prefixWord ++ tailWord_978445).sum := by decide
  have hdescent : baseEnd_978445 < baseStart_978445 := by decide
  rcases family_descends (prefixWord ++ tailWord_978445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978453 : List Nat := [1, 3, 2, 1, 3, 2, 3, 3, 2]
def baseStart_978453 : Nat := 118140960795 + 978453 * 2 ^ 59
def prefixEnd_978453 : Nat := 4983230072969 + 3 ^ 40 * 978453 * 2
def baseEnd_978453 : Nat := 446592610518902694966829

theorem tailTrace_978453 : CollatzResearch.WordTrace tailWord_978453 prefixEnd_978453 446592610518902694966829 := by
  unfold tailWord_978453
  simp only [CollatzResearch.WordTrace]
  refine ⟨35687112724239362313484013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23791408482826241542322675 35687112724239362313484013)
  ·
    refine ⟨13382667271589760867556505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35687112724239362313484013 13382667271589760867556505)
    ·
      refine ⟨10037000453692320650667379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13382667271589760867556505 10037000453692320650667379)
      ·
        refine ⟨15055500680538480976001069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037000453692320650667379 15055500680538480976001069)
        ·
          refine ⟨5645812755201930366000401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15055500680538480976001069 5645812755201930366000401)
          ·
            refine ⟨4234359566401447774500301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5645812755201930366000401 4234359566401447774500301)
            ·
              refine ⟨1587884837400542915437613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4234359566401447774500301 1587884837400542915437613)
              ·
                refine ⟨595456814025203593289105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1587884837400542915437613 595456814025203593289105)
                ·
                  refine ⟨446592610518902694966829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595456814025203593289105 446592610518902694966829)
                  ·
                    rfl

theorem cell20_978453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_978453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978453 prefixEnd_978453 := by exact prefixLift 978453
  have htrace : WordTrace (prefixWord ++ tailWord_978453) baseStart_978453 baseEnd_978453 := by
    simpa [prefixWord, tailWord_978453, baseEnd_978453] using wordTrace_append hprefix tailTrace_978453
  have hstable : (prefixWord ++ tailWord_978453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978453).length < 2 ^ (prefixWord ++ tailWord_978453).sum := by decide
  have hdescent : baseEnd_978453 < baseStart_978453 := by decide
  rcases family_descends (prefixWord ++ tailWord_978453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978512 : List Nat := [2, 1, 1, 1, 1, 3, 4, 5, 2]
def baseStart_978512 : Nat := 118140960795 + 978512 * 2 ^ 59
def prefixEnd_978512 : Nat := 4983230072969 + 3 ^ 40 * 978512 * 2
def baseEnd_978512 : Nat := 446619539726560711999921

theorem tailTrace_978512 : CollatzResearch.WordTrace tailWord_978512 prefixEnd_978512 446619539726560711999921 := by
  unfold tailWord_978512
  simp only [CollatzResearch.WordTrace]
  refine ⟨17844632315512807694940895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23792843087350410259921193 17844632315512807694940895)
  ·
    refine ⟨26766948473269211542411343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17844632315512807694940895 26766948473269211542411343)
    ·
      refine ⟨40150422709903817313617015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26766948473269211542411343 40150422709903817313617015)
      ·
        refine ⟨60225634064855725970425523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40150422709903817313617015 60225634064855725970425523)
        ·
          refine ⟨90338451097283588955638285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60225634064855725970425523 90338451097283588955638285)
          ·
            refine ⟨33876919161481345858364357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90338451097283588955638285 33876919161481345858364357)
            ·
              refine ⟨6351922342777752348443317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33876919161481345858364357 6351922342777752348443317)
              ·
                refine ⟨595492719635414282666561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6351922342777752348443317 595492719635414282666561)
                ·
                  refine ⟨446619539726560711999921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595492719635414282666561 446619539726560711999921)
                  ·
                    rfl

theorem cell20_978512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 2].length) (baseStart_978512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978512 prefixEnd_978512 := by exact prefixLift 978512
  have htrace : WordTrace (prefixWord ++ tailWord_978512) baseStart_978512 baseEnd_978512 := by
    simpa [prefixWord, tailWord_978512, baseEnd_978512] using wordTrace_append hprefix tailTrace_978512
  have hstable : (prefixWord ++ tailWord_978512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978512).length < 2 ^ (prefixWord ++ tailWord_978512).sum := by decide
  have hdescent : baseEnd_978512 < baseStart_978512 := by decide
  rcases family_descends (prefixWord ++ tailWord_978512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978518 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_978518 : Nat := 118140960795 + 978518 * 2 ^ 59
def prefixEnd_978518 : Nat := 4983230072969 + 3 ^ 40 * 978518 * 2
def baseEnd_978518 : Nat := 446622278290051357799897

theorem tailTrace_978518 : CollatzResearch.WordTrace tailWord_978518 prefixEnd_978518 446622278290051357799897 := by
  unfold tailWord_978518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230592716812742400912513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23792988979335918943066805 2230592716812742400912513)
  ·
    refine ⟨1672944537609556800684385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2230592716812742400912513 1672944537609556800684385)
    ·
      refine ⟨1254708403207167600513289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1672944537609556800684385 1254708403207167600513289)
      ·
        refine ⟨941031302405375700384967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1254708403207167600513289 941031302405375700384967)
        ·
          refine ⟨1411546953608063550577451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941031302405375700384967 1411546953608063550577451)
          ·
            refine ⟨2117320430412095325866177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411546953608063550577451 2117320430412095325866177)
            ·
              refine ⟨1587990322809071494399633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117320430412095325866177 1587990322809071494399633)
              ·
                refine ⟨1190992742106803620799725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587990322809071494399633 1190992742106803620799725)
                ·
                  refine ⟨446622278290051357799897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1190992742106803620799725 446622278290051357799897)
                  ·
                    rfl

theorem cell20_978518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_978518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978518 prefixEnd_978518 := by exact prefixLift 978518
  have htrace : WordTrace (prefixWord ++ tailWord_978518) baseStart_978518 baseEnd_978518 := by
    simpa [prefixWord, tailWord_978518, baseEnd_978518] using wordTrace_append hprefix tailTrace_978518
  have hstable : (prefixWord ++ tailWord_978518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978518).length < 2 ^ (prefixWord ++ tailWord_978518).sum := by decide
  have hdescent : baseEnd_978518 < baseStart_978518 := by decide
  rcases family_descends (prefixWord ++ tailWord_978518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978525 : List Nat := [1, 4, 4, 2, 1, 1, 1, 4, 2]
def baseStart_978525 : Nat := 118140960795 + 978525 * 2 ^ 59
def prefixEnd_978525 : Nat := 4983230072969 + 3 ^ 40 * 978525 * 2
def baseEnd_978525 : Nat := 446625473280790444566535

theorem tailTrace_978525 : CollatzResearch.WordTrace tailWord_978525 prefixEnd_978525 446625473280790444566535 := by
  unfold tailWord_978525
  simp only [CollatzResearch.WordTrace]
  refine ⟨35689738779978518610105029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23793159186652345740070019 35689738779978518610105029)
  ·
    refine ⟨6691826021245972239394693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35689738779978518610105029 6691826021245972239394693)
    ·
      refine ⟨1254717378983619794886505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6691826021245972239394693 1254717378983619794886505)
      ·
        refine ⟨941038034237714846164879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1254717378983619794886505 941038034237714846164879)
        ·
          refine ⟨1411557051356572269247319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941038034237714846164879 1411557051356572269247319)
          ·
            refine ⟨2117335577034858403870979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411557051356572269247319 2117335577034858403870979)
            ·
              refine ⟨3176003365552287605806469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117335577034858403870979 3176003365552287605806469)
              ·
                refine ⟨595500631041053926088713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3176003365552287605806469 595500631041053926088713)
                ·
                  refine ⟨446625473280790444566535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595500631041053926088713 446625473280790444566535)
                  ·
                    rfl

theorem cell20_978525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_978525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978525 prefixEnd_978525 := by exact prefixLift 978525
  have htrace : WordTrace (prefixWord ++ tailWord_978525) baseStart_978525 baseEnd_978525 := by
    simpa [prefixWord, tailWord_978525, baseEnd_978525] using wordTrace_append hprefix tailTrace_978525
  have hstable : (prefixWord ++ tailWord_978525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978525).length < 2 ^ (prefixWord ++ tailWord_978525).sum := by decide
  have hdescent : baseEnd_978525 < baseStart_978525 := by decide
  rcases family_descends (prefixWord ++ tailWord_978525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978536 : List Nat := [2, 1, 4, 3, 1, 3, 1, 5]
def baseStart_978536 : Nat := 118140960795 + 978536 * 2 ^ 59
def prefixEnd_978536 : Nat := 4983230072969 + 3 ^ 40 * 978536 * 2
def baseEnd_978536 : Nat := 148876831326841098399941

theorem tailTrace_978536 : CollatzResearch.WordTrace tailWord_978536 prefixEnd_978536 148876831326841098399941 := by
  unfold tailWord_978536
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845069991469333744377731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23793426655292444992503641 17845069991469333744377731)
  ·
    refine ⟨26767604987204000616566597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17845069991469333744377731 26767604987204000616566597)
    ·
      refine ⟨5018925935100750115606237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26767604987204000616566597 5018925935100750115606237)
      ·
        refine ⟨1882097225662781293352339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5018925935100750115606237 1882097225662781293352339)
        ·
          refine ⟨2823145838494171940028509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1882097225662781293352339 2823145838494171940028509)
          ·
            refine ⟨1058679689435314477510691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2823145838494171940028509 1058679689435314477510691)
            ·
              refine ⟨1588019534152971716266037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058679689435314477510691 1588019534152971716266037)
              ·
                refine ⟨148876831326841098399941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1588019534152971716266037 148876831326841098399941)
                ·
                  rfl

theorem cell20_978536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_978536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978536 prefixEnd_978536 := by exact prefixLift 978536
  have htrace : WordTrace (prefixWord ++ tailWord_978536) baseStart_978536 baseEnd_978536 := by
    simpa [prefixWord, tailWord_978536, baseEnd_978536] using wordTrace_append hprefix tailTrace_978536
  have hstable : (prefixWord ++ tailWord_978536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978536).length < 2 ^ (prefixWord ++ tailWord_978536).sum := by decide
  have hdescent : baseEnd_978536 < baseStart_978536 := by decide
  rcases family_descends (prefixWord ++ tailWord_978536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978550 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_978550 : Nat := 118140960795 + 978550 * 2 ^ 59
def prefixEnd_978550 : Nat := 4983230072969 + 3 ^ 40 * 978550 * 2
def baseEnd_978550 : Nat := 446636883962001468733099

theorem tailTrace_978550 : CollatzResearch.WordTrace tailWord_978550 prefixEnd_978550 446636883962001468733099 := by
  unfold tailWord_978550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230665662805496742485319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23793767069925298586510069 2230665662805496742485319)
  ·
    refine ⟨3345998494208245113727979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2230665662805496742485319 3345998494208245113727979)
    ·
      refine ⟨5018997741312367670591969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3345998494208245113727979 5018997741312367670591969)
      ·
        refine ⟨3764248305984275752943977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5018997741312367670591969 3764248305984275752943977)
        ·
          refine ⟨2823186229488206814707983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3764248305984275752943977 2823186229488206814707983)
          ·
            refine ⟨4234779344232310222061975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2823186229488206814707983 4234779344232310222061975)
            ·
              refine ⟨6352169016348465333092963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234779344232310222061975 6352169016348465333092963)
              ·
                refine ⟨9528253524522697999639445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352169016348465333092963 9528253524522697999639445)
                ·
                  refine ⟨446636883962001468733099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9528253524522697999639445 446636883962001468733099)
                  ·
                    rfl

theorem cell20_978550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_978550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978550 prefixEnd_978550 := by exact prefixLift 978550
  have htrace : WordTrace (prefixWord ++ tailWord_978550) baseStart_978550 baseEnd_978550 := by
    simpa [prefixWord, tailWord_978550, baseEnd_978550] using wordTrace_append hprefix tailTrace_978550
  have hstable : (prefixWord ++ tailWord_978550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978550).length < 2 ^ (prefixWord ++ tailWord_978550).sum := by decide
  have hdescent : baseEnd_978550 < baseStart_978550 := by decide
  rcases family_descends (prefixWord ++ tailWord_978550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978567 : List Nat := [1, 1, 4, 2, 1, 4, 2, 3, 2]
def baseStart_978567 : Nat := 118140960795 + 978567 * 2 ^ 59
def prefixEnd_978567 : Nat := 4983230072969 + 3 ^ 40 * 978567 * 2
def baseEnd_978567 : Nat := 446644643225224965166363

theorem tailTrace_978567 : CollatzResearch.WordTrace tailWord_978567 prefixEnd_978567 446644643225224965166363 := by
  unfold tailWord_978567
  simp only [CollatzResearch.WordTrace]
  refine ⟨35691270645826359783133955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23794180430550906522089303 35691270645826359783133955)
  ·
    refine ⟨53536905968739539674700933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35691270645826359783133955 53536905968739539674700933)
    ·
      refine ⟨10038169869138663689006425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53536905968739539674700933 10038169869138663689006425)
      ·
        refine ⟨7528627401853997766754819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10038169869138663689006425 7528627401853997766754819)
        ·
          refine ⟨11292941102780996650132229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7528627401853997766754819 11292941102780996650132229)
          ·
            refine ⟨2117426456771436871899793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11292941102780996650132229 2117426456771436871899793)
            ·
              refine ⟨1588069842578577653924845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117426456771436871899793 1588069842578577653924845)
              ·
                refine ⟨595526190966966620221817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1588069842578577653924845 595526190966966620221817)
                ·
                  refine ⟨446644643225224965166363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595526190966966620221817 446644643225224965166363)
                  ·
                    rfl

theorem cell20_978567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 2].length) (baseStart_978567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978567 prefixEnd_978567 := by exact prefixLift 978567
  have htrace : WordTrace (prefixWord ++ tailWord_978567) baseStart_978567 baseEnd_978567 := by
    simpa [prefixWord, tailWord_978567, baseEnd_978567] using wordTrace_append hprefix tailTrace_978567
  have hstable : (prefixWord ++ tailWord_978567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978567).length < 2 ^ (prefixWord ++ tailWord_978567).sum := by decide
  have hdescent : baseEnd_978567 < baseStart_978567 := by decide
  rcases family_descends (prefixWord ++ tailWord_978567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978622 : List Nat := [4, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_978622 : Nat := 118140960795 + 978622 * 2 ^ 59
def prefixEnd_978622 : Nat := 4983230072969 + 3 ^ 40 * 978622 * 2
def baseEnd_978622 : Nat := 446669746723889218332805

theorem tailTrace_978622 : CollatzResearch.WordTrace tailWord_978622 prefixEnd_978622 446669746723889218332805 := by
  unfold tailWord_978622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4461659582578388022048265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23795517773751402784257413 4461659582578388022048265)
  ·
    refine ⟨3346244686933791016536199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4461659582578388022048265 3346244686933791016536199)
    ·
      refine ⟨5019367030400686524804299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3346244686933791016536199 5019367030400686524804299)
      ·
        refine ⟨7529050545601029787206449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5019367030400686524804299 7529050545601029787206449)
        ·
          refine ⟨5646787909200772340404837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7529050545601029787206449 5646787909200772340404837)
          ·
            refine ⟨1058772732975144813825907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5646787909200772340404837 1058772732975144813825907)
            ·
              refine ⟨1588159099462717220738861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058772732975144813825907 1588159099462717220738861)
              ·
                refine ⟨595559662298518957777073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1588159099462717220738861 595559662298518957777073)
                ·
                  refine ⟨446669746723889218332805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595559662298518957777073 446669746723889218332805)
                  ·
                    rfl

theorem cell20_978622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_978622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978622 prefixEnd_978622 := by exact prefixLift 978622
  have htrace : WordTrace (prefixWord ++ tailWord_978622) baseStart_978622 baseEnd_978622 := by
    simpa [prefixWord, tailWord_978622, baseEnd_978622] using wordTrace_append hprefix tailTrace_978622
  have hstable : (prefixWord ++ tailWord_978622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978622).length < 2 ^ (prefixWord ++ tailWord_978622).sum := by decide
  have hdescent : baseEnd_978622 < baseStart_978622 := by decide
  rcases family_descends (prefixWord ++ tailWord_978622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978623 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_978623 : Nat := 118140960795 + 978623 * 2 ^ 59
def prefixEnd_978623 : Nat := 4983230072969 + 3 ^ 40 * 978623 * 2
def baseEnd_978623 : Nat := 446670203151137659299467

theorem tailTrace_978623 : CollatzResearch.WordTrace tailWord_978623 prefixEnd_978623 446670203151137659299467 := by
  unfold tailWord_978623
  simp only [CollatzResearch.WordTrace]
  refine ⟨35693313133623481347172523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23795542089082320898115015 35693313133623481347172523)
  ·
    refine ⟨53539969700435222020758785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35693313133623481347172523 53539969700435222020758785)
    ·
      refine ⟨40154977275326416515569089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53539969700435222020758785 40154977275326416515569089)
      ·
        refine ⟨30116232956494812386676817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40154977275326416515569089 30116232956494812386676817)
        ·
          refine ⟨22587174717371109290007613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30116232956494812386676817 22587174717371109290007613)
          ·
            refine ⟨8470190519014165983752855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22587174717371109290007613 8470190519014165983752855)
            ·
              refine ⟨12705285778521248975629283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8470190519014165983752855 12705285778521248975629283)
              ·
                refine ⟨19057928667781873463443925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12705285778521248975629283 19057928667781873463443925)
                ·
                  refine ⟨446670203151137659299467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19057928667781873463443925 446670203151137659299467)
                  ·
                    rfl

theorem cell20_978623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_978623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978623 prefixEnd_978623 := by exact prefixLift 978623
  have htrace : WordTrace (prefixWord ++ tailWord_978623) baseStart_978623 baseEnd_978623 := by
    simpa [prefixWord, tailWord_978623, baseEnd_978623] using wordTrace_append hprefix tailTrace_978623
  have hstable : (prefixWord ++ tailWord_978623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978623).length < 2 ^ (prefixWord ++ tailWord_978623).sum := by decide
  have hdescent : baseEnd_978623 < baseStart_978623 := by decide
  rcases family_descends (prefixWord ++ tailWord_978623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978657 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 3]
def baseStart_978657 : Nat := 118140960795 + 978657 * 2 ^ 59
def prefixEnd_978657 : Nat := 4983230072969 + 3 ^ 40 * 978657 * 2
def baseEnd_978657 : Nat := 446685721677584652165995

theorem tailTrace_978657 : CollatzResearch.WordTrace tailWord_978657 prefixEnd_978657 446685721677584652165995 := by
  unfold tailWord_978657
  simp only [CollatzResearch.WordTrace]
  refine ⟨35694553215500305153910225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23796368810333536769273483 35694553215500305153910225)
  ·
    refine ⟨26770914911625228865432669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35694553215500305153910225 26770914911625228865432669)
    ·
      refine ⟨10039093091859460824537251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26770914911625228865432669 10039093091859460824537251)
      ·
        refine ⟨15058639637789191236805877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10039093091859460824537251 15058639637789191236805877)
        ·
          refine ⟨1411747466042736678450551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15058639637789191236805877 1411747466042736678450551)
          ·
            refine ⟨2117621199064105017675827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411747466042736678450551 2117621199064105017675827)
            ·
              refine ⟨3176431798596157526513741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117621199064105017675827 3176431798596157526513741)
              ·
                refine ⟨1191161924473559072442653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3176431798596157526513741 1191161924473559072442653)
                ·
                  refine ⟨446685721677584652165995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191161924473559072442653 446685721677584652165995)
                  ·
                    rfl

theorem cell20_978657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_978657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978657 prefixEnd_978657 := by exact prefixLift 978657
  have htrace : WordTrace (prefixWord ++ tailWord_978657) baseStart_978657 baseEnd_978657 := by
    simpa [prefixWord, tailWord_978657, baseEnd_978657] using wordTrace_append hprefix tailTrace_978657
  have hstable : (prefixWord ++ tailWord_978657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978657).length < 2 ^ (prefixWord ++ tailWord_978657).sum := by decide
  have hdescent : baseEnd_978657 < baseStart_978657 := by decide
  rcases family_descends (prefixWord ++ tailWord_978657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978692 : List Nat := [2, 3, 2, 2, 1, 10]
def baseStart_978692 : Nat := 118140960795 + 978692 * 2 ^ 59
def prefixEnd_978692 : Nat := 4983230072969 + 3 ^ 40 * 978692 * 2
def baseEnd_978692 : Nat := 16544507282640003185155

theorem tailTrace_978692 : CollatzResearch.WordTrace tailWord_978692 prefixEnd_978692 16544507282640003185155 := by
  unfold tailWord_978692
  simp only [CollatzResearch.WordTrace]
  refine ⟨17847914885186753065717165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23797219846915670754289553 17847914885186753065717165)
  ·
    refine ⟨6692968081945032399643937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17847914885186753065717165 6692968081945032399643937)
    ·
      refine ⟨5019726061458774299732953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6692968081945032399643937 5019726061458774299732953)
      ·
        refine ⟨3764794546094080724799715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5019726061458774299732953 3764794546094080724799715)
        ·
          refine ⟨5647191819141121087199573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3764794546094080724799715 5647191819141121087199573)
          ·
            refine ⟨16544507282640003185155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5647191819141121087199573 16544507282640003185155)
            ·
              rfl

theorem cell20_978692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 10].length) (baseStart_978692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978692 prefixEnd_978692 := by exact prefixLift 978692
  have htrace : WordTrace (prefixWord ++ tailWord_978692) baseStart_978692 baseEnd_978692 := by
    simpa [prefixWord, tailWord_978692, baseEnd_978692] using wordTrace_append hprefix tailTrace_978692
  have hstable : (prefixWord ++ tailWord_978692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978692).length < 2 ^ (prefixWord ++ tailWord_978692).sum := by decide
  have hdescent : baseEnd_978692 < baseStart_978692 := by decide
  rcases family_descends (prefixWord ++ tailWord_978692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978698 : List Nat := [3, 1, 2, 2, 1, 5, 2, 2, 2]
def baseStart_978698 : Nat := 118140960795 + 978698 * 2 ^ 59
def prefixEnd_978698 : Nat := 4983230072969 + 3 ^ 40 * 978698 * 2
def baseEnd_978698 : Nat := 446704435194770731799161

theorem tailTrace_978698 : CollatzResearch.WordTrace tailWord_978698 prefixEnd_978698 446704435194770731799161 := by
  unfold tailWord_978698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8924012152087942289038187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23797365738901179437435165 8924012152087942289038187)
  ·
    refine ⟨13386018228131913433557281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8924012152087942289038187 13386018228131913433557281)
    ·
      refine ⟨10039513671098935075167961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13386018228131913433557281 10039513671098935075167961)
      ·
        refine ⟨7529635253324201306375971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10039513671098935075167961 7529635253324201306375971)
        ·
          refine ⟨11294452879986301959563957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7529635253324201306375971 11294452879986301959563957)
          ·
            refine ⟨1058854957498715808709121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11294452879986301959563957 1058854957498715808709121)
            ·
              refine ⟨794141218124036856531841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058854957498715808709121 794141218124036856531841)
              ·
                refine ⟨595605913593027642398881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794141218124036856531841 595605913593027642398881)
                ·
                  refine ⟨446704435194770731799161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595605913593027642398881 446704435194770731799161)
                  ·
                    rfl

theorem cell20_978698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_978698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978698 prefixEnd_978698 := by exact prefixLift 978698
  have htrace : WordTrace (prefixWord ++ tailWord_978698) baseStart_978698 baseEnd_978698 := by
    simpa [prefixWord, tailWord_978698, baseEnd_978698] using wordTrace_append hprefix tailTrace_978698
  have hstable : (prefixWord ++ tailWord_978698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978698).length < 2 ^ (prefixWord ++ tailWord_978698).sum := by decide
  have hdescent : baseEnd_978698 < baseStart_978698 := by decide
  rcases family_descends (prefixWord ++ tailWord_978698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978699 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_978699 : Nat := 118140960795 + 978699 * 2 ^ 59
def prefixEnd_978699 : Nat := 4983230072969 + 3 ^ 40 * 978699 * 2
def baseEnd_978699 : Nat := 446704891622019172765823

theorem tailTrace_978699 : CollatzResearch.WordTrace tailWord_978699 prefixEnd_978699 446704891622019172765823 := by
  unfold tailWord_978699
  simp only [CollatzResearch.WordTrace]
  refine ⟨35696085081348146326939151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23797390054232097551292767 35696085081348146326939151)
  ·
    refine ⟨53544127622022219490408727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35696085081348146326939151 53544127622022219490408727)
    ·
      refine ⟨80316191433033329235613091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53544127622022219490408727 80316191433033329235613091)
      ·
        refine ⟨120474287149549993853419637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80316191433033329235613091 120474287149549993853419637)
        ·
          refine ⟨11294464420270311923758091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120474287149549993853419637 11294464420270311923758091)
          ·
            refine ⟨16941696630405467885637137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11294464420270311923758091 16941696630405467885637137)
            ·
              refine ⟨12706272472804100914227853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16941696630405467885637137 12706272472804100914227853)
              ·
                refine ⟨4764852177301537842835445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12706272472804100914227853 4764852177301537842835445)
                ·
                  refine ⟨446704891622019172765823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4764852177301537842835445 446704891622019172765823)
                  ·
                    rfl

theorem cell20_978699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_978699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978699 prefixEnd_978699 := by exact prefixLift 978699
  have htrace : WordTrace (prefixWord ++ tailWord_978699) baseStart_978699 baseEnd_978699 := by
    simpa [prefixWord, tailWord_978699, baseEnd_978699] using wordTrace_append hprefix tailTrace_978699
  have hstable : (prefixWord ++ tailWord_978699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978699).length < 2 ^ (prefixWord ++ tailWord_978699).sum := by decide
  have hdescent : baseEnd_978699 < baseStart_978699 := by decide
  rcases family_descends (prefixWord ++ tailWord_978699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978701 : List Nat := [1, 7, 2, 1, 1, 2, 1, 5]
def baseStart_978701 : Nat := 118140960795 + 978701 * 2 ^ 59
def prefixEnd_978701 : Nat := 4983230072969 + 3 ^ 40 * 978701 * 2
def baseEnd_978701 : Nat := 148901934825505351566383

theorem tailTrace_978701 : CollatzResearch.WordTrace tailWord_978701 prefixEnd_978701 148901934825505351566383 := by
  unfold tailWord_978701
  simp only [CollatzResearch.WordTrace]
  refine ⟨35696158027340900668511957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23797438684893933779007971 35696158027340900668511957)
  ·
    refine ⟨836628703765802359418249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 35696158027340900668511957 836628703765802359418249)
    ·
      refine ⟨627471527824351769563687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 836628703765802359418249 627471527824351769563687)
      ·
        refine ⟨941207291736527654345531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627471527824351769563687 941207291736527654345531)
        ·
          refine ⟨1411810937604791481518297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941207291736527654345531 1411810937604791481518297)
          ·
            refine ⟨1058858203203593611138723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411810937604791481518297 1058858203203593611138723)
            ·
              refine ⟨1588287304805390416708085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058858203203593611138723 1588287304805390416708085)
              ·
                refine ⟨148901934825505351566383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1588287304805390416708085 148901934825505351566383)
                ·
                  rfl

theorem cell20_978701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 5].length) (baseStart_978701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978701 prefixEnd_978701 := by exact prefixLift 978701
  have htrace : WordTrace (prefixWord ++ tailWord_978701) baseStart_978701 baseEnd_978701 := by
    simpa [prefixWord, tailWord_978701, baseEnd_978701] using wordTrace_append hprefix tailTrace_978701
  have hstable : (prefixWord ++ tailWord_978701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978701).length < 2 ^ (prefixWord ++ tailWord_978701).sum := by decide
  have hdescent : baseEnd_978701 < baseStart_978701 := by decide
  rcases family_descends (prefixWord ++ tailWord_978701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978709 : List Nat := [1, 3, 2, 1, 2, 5, 1, 5]
def baseStart_978709 : Nat := 118140960795 + 978709 * 2 ^ 59
def prefixEnd_978709 : Nat := 4983230072969 + 3 ^ 40 * 978709 * 2
def baseEnd_978709 : Nat := 148903151964834527477483

theorem tailTrace_978709 : CollatzResearch.WordTrace tailWord_978709 prefixEnd_978709 148903151964834527477483 := by
  unfold tailWord_978709
  simp only [CollatzResearch.WordTrace]
  refine ⟨35696449811311918034803181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23797633207541278689868787 35696449811311918034803181)
  ·
    refine ⟨13386168679241969263051193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35696449811311918034803181 13386168679241969263051193)
    ·
      refine ⟨10039626509431476947288395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13386168679241969263051193 10039626509431476947288395)
      ·
        refine ⟨15059439764147215420932593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10039626509431476947288395 15059439764147215420932593)
        ·
          refine ⟨11294579823110411565699445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15059439764147215420932593 11294579823110411565699445)
          ·
            refine ⟨1058866858416601084284323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11294579823110411565699445 1058866858416601084284323)
            ·
              refine ⟨1588300287624901626426485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058866858416601084284323 1588300287624901626426485)
              ·
                refine ⟨148903151964834527477483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1588300287624901626426485 148903151964834527477483)
                ·
                  rfl

theorem cell20_978709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 5].length) (baseStart_978709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978709 prefixEnd_978709 := by exact prefixLift 978709
  have htrace : WordTrace (prefixWord ++ tailWord_978709) baseStart_978709 baseEnd_978709 := by
    simpa [prefixWord, tailWord_978709, baseEnd_978709] using wordTrace_append hprefix tailTrace_978709
  have hstable : (prefixWord ++ tailWord_978709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978709).length < 2 ^ (prefixWord ++ tailWord_978709).sum := by decide
  have hdescent : baseEnd_978709 < baseStart_978709 := by decide
  rcases family_descends (prefixWord ++ tailWord_978709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978716 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 3]
def baseStart_978716 : Nat := 118140960795 + 978716 * 2 ^ 59
def prefixEnd_978716 : Nat := 4983230072969 + 3 ^ 40 * 978716 * 2
def baseEnd_978716 : Nat := 446712650885242669199087

theorem tailTrace_978716 : CollatzResearch.WordTrace tailWord_978716 prefixEnd_978716 446712650885242669199087 := by
  unfold tailWord_978716
  simp only [CollatzResearch.WordTrace]
  refine ⟨17848352561143279115154001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23797803414857705486872001 17848352561143279115154001)
  ·
    refine ⟨13386264420857459336365501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17848352561143279115154001 13386264420857459336365501)
    ·
      refine ⟨5019849157821547251137063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13386264420857459336365501 5019849157821547251137063)
      ·
        refine ⟨7529773736732320876705595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5019849157821547251137063 7529773736732320876705595)
        ·
          refine ⟨11294660605098481315058393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7529773736732320876705595 11294660605098481315058393)
          ·
            refine ⟨8470995453823860986293795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11294660605098481315058393 8470995453823860986293795)
            ·
              refine ⟨12706493180735791479440693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8470995453823860986293795 12706493180735791479440693)
              ·
                refine ⟨1191233735693980451197565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12706493180735791479440693 1191233735693980451197565)
                ·
                  refine ⟨446712650885242669199087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191233735693980451197565 446712650885242669199087)
                  ·
                    rfl

theorem cell20_978716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_978716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978716 prefixEnd_978716 := by exact prefixLift 978716
  have htrace : WordTrace (prefixWord ++ tailWord_978716) baseStart_978716 baseEnd_978716 := by
    simpa [prefixWord, tailWord_978716, baseEnd_978716] using wordTrace_append hprefix tailTrace_978716
  have hstable : (prefixWord ++ tailWord_978716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978716).length < 2 ^ (prefixWord ++ tailWord_978716).sum := by decide
  have hdescent : baseEnd_978716 < baseStart_978716 := by decide
  rcases family_descends (prefixWord ++ tailWord_978716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978750 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_978750 : Nat := 118140960795 + 978750 * 2 ^ 59
def prefixEnd_978750 : Nat := 4983230072969 + 3 ^ 40 * 978750 * 2
def baseEnd_978750 : Nat := 446728169411689662065615

theorem tailTrace_978750 : CollatzResearch.WordTrace tailWord_978750 prefixEnd_978750 446728169411689662065615 := by
  unfold tailWord_978750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462243150520422754630713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23798630136108921358030469 4462243150520422754630713)
  ·
    refine ⟨3346682362890317065973035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4462243150520422754630713 3346682362890317065973035)
    ·
      refine ⟨5020023544335475598959553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3346682362890317065973035 5020023544335475598959553)
      ·
        refine ⟨3765017658251606699219665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5020023544335475598959553 3765017658251606699219665)
        ·
          refine ⟨2823763243688705024414749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3765017658251606699219665 2823763243688705024414749)
          ·
            refine ⟨1058911216383264384155531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2823763243688705024414749 1058911216383264384155531)
            ·
              refine ⟨1588366824574896576233297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058911216383264384155531 1588366824574896576233297)
              ·
                refine ⟨1191275118431172432174973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1588366824574896576233297 1191275118431172432174973)
                ·
                  refine ⟨446728169411689662065615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191275118431172432174973 446728169411689662065615)
                  ·
                    rfl

theorem cell20_978750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_978750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978750 prefixEnd_978750 := by exact prefixLift 978750
  have htrace : WordTrace (prefixWord ++ tailWord_978750) baseStart_978750 baseEnd_978750 := by
    simpa [prefixWord, tailWord_978750, baseEnd_978750] using wordTrace_append hprefix tailTrace_978750
  have hstable : (prefixWord ++ tailWord_978750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978750).length < 2 ^ (prefixWord ++ tailWord_978750).sum := by decide
  have hdescent : baseEnd_978750 < baseStart_978750 := by decide
  rcases family_descends (prefixWord ++ tailWord_978750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978761 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 4]
def baseStart_978761 : Nat := 118140960795 + 978761 * 2 ^ 59
def prefixEnd_978761 : Nat := 4983230072969 + 3 ^ 40 * 978761 * 2
def baseEnd_978761 : Nat := 446733190111422512698903

theorem tailTrace_978761 : CollatzResearch.WordTrace tailWord_978761 prefixEnd_978761 446733190111422512698903 := by
  unfold tailWord_978761
  simp only [CollatzResearch.WordTrace]
  refine ⟨35698346407123530915696137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23798897604749020610464091 35698346407123530915696137)
  ·
    refine ⟨26773759805342648186772103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35698346407123530915696137 26773759805342648186772103)
    ·
      refine ⟨40160639708013972280158155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26773759805342648186772103 40160639708013972280158155)
      ·
        refine ⟨60240959562020958420237233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40160639708013972280158155 60240959562020958420237233)
        ·
          refine ⟨45180719671515718815177925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60240959562020958420237233 45180719671515718815177925)
          ·
            refine ⟨8471384938409197277845861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45180719671515718815177925 8471384938409197277845861)
            ·
              refine ⟨1588384675951724489596099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8471384938409197277845861 1588384675951724489596099)
              ·
                refine ⟨2382577013927586734394149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588384675951724489596099 2382577013927586734394149)
                ·
                  refine ⟨446733190111422512698903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2382577013927586734394149 446733190111422512698903)
                  ·
                    rfl

theorem cell20_978761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_978761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978761 prefixEnd_978761 := by exact prefixLift 978761
  have htrace : WordTrace (prefixWord ++ tailWord_978761) baseStart_978761 baseEnd_978761 := by
    simpa [prefixWord, tailWord_978761, baseEnd_978761] using wordTrace_append hprefix tailTrace_978761
  have hstable : (prefixWord ++ tailWord_978761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978761).length < 2 ^ (prefixWord ++ tailWord_978761).sum := by decide
  have hdescent : baseEnd_978761 < baseStart_978761 := by decide
  rcases family_descends (prefixWord ++ tailWord_978761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978823 : List Nat := [1, 1, 4, 2, 4, 1, 2, 5]
def baseStart_978823 : Nat := 118140960795 + 978823 * 2 ^ 59
def prefixEnd_978823 : Nat := 4983230072969 + 3 ^ 40 * 978823 * 2
def baseEnd_978823 : Nat := 148920496200275284210661

theorem tailTrace_978823 : CollatzResearch.WordTrace tailWord_978823 prefixEnd_978823 148920496200275284210661 := by
  unfold tailWord_978823
  simp only [CollatzResearch.WordTrace]
  refine ⟨35700607732898915504453123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23800405155265943669635415 35700607732898915504453123)
  ·
    refine ⟨53550911599348373256679685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35700607732898915504453123 53550911599348373256679685)
    ·
      refine ⟨10040795924877819985627441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53550911599348373256679685 10040795924877819985627441)
      ·
        refine ⟨7530596943658364989220581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10040795924877819985627441 7530596943658364989220581)
        ·
          refine ⟨1411986926935943435478859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7530596943658364989220581 1411986926935943435478859)
          ·
            refine ⟨2117980390403915153218289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411986926935943435478859 2117980390403915153218289)
            ·
              refine ⟨1588485292802936364913717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117980390403915153218289 1588485292802936364913717)
              ·
                refine ⟨148920496200275284210661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1588485292802936364913717 148920496200275284210661)
                ·
                  rfl

theorem cell20_978823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 5].length) (baseStart_978823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978823 prefixEnd_978823 := by exact prefixLift 978823
  have htrace : WordTrace (prefixWord ++ tailWord_978823) baseStart_978823 baseEnd_978823 := by
    simpa [prefixWord, tailWord_978823, baseEnd_978823] using wordTrace_append hprefix tailTrace_978823
  have hstable : (prefixWord ++ tailWord_978823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978823).length < 2 ^ (prefixWord ++ tailWord_978823).sum := by decide
  have hdescent : baseEnd_978823 < baseStart_978823 := by decide
  rcases family_descends (prefixWord ++ tailWord_978823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978896 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_978896 : Nat := 118140960795 + 978896 * 2 ^ 59
def prefixEnd_978896 : Nat := 4983230072969 + 3 ^ 40 * 978896 * 2
def baseEnd_978896 : Nat := 446794807789962043198351

theorem tailTrace_978896 : CollatzResearch.WordTrace tailWord_978896 prefixEnd_978896 446794807789962043198351 := by
  unfold tailWord_978896
  simp only [CollatzResearch.WordTrace]
  refine ⟨17851635130817224485930271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23802180174422965981240361 17851635130817224485930271)
  ·
    refine ⟨26777452696225836728895407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17851635130817224485930271 26777452696225836728895407)
    ·
      refine ⟨40166179044338755093343111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26777452696225836728895407 40166179044338755093343111)
      ·
        refine ⟨60249268566508132640014667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40166179044338755093343111 60249268566508132640014667)
        ·
          refine ⟨90373902849762198960022001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60249268566508132640014667 90373902849762198960022001)
          ·
            refine ⟨67780427137321649220016501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90373902849762198960022001 67780427137321649220016501)
            ·
              refine ⟨6354415044123904614376547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67780427137321649220016501 6354415044123904614376547)
              ·
                refine ⟨9531622566185856921564821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6354415044123904614376547 9531622566185856921564821)
                ·
                  refine ⟨446794807789962043198351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9531622566185856921564821 446794807789962043198351)
                  ·
                    rfl

theorem cell20_978896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_978896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978896 prefixEnd_978896 := by exact prefixLift 978896
  have htrace : WordTrace (prefixWord ++ tailWord_978896) baseStart_978896 baseEnd_978896 := by
    simpa [prefixWord, tailWord_978896, baseEnd_978896] using wordTrace_append hprefix tailTrace_978896
  have hstable : (prefixWord ++ tailWord_978896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978896).length < 2 ^ (prefixWord ++ tailWord_978896).sum := by decide
  have hdescent : baseEnd_978896 < baseStart_978896 := by decide
  rcases family_descends (prefixWord ++ tailWord_978896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978927 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 5]
def baseStart_978927 : Nat := 118140960795 + 978927 * 2 ^ 59
def prefixEnd_978927 : Nat := 4983230072969 + 3 ^ 40 * 978927 * 2
def baseEnd_978927 : Nat := 446808957034663713164891

theorem tailTrace_978927 : CollatzResearch.WordTrace tailWord_978927 prefixEnd_978927 446808957034663713164891 := by
  unfold tailWord_978927
  simp only [CollatzResearch.WordTrace]
  refine ⟨35704400924522141266239035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23802933949681427510826023 35704400924522141266239035)
  ·
    refine ⟨53556601386783211899358553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35704400924522141266239035 53556601386783211899358553)
    ·
      refine ⟨40167451040087408924518915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53556601386783211899358553 40167451040087408924518915)
      ·
        refine ⟨60251176560131113386778373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40167451040087408924518915 60251176560131113386778373)
        ·
          refine ⟨11297095605024583760020945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60251176560131113386778373 11297095605024583760020945)
          ·
            refine ⟨8472821703768437820015709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11297095605024583760020945 8472821703768437820015709)
            ·
              refine ⟨3177308138913164182505891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8472821703768437820015709 3177308138913164182505891)
              ·
                refine ⟨4765962208369746273758837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177308138913164182505891 4765962208369746273758837)
                ·
                  refine ⟨446808957034663713164891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4765962208369746273758837 446808957034663713164891)
                  ·
                    rfl

theorem cell20_978927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_978927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978927 prefixEnd_978927 := by exact prefixLift 978927
  have htrace : WordTrace (prefixWord ++ tailWord_978927) baseStart_978927 baseEnd_978927 := by
    simpa [prefixWord, tailWord_978927, baseEnd_978927] using wordTrace_append hprefix tailTrace_978927
  have hstable : (prefixWord ++ tailWord_978927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978927).length < 2 ^ (prefixWord ++ tailWord_978927).sum := by decide
  have hdescent : baseEnd_978927 < baseStart_978927 := by decide
  rcases family_descends (prefixWord ++ tailWord_978927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978950 : List Nat := [6, 2, 1, 2, 1, 1, 1, 6]
def baseStart_978950 : Nat := 118140960795 + 978950 * 2 ^ 59
def prefixEnd_978950 : Nat := 4983230072969 + 3 ^ 40 * 978950 * 2
def baseEnd_978950 : Nat := 148939818287125951799377

theorem tailTrace_978950 : CollatzResearch.WordTrace tailWord_978950 prefixEnd_978950 148939818287125951799377 := by
  unfold tailWord_978950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1115788743857463006072697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23803493202292544129550869 1115788743857463006072697)
  ·
    refine ⟨836841557893097254554523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1115788743857463006072697 836841557893097254554523)
    ·
      refine ⟨1255262336839645881831785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836841557893097254554523 1255262336839645881831785)
      ·
        refine ⟨941446752629734411373839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1255262336839645881831785 941446752629734411373839)
        ·
          refine ⟨1412170128944601617060759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941446752629734411373839 1412170128944601617060759)
          ·
            refine ⟨2118255193416902425591139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412170128944601617060759 2118255193416902425591139)
            ·
              refine ⟨3177382790125353638386709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118255193416902425591139 3177382790125353638386709)
              ·
                refine ⟨148939818287125951799377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3177382790125353638386709 148939818287125951799377)
                ·
                  rfl

theorem cell20_978950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_978950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978950 prefixEnd_978950 := by exact prefixLift 978950
  have htrace : WordTrace (prefixWord ++ tailWord_978950) baseStart_978950 baseEnd_978950 := by
    simpa [prefixWord, tailWord_978950, baseEnd_978950] using wordTrace_append hprefix tailTrace_978950
  have hstable : (prefixWord ++ tailWord_978950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978950).length < 2 ^ (prefixWord ++ tailWord_978950).sum := by decide
  have hdescent : baseEnd_978950 < baseStart_978950 := by decide
  rcases family_descends (prefixWord ++ tailWord_978950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978951 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 4]
def baseStart_978951 : Nat := 118140960795 + 978951 * 2 ^ 59
def prefixEnd_978951 : Nat := 4983230072969 + 3 ^ 40 * 978951 * 2
def baseEnd_978951 : Nat := 446819911288626296364793

theorem tailTrace_978951 : CollatzResearch.WordTrace tailWord_978951 prefixEnd_978951 446819911288626296364793 := by
  unfold tailWord_978951
  simp only [CollatzResearch.WordTrace]
  refine ⟨35705276276435193365112707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23803517517623462243408471 35705276276435193365112707)
  ·
    refine ⟨53557914414652790047669061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35705276276435193365112707 53557914414652790047669061)
    ·
      refine ⟨10042108952747398133937949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53557914414652790047669061 10042108952747398133937949)
      ·
        refine ⟨3765790857280274300226731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10042108952747398133937949 3765790857280274300226731)
        ·
          refine ⟨5648686285920411450340097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3765790857280274300226731 5648686285920411450340097)
          ·
            refine ⟨4236514714440308587755073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5648686285920411450340097 4236514714440308587755073)
            ·
              refine ⟨3177386035830231440816305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236514714440308587755073 3177386035830231440816305)
              ·
                refine ⟨2383039526872673580612229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3177386035830231440816305 2383039526872673580612229)
                ·
                  refine ⟨446819911288626296364793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2383039526872673580612229 446819911288626296364793)
                  ·
                    rfl

theorem cell20_978951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_978951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978951 prefixEnd_978951 := by exact prefixLift 978951
  have htrace : WordTrace (prefixWord ++ tailWord_978951) baseStart_978951 baseEnd_978951 := by
    simpa [prefixWord, tailWord_978951, baseEnd_978951] using wordTrace_append hprefix tailTrace_978951
  have hstable : (prefixWord ++ tailWord_978951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978951).length < 2 ^ (prefixWord ++ tailWord_978951).sum := by decide
  have hdescent : baseEnd_978951 < baseStart_978951 := by decide
  rcases family_descends (prefixWord ++ tailWord_978951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978954 : List Nat := [3, 1, 2, 2, 4, 2, 2, 4]
def baseStart_978954 : Nat := 118140960795 + 978954 * 2 ^ 59
def prefixEnd_978954 : Nat := 4983230072969 + 3 ^ 40 * 978954 * 2
def baseEnd_978954 : Nat := 148940426856790539754927

theorem tailTrace_978954 : CollatzResearch.WordTrace tailWord_978954 prefixEnd_978954 148940426856790539754927 := by
  unfold tailWord_978954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8926346423856081219367979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23803590463616216584981277 8926346423856081219367979)
  ·
    refine ⟨13389519635784121829051969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8926346423856081219367979 13389519635784121829051969)
    ·
      refine ⟨10042139726838091371788977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13389519635784121829051969 10042139726838091371788977)
      ·
        refine ⟨7531604795128568528841733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10042139726838091371788977 7531604795128568528841733)
        ·
          refine ⟨1412175899086606599157825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7531604795128568528841733 1412175899086606599157825)
          ·
            refine ⟨1059131924314954949368369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1412175899086606599157825 1059131924314954949368369)
            ·
              refine ⟨794348943236216212026277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059131924314954949368369 794348943236216212026277)
              ·
                refine ⟨148940426856790539754927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 794348943236216212026277 148940426856790539754927)
                ·
                  rfl

theorem cell20_978954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_978954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978954 prefixEnd_978954 := by exact prefixLift 978954
  have htrace : WordTrace (prefixWord ++ tailWord_978954) baseStart_978954 baseEnd_978954 := by
    simpa [prefixWord, tailWord_978954, baseEnd_978954] using wordTrace_append hprefix tailTrace_978954
  have hstable : (prefixWord ++ tailWord_978954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978954).length < 2 ^ (prefixWord ++ tailWord_978954).sum := by decide
  have hdescent : baseEnd_978954 < baseStart_978954 := by decide
  rcases family_descends (prefixWord ++ tailWord_978954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978958 : List Nat := [4, 1, 1, 2, 2, 1, 3, 6]
def baseStart_978958 : Nat := 118140960795 + 978958 * 2 ^ 59
def prefixEnd_978958 : Nat := 4983230072969 + 3 ^ 40 * 978958 * 2
def baseEnd_978958 : Nat := 148941035426455127710477

theorem tailTrace_978958 : CollatzResearch.WordTrace tailWord_978958 prefixEnd_978958 148941035426455127710477 := by
  unfold tailWord_978958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4463191448426229195077191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23803687724939889040411685 4463191448426229195077191)
  ·
    refine ⟨6694787172639343792615787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4463191448426229195077191 6694787172639343792615787)
    ·
      refine ⟨10042180758959015688923681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6694787172639343792615787 10042180758959015688923681)
      ·
        refine ⟨7531635569219261766692761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10042180758959015688923681 7531635569219261766692761)
        ·
          refine ⟨5648726676914446325019571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7531635569219261766692761 5648726676914446325019571)
          ·
            refine ⟨8473090015371669487529357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648726676914446325019571 8473090015371669487529357)
            ·
              refine ⟨3177408755764376057823509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8473090015371669487529357 3177408755764376057823509)
              ·
                refine ⟨148941035426455127710477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3177408755764376057823509 148941035426455127710477)
                ·
                  rfl

theorem cell20_978958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_978958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_978958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_978958 prefixEnd_978958 := by exact prefixLift 978958
  have htrace : WordTrace (prefixWord ++ tailWord_978958) baseStart_978958 baseEnd_978958 := by
    simpa [prefixWord, tailWord_978958, baseEnd_978958] using wordTrace_append hprefix tailTrace_978958
  have hstable : (prefixWord ++ tailWord_978958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978958).length < 2 ^ (prefixWord ++ tailWord_978958).sum := by decide
  have hdescent : baseEnd_978958 < baseStart_978958 := by decide
  rcases family_descends (prefixWord ++ tailWord_978958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979003 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 3]
def baseStart_979003 : Nat := 118140960795 + 979003 * 2 ^ 59
def prefixEnd_979003 : Nat := 4983230072969 + 3 ^ 40 * 979003 * 2
def baseEnd_979003 : Nat := 446843645505545226631247

theorem tailTrace_979003 : CollatzResearch.WordTrace tailWord_979003 prefixEnd_979003 446843645505545226631247 := by
  unfold tailWord_979003
  simp only [CollatzResearch.WordTrace]
  refine ⟨35707172872246806246005663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23804781914831204164003775 35707172872246806246005663)
  ·
    refine ⟨53560759308370209369008495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35707172872246806246005663 53560759308370209369008495)
    ·
      refine ⟨80341138962555314053512743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53560759308370209369008495 80341138962555314053512743)
      ·
        refine ⟨120511708443832971080269115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80341138962555314053512743 120511708443832971080269115)
        ·
          refine ⟨180767562665749456620403673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120511708443832971080269115 180767562665749456620403673)
          ·
            refine ⟨135575671999312092465302755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180767562665749456620403673 135575671999312092465302755)
            ·
              refine ⟨203363507998968138697954133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135575671999312092465302755 203363507998968138697954133)
              ·
                refine ⟨1191583054681453937683325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 203363507998968138697954133 1191583054681453937683325)
                ·
                  refine ⟨446843645505545226631247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191583054681453937683325 446843645505545226631247)
                  ·
                    rfl

theorem cell20_979003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 3].length) (baseStart_979003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979003 prefixEnd_979003 := by exact prefixLift 979003
  have htrace : WordTrace (prefixWord ++ tailWord_979003) baseStart_979003 baseEnd_979003 := by
    simpa [prefixWord, tailWord_979003, baseEnd_979003] using wordTrace_append hprefix tailTrace_979003
  have hstable : (prefixWord ++ tailWord_979003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979003).length < 2 ^ (prefixWord ++ tailWord_979003).sum := by decide
  have hdescent : baseEnd_979003 < baseStart_979003 := by decide
  rcases family_descends (prefixWord ++ tailWord_979003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979017 : List Nat := [1, 2, 1, 1, 2, 2, 3, 8]
def baseStart_979017 : Nat := 118140960795 + 979017 * 2 ^ 59
def prefixEnd_979017 : Nat := 4983230072969 + 3 ^ 40 * 979017 * 2
def baseEnd_979017 : Nat := 148950011829007800054841

theorem tailTrace_979017 : CollatzResearch.WordTrace tailWord_979017 prefixEnd_979017 148950011829007800054841 := by
  unfold tailWord_979017
  simp only [CollatzResearch.WordTrace]
  refine ⟨35707683494196086637015305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23805122329464057758010203 35707683494196086637015305)
  ·
    refine ⟨26780762620647064977761479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35707683494196086637015305 26780762620647064977761479)
    ·
      refine ⟨40171143930970597466642219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26780762620647064977761479 40171143930970597466642219)
      ·
        refine ⟨60256715896455896199963329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40171143930970597466642219 60256715896455896199963329)
        ·
          refine ⟨45192536922341922149972497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60256715896455896199963329 45192536922341922149972497)
          ·
            refine ⟨33894402691756441612479373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45192536922341922149972497 33894402691756441612479373)
            ·
              refine ⟨12710401009408665604679765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33894402691756441612479373 12710401009408665604679765)
              ·
                refine ⟨148950011829007800054841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12710401009408665604679765 148950011829007800054841)
                ·
                  rfl

theorem cell20_979017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_979017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979017 prefixEnd_979017 := by exact prefixLift 979017
  have htrace : WordTrace (prefixWord ++ tailWord_979017) baseStart_979017 baseEnd_979017 := by
    simpa [prefixWord, tailWord_979017, baseEnd_979017] using wordTrace_append hprefix tailTrace_979017
  have hstable : (prefixWord ++ tailWord_979017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979017).length < 2 ^ (prefixWord ++ tailWord_979017).sum := by decide
  have hdescent : baseEnd_979017 < baseStart_979017 := by decide
  rcases family_descends (prefixWord ++ tailWord_979017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979037 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 3]
def baseStart_979037 : Nat := 118140960795 + 979037 * 2 ^ 59
def prefixEnd_979037 : Nat := 4983230072969 + 3 ^ 40 * 979037 * 2
def baseEnd_979037 : Nat := 446859164031992219497775

theorem tailTrace_979037 : CollatzResearch.WordTrace tailWord_979037 prefixEnd_979037 446859164031992219497775 := by
  unfold tailWord_979037
  simp only [CollatzResearch.WordTrace]
  refine ⟨35708412954123630052743365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23805608636082420035162243 35708412954123630052743365)
  ·
    refine ⟨6695327428898180634889381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35708412954123630052743365 6695327428898180634889381)
    ·
      refine ⟨1255373892918408869041759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6695327428898180634889381 1255373892918408869041759)
      ·
        refine ⟨1883060839377613303562639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255373892918408869041759 1883060839377613303562639)
        ·
          refine ⟨2824591259066419955343959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883060839377613303562639 2824591259066419955343959)
          ·
            refine ⟨4236886888599629933015939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824591259066419955343959 4236886888599629933015939)
            ·
              refine ⟨6355330332899444899523909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236886888599629933015939 6355330332899444899523909)
              ·
                refine ⟨1191624437418645918660733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6355330332899444899523909 1191624437418645918660733)
                ·
                  refine ⟨446859164031992219497775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191624437418645918660733 446859164031992219497775)
                  ·
                    rfl

theorem cell20_979037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_979037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979037 prefixEnd_979037 := by exact prefixLift 979037
  have htrace : WordTrace (prefixWord ++ tailWord_979037) baseStart_979037 baseEnd_979037 := by
    simpa [prefixWord, tailWord_979037, baseEnd_979037] using wordTrace_append hprefix tailTrace_979037
  have hstable : (prefixWord ++ tailWord_979037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979037).length < 2 ^ (prefixWord ++ tailWord_979037).sum := by decide
  have hdescent : baseEnd_979037 < baseStart_979037 := by decide
  rcases family_descends (prefixWord ++ tailWord_979037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979058 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_979058 : Nat := 118140960795 + 979058 * 2 ^ 59
def prefixEnd_979058 : Nat := 4983230072969 + 3 ^ 40 * 979058 * 2
def baseEnd_979058 : Nat := 446868749004209479797689

theorem tailTrace_979058 : CollatzResearch.WordTrace tailWord_979058 prefixEnd_979058 446868749004209479797689 := by
  unfold tailWord_979058
  simp only [CollatzResearch.WordTrace]
  refine ⟨8927294721761887659814457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23806119258031700426171885 8927294721761887659814457)
  ·
    refine ⟨6695471041321415744860843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8927294721761887659814457 6695471041321415744860843)
    ·
      refine ⟨10043206561982123617291265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6695471041321415744860843 10043206561982123617291265)
      ·
        refine ⟨7532404921486592712968449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10043206561982123617291265 7532404921486592712968449)
        ·
          refine ⟨5649303691114944534726337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7532404921486592712968449 5649303691114944534726337)
          ·
            refine ⟨4236977768336208401044753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5649303691114944534726337 4236977768336208401044753)
            ·
              refine ⟨3177733326252156300783565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236977768336208401044753 3177733326252156300783565)
              ·
                refine ⟨1191649997344558612793837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3177733326252156300783565 1191649997344558612793837)
                ·
                  refine ⟨446868749004209479797689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191649997344558612793837 446868749004209479797689)
                  ·
                    rfl

theorem cell20_979058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_979058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979058 prefixEnd_979058 := by exact prefixLift 979058
  have htrace : WordTrace (prefixWord ++ tailWord_979058) baseStart_979058 baseEnd_979058 := by
    simpa [prefixWord, tailWord_979058, baseEnd_979058] using wordTrace_append hprefix tailTrace_979058
  have hstable : (prefixWord ++ tailWord_979058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979058).length < 2 ^ (prefixWord ++ tailWord_979058).sum := by decide
  have hdescent : baseEnd_979058 < baseStart_979058 := by decide
  rcases family_descends (prefixWord ++ tailWord_979058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979065 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 4]
def baseStart_979065 : Nat := 118140960795 + 979065 * 2 ^ 59
def prefixEnd_979065 : Nat := 4983230072969 + 3 ^ 40 * 979065 * 2
def baseEnd_979065 : Nat := 446871943994948566564327

theorem tailTrace_979065 : CollatzResearch.WordTrace tailWord_979065 prefixEnd_979065 446871943994948566564327 := by
  unfold tailWord_979065
  simp only [CollatzResearch.WordTrace]
  refine ⟨35709434198022190834762649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23806289465348127223175099 35709434198022190834762649)
  ·
    refine ⟨26782075648516643126071987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35709434198022190834762649 26782075648516643126071987)
    ·
      refine ⟨40173113472774964689107981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26782075648516643126071987 40173113472774964689107981)
      ·
        refine ⟨15064917552290611758415493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40173113472774964689107981 15064917552290611758415493)
        ·
          refine ⟨2824672041054489704702905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15064917552290611758415493 2824672041054489704702905)
          ·
            refine ⟨2118504030790867278527179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2824672041054489704702905 2118504030790867278527179)
            ·
              refine ⟨3177756046186300917790769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118504030790867278527179 3177756046186300917790769)
              ·
                refine ⟨2383317034639725688343077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3177756046186300917790769 2383317034639725688343077)
                ·
                  refine ⟨446871943994948566564327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2383317034639725688343077 446871943994948566564327)
                  ·
                    rfl

theorem cell20_979065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_979065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979065 prefixEnd_979065 := by exact prefixLift 979065
  have htrace : WordTrace (prefixWord ++ tailWord_979065) baseStart_979065 baseEnd_979065 := by
    simpa [prefixWord, tailWord_979065, baseEnd_979065] using wordTrace_append hprefix tailTrace_979065
  have hstable : (prefixWord ++ tailWord_979065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979065).length < 2 ^ (prefixWord ++ tailWord_979065).sum := by decide
  have hdescent : baseEnd_979065 < baseStart_979065 := by decide
  rcases family_descends (prefixWord ++ tailWord_979065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979082 : List Nat := [3, 1, 2, 3, 1, 2, 1, 5, 2]
def baseStart_979082 : Nat := 118140960795 + 979082 * 2 ^ 59
def prefixEnd_979082 : Nat := 4983230072969 + 3 ^ 40 * 979082 * 2
def baseEnd_979082 : Nat := 446879703258172062997591

theorem tailTrace_979082 : CollatzResearch.WordTrace tailWord_979082 prefixEnd_979082 446879703258172062997591 := by
  unfold tailWord_979082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8927513559740150684532875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23806702825973735158754333 8927513559740150684532875)
  ·
    refine ⟨13391270339610226026799313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8927513559740150684532875 13391270339610226026799313)
    ·
      refine ⟨10043452754707669520099485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13391270339610226026799313 10043452754707669520099485)
      ·
        refine ⟨3766294783015376070037307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10043452754707669520099485 3766294783015376070037307)
        ·
          refine ⟨5649442174523064105055961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766294783015376070037307 5649442174523064105055961)
          ·
            refine ⟨4237081630892298078791971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5649442174523064105055961 4237081630892298078791971)
            ·
              refine ⟨6355622446338447118187957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237081630892298078791971 6355622446338447118187957)
              ·
                refine ⟨595839604344229417330121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6355622446338447118187957 595839604344229417330121)
                ·
                  refine ⟨446879703258172062997591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 595839604344229417330121 446879703258172062997591)
                  ·
                    rfl

theorem cell20_979082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_979082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979082 prefixEnd_979082 := by exact prefixLift 979082
  have htrace : WordTrace (prefixWord ++ tailWord_979082) baseStart_979082 baseEnd_979082 := by
    simpa [prefixWord, tailWord_979082, baseEnd_979082] using wordTrace_append hprefix tailTrace_979082
  have hstable : (prefixWord ++ tailWord_979082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979082).length < 2 ^ (prefixWord ++ tailWord_979082).sum := by decide
  have hdescent : baseEnd_979082 < baseStart_979082 := by decide
  rcases family_descends (prefixWord ++ tailWord_979082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979093 : List Nat := [1, 3, 2, 1, 1, 1, 11]
def baseStart_979093 : Nat := 118140960795 + 979093 * 2 ^ 59
def prefixEnd_979093 : Nat := 4983230072969 + 3 ^ 40 * 979093 * 2
def baseEnd_979093 : Nat := 49653858217544990403431

theorem tailTrace_979093 : CollatzResearch.WordTrace tailWord_979093 prefixEnd_979093 49653858217544990403431 := by
  unfold tailWord_979093
  simp only [CollatzResearch.WordTrace]
  refine ⟨35710455441920751616781933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23806970294613834411187955 35710455441920751616781933)
  ·
    refine ⟨13391420790720281856293225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35710455441920751616781933 13391420790720281856293225)
    ·
      refine ⟨10043565593040211392219919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13391420790720281856293225 10043565593040211392219919)
      ·
        refine ⟨15065348389560317088329879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10043565593040211392219919 15065348389560317088329879)
        ·
          refine ⟨22598022584340475632494819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15065348389560317088329879 22598022584340475632494819)
          ·
            refine ⟨33897033876510713448742229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22598022584340475632494819 33897033876510713448742229)
            ·
              refine ⟨49653858217544990403431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33897033876510713448742229 49653858217544990403431)
              ·
                rfl

theorem cell20_979093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 11].length) (baseStart_979093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979093 prefixEnd_979093 := by exact prefixLift 979093
  have htrace : WordTrace (prefixWord ++ tailWord_979093) baseStart_979093 baseEnd_979093 := by
    simpa [prefixWord, tailWord_979093, baseEnd_979093] using wordTrace_append hprefix tailTrace_979093
  have hstable : (prefixWord ++ tailWord_979093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979093).length < 2 ^ (prefixWord ++ tailWord_979093).sum := by decide
  have hdescent : baseEnd_979093 < baseStart_979093 := by decide
  rcases family_descends (prefixWord ++ tailWord_979093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979096 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 5]
def baseStart_979096 : Nat := 118140960795 + 979096 * 2 ^ 59
def prefixEnd_979096 : Nat := 4983230072969 + 3 ^ 40 * 979096 * 2
def baseEnd_979096 : Nat := 446886093239650236530867

theorem tailTrace_979096 : CollatzResearch.WordTrace tailWord_979096 prefixEnd_979096 446886093239650236530867 := by
  unfold tailWord_979096
  simp only [CollatzResearch.WordTrace]
  refine ⟨17855282430454941564570571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23807043240606588752760761 17855282430454941564570571)
  ·
    refine ⟨26782923645682412346855857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17855282430454941564570571 26782923645682412346855857)
    ·
      refine ⟨20087192734261809260141893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26782923645682412346855857 20087192734261809260141893)
      ·
        refine ⟨3766348637674089236276605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20087192734261809260141893 3766348637674089236276605)
        ·
          refine ⟨1412380739127783463603727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3766348637674089236276605 1412380739127783463603727)
          ·
            refine ⟨2118571108691675195405591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412380739127783463603727 2118571108691675195405591)
            ·
              refine ⟨3177856663037512793108387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118571108691675195405591 3177856663037512793108387)
              ·
                refine ⟨4766784994556269189662581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177856663037512793108387 4766784994556269189662581)
                ·
                  refine ⟨446886093239650236530867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4766784994556269189662581 446886093239650236530867)
                  ·
                    rfl

theorem cell20_979096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_979096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979096 prefixEnd_979096 := by exact prefixLift 979096
  have htrace : WordTrace (prefixWord ++ tailWord_979096) baseStart_979096 baseEnd_979096 := by
    simpa [prefixWord, tailWord_979096, baseEnd_979096] using wordTrace_append hprefix tailTrace_979096
  have hstable : (prefixWord ++ tailWord_979096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979096).length < 2 ^ (prefixWord ++ tailWord_979096).sum := by decide
  have hdescent : baseEnd_979096 < baseStart_979096 := by decide
  rcases family_descends (prefixWord ++ tailWord_979096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979103 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 4]
def baseStart_979103 : Nat := 118140960795 + 979103 * 2 ^ 59
def prefixEnd_979103 : Nat := 4983230072969 + 3 ^ 40 * 979103 * 2
def baseEnd_979103 : Nat := 446889288230389323297505

theorem tailTrace_979103 : CollatzResearch.WordTrace tailWord_979103 prefixEnd_979103 446889288230389323297505 := by
  unfold tailWord_979103
  simp only [CollatzResearch.WordTrace]
  refine ⟨35710820171884523324645963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23807213447923015549763975 35710820171884523324645963)
  ·
    refine ⟨53566230257826784986968945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35710820171884523324645963 53566230257826784986968945)
    ·
      refine ⟨40174672693370088740226709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53566230257826784986968945 40174672693370088740226709)
      ·
        refine ⟨1883187782501722909698127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40174672693370088740226709 1883187782501722909698127)
        ·
          refine ⟨2824781673752584364547191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883187782501722909698127 2824781673752584364547191)
          ·
            refine ⟨4237172510628876546820787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824781673752584364547191 4237172510628876546820787)
            ·
              refine ⟨6355758765943314820231181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237172510628876546820787 6355758765943314820231181)
              ·
                refine ⟨2383409537228743057586693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6355758765943314820231181 2383409537228743057586693)
                ·
                  refine ⟨446889288230389323297505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2383409537228743057586693 446889288230389323297505)
                  ·
                    rfl

theorem cell20_979103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_979103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979103 prefixEnd_979103 := by exact prefixLift 979103
  have htrace : WordTrace (prefixWord ++ tailWord_979103) baseStart_979103 baseEnd_979103 := by
    simpa [prefixWord, tailWord_979103, baseEnd_979103] using wordTrace_append hprefix tailTrace_979103
  have hstable : (prefixWord ++ tailWord_979103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979103).length < 2 ^ (prefixWord ++ tailWord_979103).sum := by decide
  have hdescent : baseEnd_979103 < baseStart_979103 := by decide
  rcases family_descends (prefixWord ++ tailWord_979103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979127 : List Nat := [1, 1, 3, 1, 4, 4, 2, 4]
def baseStart_979127 : Nat := 118140960795 + 979127 * 2 ^ 59
def prefixEnd_979127 : Nat := 4983230072969 + 3 ^ 40 * 979127 * 2
def baseEnd_979127 : Nat := 148966747494783968832469

theorem tailTrace_979127 : CollatzResearch.WordTrace tailWord_979127 prefixEnd_979127 148966747494783968832469 := by
  unfold tailWord_979127
  simp only [CollatzResearch.WordTrace]
  refine ⟨35711695523797575423519635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23807797015865050282346423 35711695523797575423519635)
  ·
    refine ⟨53567543285696363135279453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35711695523797575423519635 53567543285696363135279453)
    ·
      refine ⟨20087828732136136175729795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53567543285696363135279453 20087828732136136175729795)
      ·
        refine ⟨30131743098204204263594693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20087828732136136175729795 30131743098204204263594693)
        ·
          refine ⟨5649701830913288299424005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30131743098204204263594693 5649701830913288299424005)
          ·
            refine ⟨1059319093296241556142001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5649701830913288299424005 1059319093296241556142001)
            ·
              refine ⟨794489319972181167106501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059319093296241556142001 794489319972181167106501)
              ·
                refine ⟨148966747494783968832469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 794489319972181167106501 148966747494783968832469)
                ·
                  rfl

theorem cell20_979127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 4].length) (baseStart_979127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979127 prefixEnd_979127 := by exact prefixLift 979127
  have htrace : WordTrace (prefixWord ++ tailWord_979127) baseStart_979127 baseEnd_979127 := by
    simpa [prefixWord, tailWord_979127, baseEnd_979127] using wordTrace_append hprefix tailTrace_979127
  have hstable : (prefixWord ++ tailWord_979127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979127).length < 2 ^ (prefixWord ++ tailWord_979127).sum := by decide
  have hdescent : baseEnd_979127 < baseStart_979127 := by decide
  rcases family_descends (prefixWord ++ tailWord_979127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979131 : List Nat := [1, 1, 1, 1, 1, 2, 7, 6]
def baseStart_979131 : Nat := 118140960795 + 979131 * 2 ^ 59
def prefixEnd_979131 : Nat := 4983230072969 + 3 ^ 40 * 979131 * 2
def baseEnd_979131 : Nat := 148967356064448556788019

theorem tailTrace_979131 : CollatzResearch.WordTrace tailWord_979131 prefixEnd_979131 148967356064448556788019 := by
  unfold tailWord_979131
  simp only [CollatzResearch.WordTrace]
  refine ⟨35711841415783084106665247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23807894277188722737776831 35711841415783084106665247)
  ·
    refine ⟨53567762123674626159997871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35711841415783084106665247 53567762123674626159997871)
    ·
      refine ⟨80351643185511939239996807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53567762123674626159997871 80351643185511939239996807)
      ·
        refine ⟨120527464778267908859995211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80351643185511939239996807 120527464778267908859995211)
        ·
          refine ⟨180791197167401863289992817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120527464778267908859995211 180791197167401863289992817)
          ·
            refine ⟨135593397875551397467494613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180791197167401863289992817 135593397875551397467494613)
            ·
              refine ⟨3177970262708235878144405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 135593397875551397467494613 3177970262708235878144405)
              ·
                refine ⟨148967356064448556788019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3177970262708235878144405 148967356064448556788019)
                ·
                  rfl

theorem cell20_979131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_979131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979131 prefixEnd_979131 := by exact prefixLift 979131
  have htrace : WordTrace (prefixWord ++ tailWord_979131) baseStart_979131 baseEnd_979131 := by
    simpa [prefixWord, tailWord_979131, baseEnd_979131] using wordTrace_append hprefix tailTrace_979131
  have hstable : (prefixWord ++ tailWord_979131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979131).length < 2 ^ (prefixWord ++ tailWord_979131).sum := by decide
  have hdescent : baseEnd_979131 < baseStart_979131 := by decide
  rcases family_descends (prefixWord ++ tailWord_979131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979164 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 3]
def baseStart_979164 : Nat := 118140960795 + 979164 * 2 ^ 59
def prefixEnd_979164 : Nat := 4983230072969 + 3 ^ 40 * 979164 * 2
def baseEnd_979164 : Nat := 446917130292544222263923

theorem tailTrace_979164 : CollatzResearch.WordTrace tailWord_979164 prefixEnd_979164 446917130292544222263923 := by
  unfold tailWord_979164
  simp only [CollatzResearch.WordTrace]
  refine ⟨17856522512331765371308273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23808696683109020495077697 17856522512331765371308273)
  ·
    refine ⟨13392391884248824028481205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17856522512331765371308273 13392391884248824028481205)
    ·
      refine ⟨1255536739148327252670113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13392391884248824028481205 1255536739148327252670113)
      ·
        refine ⟨941652554361245439502585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1255536739148327252670113 941652554361245439502585)
        ·
          refine ⟨706239415770934079626939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941652554361245439502585 706239415770934079626939)
          ·
            refine ⟨1059359123656401119440409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706239415770934079626939 1059359123656401119440409)
            ·
              refine ⟨794519342742300839580307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059359123656401119440409 794519342742300839580307)
              ·
                refine ⟨1191779014113451259370461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794519342742300839580307 1191779014113451259370461)
                ·
                  refine ⟨446917130292544222263923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1191779014113451259370461 446917130292544222263923)
                  ·
                    rfl

theorem cell20_979164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_979164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979164 prefixEnd_979164 := by exact prefixLift 979164
  have htrace : WordTrace (prefixWord ++ tailWord_979164) baseStart_979164 baseEnd_979164 := by
    simpa [prefixWord, tailWord_979164, baseEnd_979164] using wordTrace_append hprefix tailTrace_979164
  have hstable : (prefixWord ++ tailWord_979164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979164).length < 2 ^ (prefixWord ++ tailWord_979164).sum := by decide
  have hdescent : baseEnd_979164 < baseStart_979164 := by decide
  rcases family_descends (prefixWord ++ tailWord_979164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979165 : List Nat := [1, 4, 3, 2, 1, 2, 2, 5]
def baseStart_979165 : Nat := 118140960795 + 979165 * 2 ^ 59
def prefixEnd_979165 : Nat := 4983230072969 + 3 ^ 40 * 979165 * 2
def baseEnd_979165 : Nat := 148972528906597554410195

theorem tailTrace_979165 : CollatzResearch.WordTrace tailWord_979165 prefixEnd_979165 148972528906597554410195 := by
  unfold tailWord_979165
  simp only [CollatzResearch.WordTrace]
  refine ⟨35713081497659907913402949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23808720998439938608935299 35713081497659907913402949)
  ·
    refine ⟨6696202780811232733763053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35713081497659907913402949 6696202780811232733763053)
    ·
      refine ⟨2511076042804212275161145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6696202780811232733763053 2511076042804212275161145)
      ·
        refine ⟨1883307032103159206370859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2511076042804212275161145 1883307032103159206370859)
        ·
          refine ⟨2824960548154738809556289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883307032103159206370859 2824960548154738809556289)
          ·
            refine ⟨2118720411116054107167217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2824960548154738809556289 2118720411116054107167217)
            ·
              refine ⟨1589040308337040580375413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2118720411116054107167217 1589040308337040580375413)
              ·
                refine ⟨148972528906597554410195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1589040308337040580375413 148972528906597554410195)
                ·
                  rfl

theorem cell20_979165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_979165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979165 prefixEnd_979165 := by exact prefixLift 979165
  have htrace : WordTrace (prefixWord ++ tailWord_979165) baseStart_979165 baseEnd_979165 := by
    simpa [prefixWord, tailWord_979165, baseEnd_979165] using wordTrace_append hprefix tailTrace_979165
  have hstable : (prefixWord ++ tailWord_979165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979165).length < 2 ^ (prefixWord ++ tailWord_979165).sum := by decide
  have hdescent : baseEnd_979165 < baseStart_979165 := by decide
  rcases family_descends (prefixWord ++ tailWord_979165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979186 : List Nat := [3, 2, 1, 3, 2, 1, 2, 6]
def baseStart_979186 : Nat := 118140960795 + 979186 * 2 ^ 59
def prefixEnd_979186 : Nat := 4983230072969 + 3 ^ 40 * 979186 * 2
def baseEnd_979186 : Nat := 148975723897336641176833

theorem tailTrace_979186 : CollatzResearch.WordTrace tailWord_979186 prefixEnd_979186 148975723897336641176833 := by
  unfold tailWord_979186
  simp only [CollatzResearch.WordTrace]
  refine ⟨8928461857645957124979353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23809231620389218999944941 8928461857645957124979353)
  ·
    refine ⟨6696346393234467843734515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8928461857645957124979353 6696346393234467843734515)
    ·
      refine ⟨10044519589851701765601773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6696346393234467843734515 10044519589851701765601773)
      ·
        refine ⟨3766694846194388162100665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10044519589851701765601773 3766694846194388162100665)
        ·
          refine ⟨2825021134645791121575499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3766694846194388162100665 2825021134645791121575499)
          ·
            refine ⟨4237531701968686682363249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825021134645791121575499 4237531701968686682363249)
            ·
              refine ⟨3178148776476515011772437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4237531701968686682363249 3178148776476515011772437)
              ·
                refine ⟨148975723897336641176833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3178148776476515011772437 148975723897336641176833)
                ·
                  rfl

theorem cell20_979186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_979186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979186 prefixEnd_979186 := by exact prefixLift 979186
  have htrace : WordTrace (prefixWord ++ tailWord_979186) baseStart_979186 baseEnd_979186 := by
    simpa [prefixWord, tailWord_979186, baseEnd_979186] using wordTrace_append hprefix tailTrace_979186
  have hstable : (prefixWord ++ tailWord_979186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979186).length < 2 ^ (prefixWord ++ tailWord_979186).sum := by decide
  have hdescent : baseEnd_979186 < baseStart_979186 := by decide
  rcases family_descends (prefixWord ++ tailWord_979186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979262 : List Nat := [4, 2, 1, 2, 1, 3, 7]
def baseStart_979262 : Nat := 118140960795 + 979262 * 2 ^ 59
def prefixEnd_979262 : Nat := 4983230072969 + 3 ^ 40 * 979262 * 2
def baseEnd_979262 : Nat := 49662428906987937444095

theorem tailTrace_979262 : CollatzResearch.WordTrace tailWord_979262 prefixEnd_979262 49662428906987937444095 := by
  unfold tailWord_979262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464577422288561684960505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23811079585538995653122693 4464577422288561684960505)
  ·
    refine ⟨3348433066716421263720379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4464577422288561684960505 3348433066716421263720379)
    ·
      refine ⟨5022649600074631895580569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3348433066716421263720379 5022649600074631895580569)
      ·
        refine ⟨3766987200055973921685427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5022649600074631895580569 3766987200055973921685427)
        ·
          refine ⟨5650480800083960882528141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766987200055973921685427 5650480800083960882528141)
          ·
            refine ⟨2118930300031485330948053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5650480800083960882528141 2118930300031485330948053)
            ·
              refine ⟨49662428906987937444095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2118930300031485330948053 49662428906987937444095)
              ·
                rfl

theorem cell20_979262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 7].length) (baseStart_979262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979262 prefixEnd_979262 := by exact prefixLift 979262
  have htrace : WordTrace (prefixWord ++ tailWord_979262) baseStart_979262 baseEnd_979262 := by
    simpa [prefixWord, tailWord_979262, baseEnd_979262] using wordTrace_append hprefix tailTrace_979262
  have hstable : (prefixWord ++ tailWord_979262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979262).length < 2 ^ (prefixWord ++ tailWord_979262).sum := by decide
  have hdescent : baseEnd_979262 < baseStart_979262 := by decide
  rcases family_descends (prefixWord ++ tailWord_979262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979296 : List Nat := [2, 1, 1, 3, 6, 1, 2, 4]
def baseStart_979296 : Nat := 118140960795 + 979296 * 2 ^ 59
def prefixEnd_979296 : Nat := 4983230072969 + 3 ^ 40 * 979296 * 2
def baseEnd_979296 : Nat := 148992459563112809954461

theorem tailTrace_979296 : CollatzResearch.WordTrace tailWord_979296 prefixEnd_979296 148992459563112809954461 := by
  unfold tailWord_979296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17858929730092658643210871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23811906306790211524281161 17858929730092658643210871)
  ·
    refine ⟨26788394595138987964816307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17858929730092658643210871 26788394595138987964816307)
    ·
      refine ⟨40182591892708481947224461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26788394595138987964816307 40182591892708481947224461)
      ·
        refine ⟨15068471959765680730209173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40182591892708481947224461 15068471959765680730209173)
        ·
          refine ⟨706334623114016284228555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15068471959765680730209173 706334623114016284228555)
          ·
            refine ⟨1059501934671024426342833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706334623114016284228555 1059501934671024426342833)
            ·
              refine ⟨794626451003268319757125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059501934671024426342833 794626451003268319757125)
              ·
                refine ⟨148992459563112809954461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 794626451003268319757125 148992459563112809954461)
                ·
                  rfl

theorem cell20_979296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_979296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979296 prefixEnd_979296 := by exact prefixLift 979296
  have htrace : WordTrace (prefixWord ++ tailWord_979296) baseStart_979296 baseEnd_979296 := by
    simpa [prefixWord, tailWord_979296, baseEnd_979296] using wordTrace_append hprefix tailTrace_979296
  have hstable : (prefixWord ++ tailWord_979296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979296).length < 2 ^ (prefixWord ++ tailWord_979296).sum := by decide
  have hdescent : baseEnd_979296 < baseStart_979296 := by decide
  rcases family_descends (prefixWord ++ tailWord_979296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979359 : List Nat := [1, 1, 2, 5, 1, 1, 1, 8]
def baseStart_979359 : Nat := 118140960795 + 979359 * 2 ^ 59
def prefixEnd_979359 : Nat := 4983230072969 + 3 ^ 40 * 979359 * 2
def baseEnd_979359 : Nat := 149002044535330070254375

theorem tailTrace_979359 : CollatzResearch.WordTrace tailWord_979359 prefixEnd_979359 149002044535330070254375 := by
  unfold tailWord_979359
  simp only [CollatzResearch.WordTrace]
  refine ⟨35720157258957079045965131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23813438172638052697310087 35720157258957079045965131)
  ·
    refine ⟨53580235888435618568947697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35720157258957079045965131 53580235888435618568947697)
    ·
      refine ⟨40185176916326713926710773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53580235888435618568947697 40185176916326713926710773)
      ·
        refine ⟨3767360335905629430629135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40185176916326713926710773 3767360335905629430629135)
        ·
          refine ⟨5651040503858444145943703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3767360335905629430629135 5651040503858444145943703)
          ·
            refine ⟨8476560755787666218915555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651040503858444145943703 8476560755787666218915555)
            ·
              refine ⟨12714841133681499328373333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8476560755787666218915555 12714841133681499328373333)
              ·
                refine ⟨149002044535330070254375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12714841133681499328373333 149002044535330070254375)
                ·
                  rfl

theorem cell20_979359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_979359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979359 prefixEnd_979359 := by exact prefixLift 979359
  have htrace : WordTrace (prefixWord ++ tailWord_979359) baseStart_979359 baseEnd_979359 := by
    simpa [prefixWord, tailWord_979359, baseEnd_979359] using wordTrace_append hprefix tailTrace_979359
  have hstable : (prefixWord ++ tailWord_979359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979359).length < 2 ^ (prefixWord ++ tailWord_979359).sum := by decide
  have hdescent : baseEnd_979359 < baseStart_979359 := by decide
  rcases family_descends (prefixWord ++ tailWord_979359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979383 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 3]
def baseStart_979383 : Nat := 118140960795 + 979383 * 2 ^ 59
def prefixEnd_979383 : Nat := 4983230072969 + 3 ^ 40 * 979383 * 2
def baseEnd_979383 : Nat := 447017087859952793963027

theorem tailTrace_979383 : CollatzResearch.WordTrace tailWord_979383 prefixEnd_979383 447017087859952793963027 := by
  unfold tailWord_979383
  simp only [CollatzResearch.WordTrace]
  refine ⟨35721032610870131144838803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23814021740580087429892535 35721032610870131144838803)
  ·
    refine ⟨53581548916305196717258205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35721032610870131144838803 53581548916305196717258205)
    ·
      refine ⟨20093080843614448768971827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53581548916305196717258205 20093080843614448768971827)
      ·
        refine ⟨30139621265421673153457741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20093080843614448768971827 30139621265421673153457741)
        ·
          refine ⟨11302357974533127432546653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30139621265421673153457741 11302357974533127432546653)
          ·
            refine ⟨4238384240449922787204995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11302357974533127432546653 4238384240449922787204995)
            ·
              refine ⟨6357576360674884180807493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238384240449922787204995 6357576360674884180807493)
              ·
                refine ⟨1192045567626540783901405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6357576360674884180807493 1192045567626540783901405)
                ·
                  refine ⟨447017087859952793963027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192045567626540783901405 447017087859952793963027)
                  ·
                    rfl

theorem cell20_979383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 3].length) (baseStart_979383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979383 prefixEnd_979383 := by exact prefixLift 979383
  have htrace : WordTrace (prefixWord ++ tailWord_979383) baseStart_979383 baseEnd_979383 := by
    simpa [prefixWord, tailWord_979383, baseEnd_979383] using wordTrace_append hprefix tailTrace_979383
  have hstable : (prefixWord ++ tailWord_979383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979383).length < 2 ^ (prefixWord ++ tailWord_979383).sum := by decide
  have hdescent : baseEnd_979383 < baseStart_979383 := by decide
  rcases family_descends (prefixWord ++ tailWord_979383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979410 : List Nat := [3, 2, 2, 4, 1, 1, 3, 4]
def baseStart_979410 : Nat := 118140960795 + 979410 * 2 ^ 59
def prefixEnd_979410 : Nat := 4983230072969 + 3 ^ 40 * 979410 * 2
def baseEnd_979410 : Nat := 149009803798553566687639

theorem tailTrace_979410 : CollatzResearch.WordTrace tailWord_979410 prefixEnd_979410 149009803798553566687639 := by
  unfold tailWord_979410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8930504345443078689017921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23814678254514876504047789 8930504345443078689017921)
  ·
    refine ⟨6697878259082309016763441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8930504345443078689017921 6697878259082309016763441)
    ·
      refine ⟨5023408694311731762572581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6697878259082309016763441 5023408694311731762572581)
      ·
        refine ⟨941889130183449705482359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5023408694311731762572581 941889130183449705482359)
        ·
          refine ⟨1412833695275174558223539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941889130183449705482359 1412833695275174558223539)
          ·
            refine ⟨2119250542912761837335309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412833695275174558223539 2119250542912761837335309)
            ·
              refine ⟨794718953592285689000741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2119250542912761837335309 794718953592285689000741)
              ·
                refine ⟨149009803798553566687639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 794718953592285689000741 149009803798553566687639)
                ·
                  rfl

theorem cell20_979410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_979410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979410 prefixEnd_979410 := by exact prefixLift 979410
  have htrace : WordTrace (prefixWord ++ tailWord_979410) baseStart_979410 baseEnd_979410 := by
    simpa [prefixWord, tailWord_979410, baseEnd_979410] using wordTrace_append hprefix tailTrace_979410
  have hstable : (prefixWord ++ tailWord_979410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979410).length < 2 ^ (prefixWord ++ tailWord_979410).sum := by decide
  have hdescent : baseEnd_979410 < baseStart_979410 := by decide
  rcases family_descends (prefixWord ++ tailWord_979410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979421 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 5]
def baseStart_979421 : Nat := 118140960795 + 979421 * 2 ^ 59
def prefixEnd_979421 : Nat := 4983230072969 + 3 ^ 40 * 979421 * 2
def baseEnd_979421 : Nat := 447034432095393550696205

theorem tailTrace_979421 : CollatzResearch.WordTrace tailWord_979421 prefixEnd_979421 447034432095393550696205 := by
  unfold tailWord_979421
  simp only [CollatzResearch.WordTrace]
  refine ⟨35722418584732463634722117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23814945723154975756481411 35722418584732463634722117)
  ·
    refine ⟨6697953484637336931510397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35722418584732463634722117 6697953484637336931510397)
    ·
      refine ⟨2511732556739001349316399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6697953484637336931510397 2511732556739001349316399)
      ·
        refine ⟨3767598835108502023974599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511732556739001349316399 3767598835108502023974599)
        ·
          refine ⟨5651398252662753035961899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3767598835108502023974599 5651398252662753035961899)
          ·
            refine ⟨8477097378994129553942849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651398252662753035961899 8477097378994129553942849)
            ·
              refine ⟨6357823034245597165457137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8477097378994129553942849 6357823034245597165457137)
              ·
                refine ⟨4768367275684197874092853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6357823034245597165457137 4768367275684197874092853)
                ·
                  refine ⟨447034432095393550696205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4768367275684197874092853 447034432095393550696205)
                  ·
                    rfl

theorem cell20_979421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_979421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979421 prefixEnd_979421 := by exact prefixLift 979421
  have htrace : WordTrace (prefixWord ++ tailWord_979421) baseStart_979421 baseEnd_979421 := by
    simpa [prefixWord, tailWord_979421, baseEnd_979421] using wordTrace_append hprefix tailTrace_979421
  have hstable : (prefixWord ++ tailWord_979421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979421).length < 2 ^ (prefixWord ++ tailWord_979421).sum := by decide
  have hdescent : baseEnd_979421 < baseStart_979421 := by decide
  rcases family_descends (prefixWord ++ tailWord_979421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979438 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_979438 : Nat := 118140960795 + 979438 * 2 ^ 59
def prefixEnd_979438 : Nat := 4983230072969 + 3 ^ 40 * 979438 * 2
def baseEnd_979438 : Nat := 447042191358617047129469

theorem tailTrace_979438 : CollatzResearch.WordTrace tailWord_979438 prefixEnd_979438 447042191358617047129469 := by
  unfold tailWord_979438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465379828208859442261371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23815359083780583692060645 4465379828208859442261371)
  ·
    refine ⟨6698069742313289163392057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4465379828208859442261371 6698069742313289163392057)
    ·
      refine ⟨5023552306734966872544043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6698069742313289163392057 5023552306734966872544043)
      ·
        refine ⟨7535328460102450308816065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5023552306734966872544043 7535328460102450308816065)
        ·
          refine ⟨5651496345076837731612049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7535328460102450308816065 5651496345076837731612049)
          ·
            refine ⟨4238622258807628298709037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5651496345076837731612049 4238622258807628298709037)
            ·
              refine ⟨1589483347052860612015889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4238622258807628298709037 1589483347052860612015889)
              ·
                refine ⟨1192112510289645459011917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1589483347052860612015889 1192112510289645459011917)
                ·
                  refine ⟨447042191358617047129469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192112510289645459011917 447042191358617047129469)
                  ·
                    rfl

theorem cell20_979438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_979438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979438 prefixEnd_979438 := by exact prefixLift 979438
  have htrace : WordTrace (prefixWord ++ tailWord_979438) baseStart_979438 baseEnd_979438 := by
    simpa [prefixWord, tailWord_979438, baseEnd_979438] using wordTrace_append hprefix tailTrace_979438
  have hstable : (prefixWord ++ tailWord_979438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979438).length < 2 ^ (prefixWord ++ tailWord_979438).sum := by decide
  have hdescent : baseEnd_979438 < baseStart_979438 := by decide
  rcases family_descends (prefixWord ++ tailWord_979438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979466 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_979466 : Nat := 118140960795 + 979466 * 2 ^ 59
def prefixEnd_979466 : Nat := 4983230072969 + 3 ^ 40 * 979466 * 2
def baseEnd_979466 : Nat := 447054971321573394196021

theorem tailTrace_979466 : CollatzResearch.WordTrace tailWord_979466 prefixEnd_979466 447054971321573394196021 := by
  unfold tailWord_979466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8931014967392359080027563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23816039913046290880073501 8931014967392359080027563)
  ·
    refine ⟨13396522451088538620041345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8931014967392359080027563 13396522451088538620041345)
    ·
      refine ⟨10047391838316403965031009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13396522451088538620041345 10047391838316403965031009)
      ·
        refine ⟨7535543878737302973773257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10047391838316403965031009 7535543878737302973773257)
        ·
          refine ⟨5651657909052977230329943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7535543878737302973773257 5651657909052977230329943)
          ·
            refine ⟨8477486863579465845494915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651657909052977230329943 8477486863579465845494915)
            ·
              refine ⟨12716230295369198768242373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8477486863579465845494915 12716230295369198768242373)
              ·
                refine ⟨2384293180381724769045445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12716230295369198768242373 2384293180381724769045445)
                ·
                  refine ⟨447054971321573394196021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2384293180381724769045445 447054971321573394196021)
                  ·
                    rfl

theorem cell20_979466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_979466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979466 prefixEnd_979466 := by exact prefixLift 979466
  have htrace : WordTrace (prefixWord ++ tailWord_979466) baseStart_979466 baseEnd_979466 := by
    simpa [prefixWord, tailWord_979466, baseEnd_979466] using wordTrace_append hprefix tailTrace_979466
  have hstable : (prefixWord ++ tailWord_979466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979466).length < 2 ^ (prefixWord ++ tailWord_979466).sum := by decide
  have hdescent : baseEnd_979466 < baseStart_979466 := by decide
  rcases family_descends (prefixWord ++ tailWord_979466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979476 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 5]
def baseStart_979476 : Nat := 118140960795 + 979476 * 2 ^ 59
def prefixEnd_979476 : Nat := 4983230072969 + 3 ^ 40 * 979476 * 2
def baseEnd_979476 : Nat := 447059535594057803862647

theorem tailTrace_979476 : CollatzResearch.WordTrace tailWord_979476 prefixEnd_979476 447059535594057803862647 := by
  unfold tailWord_979476
  simp only [CollatzResearch.WordTrace]
  refine ⟨17862212299766604013987141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23816283066355472018649521 17862212299766604013987141)
  ·
    refine ⟨3349164806206238252622589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17862212299766604013987141 3349164806206238252622589)
    ·
      refine ⟨1255936802327339344733471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3349164806206238252622589 1255936802327339344733471)
      ·
        refine ⟨1883905203491009017100207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255936802327339344733471 1883905203491009017100207)
        ·
          refine ⟨2825857805236513525650311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883905203491009017100207 2825857805236513525650311)
          ·
            refine ⟨4238786707854770288475467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825857805236513525650311 4238786707854770288475467)
            ·
              refine ⟨6358180061782155432713201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238786707854770288475467 6358180061782155432713201)
              ·
                refine ⟨4768635046336616574534901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6358180061782155432713201 4768635046336616574534901)
                ·
                  refine ⟨447059535594057803862647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4768635046336616574534901 447059535594057803862647)
                  ·
                    rfl

theorem cell20_979476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_979476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979476 prefixEnd_979476 := by exact prefixLift 979476
  have htrace : WordTrace (prefixWord ++ tailWord_979476) baseStart_979476 baseEnd_979476 := by
    simpa [prefixWord, tailWord_979476, baseEnd_979476] using wordTrace_append hprefix tailTrace_979476
  have hstable : (prefixWord ++ tailWord_979476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979476).length < 2 ^ (prefixWord ++ tailWord_979476).sum := by decide
  have hdescent : baseEnd_979476 < baseStart_979476 := by decide
  rcases family_descends (prefixWord ++ tailWord_979476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979504 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_979504 : Nat := 118140960795 + 979504 * 2 ^ 59
def prefixEnd_979504 : Nat := 4983230072969 + 3 ^ 40 * 979504 * 2
def baseEnd_979504 : Nat := 447072315557014150929199

theorem tailTrace_979504 : CollatzResearch.WordTrace tailWord_979504 prefixEnd_979504 447072315557014150929199 := by
  unfold tailWord_979504
  simp only [CollatzResearch.WordTrace]
  refine ⟨17862722921715884404996783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23816963895621179206662377 17862722921715884404996783)
  ·
    refine ⟨26794084382573826607495175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17862722921715884404996783 26794084382573826607495175)
    ·
      refine ⟨40191126573860739911242763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26794084382573826607495175 40191126573860739911242763)
      ·
        refine ⟨60286689860791109866864145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40191126573860739911242763 60286689860791109866864145)
        ·
          refine ⟨45215017395593332400148109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60286689860791109866864145 45215017395593332400148109)
          ·
            refine ⟨16955631523347499650055541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45215017395593332400148109 16955631523347499650055541)
            ·
              refine ⟨1589590455313828092192707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16955631523347499650055541 1589590455313828092192707)
              ·
                refine ⟨2384385682970742138289061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589590455313828092192707 2384385682970742138289061)
                ·
                  refine ⟨447072315557014150929199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2384385682970742138289061 447072315557014150929199)
                  ·
                    rfl

theorem cell20_979504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_979504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979504 prefixEnd_979504 := by exact prefixLift 979504
  have htrace : WordTrace (prefixWord ++ tailWord_979504) baseStart_979504 baseEnd_979504 := by
    simpa [prefixWord, tailWord_979504, baseEnd_979504] using wordTrace_append hprefix tailTrace_979504
  have hstable : (prefixWord ++ tailWord_979504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979504).length < 2 ^ (prefixWord ++ tailWord_979504).sum := by decide
  have hdescent : baseEnd_979504 < baseStart_979504 := by decide
  rcases family_descends (prefixWord ++ tailWord_979504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979510 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_979510 : Nat := 118140960795 + 979510 * 2 ^ 59
def prefixEnd_979510 : Nat := 4983230072969 + 3 ^ 40 * 979510 * 2
def baseEnd_979510 : Nat := 447075054120504796729175

theorem tailTrace_979510 : CollatzResearch.WordTrace tailWord_979510 prefixEnd_979510 447075054120504796729175 := by
  unfold tailWord_979510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232854042588126989669499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23817109787606687889807989 2232854042588126989669499)
  ·
    refine ⟨3349281063882190484504249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2232854042588126989669499 3349281063882190484504249)
    ·
      refine ⟨2511960797911642863378187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3349281063882190484504249 2511960797911642863378187)
      ·
        refine ⟨3767941196867464295067281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511960797911642863378187 3767941196867464295067281)
        ·
          refine ⟨2825955897650598221300461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3767941196867464295067281 2825955897650598221300461)
          ·
            refine ⟨1059733461618974332987673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2825955897650598221300461 1059733461618974332987673)
            ·
              refine ⟨794800096214230749740755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059733461618974332987673 794800096214230749740755)
              ·
                refine ⟨1192200144321346124611133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794800096214230749740755 1192200144321346124611133)
                ·
                  refine ⟨447075054120504796729175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1192200144321346124611133 447075054120504796729175)
                  ·
                    rfl

theorem cell20_979510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_979510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979510 prefixEnd_979510 := by exact prefixLift 979510
  have htrace : WordTrace (prefixWord ++ tailWord_979510) baseStart_979510 baseEnd_979510 := by
    simpa [prefixWord, tailWord_979510, baseEnd_979510] using wordTrace_append hprefix tailTrace_979510
  have hstable : (prefixWord ++ tailWord_979510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979510).length < 2 ^ (prefixWord ++ tailWord_979510).sum := by decide
  have hdescent : baseEnd_979510 < baseStart_979510 := by decide
  rcases family_descends (prefixWord ++ tailWord_979510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979511 : List Nat := [1, 1, 3, 1, 2, 3, 4, 5]
def baseStart_979511 : Nat := 118140960795 + 979511 * 2 ^ 59
def prefixEnd_979511 : Nat := 4983230072969 + 3 ^ 40 * 979511 * 2
def baseEnd_979511 : Nat := 149025170182584412565279

theorem tailTrace_979511 : CollatzResearch.WordTrace tailWord_979511 prefixEnd_979511 149025170182584412565279 := by
  unfold tailWord_979511
  simp only [CollatzResearch.WordTrace]
  refine ⟨35725701154406409005498387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23817134102937606003665591 35725701154406409005498387)
  ·
    refine ⟨53588551731609613508247581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35725701154406409005498387 53588551731609613508247581)
    ·
      refine ⟨20095706899353605065592843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53588551731609613508247581 20095706899353605065592843)
      ·
        refine ⟨30143560349030407598389265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20095706899353605065592843 30143560349030407598389265)
        ·
          refine ⟨22607670261772805698791949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30143560349030407598389265 22607670261772805698791949)
          ·
            refine ⟨8477876348164802137046981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22607670261772805698791949 8477876348164802137046981)
            ·
              refine ⟨1589601815280900400696309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8477876348164802137046981 1589601815280900400696309)
              ·
                refine ⟨149025170182584412565279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1589601815280900400696309 149025170182584412565279)
                ·
                  rfl

theorem cell20_979511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_979511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_979511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_979511 prefixEnd_979511 := by exact prefixLift 979511
  have htrace : WordTrace (prefixWord ++ tailWord_979511) baseStart_979511 baseEnd_979511 := by
    simpa [prefixWord, tailWord_979511, baseEnd_979511] using wordTrace_append hprefix tailTrace_979511
  have hstable : (prefixWord ++ tailWord_979511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979511).length < 2 ^ (prefixWord ++ tailWord_979511).sum := by decide
  have hdescent : baseEnd_979511 < baseStart_979511 := by decide
  rcases family_descends (prefixWord ++ tailWord_979511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
