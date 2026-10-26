import V185TrunkScan23Chunk0788

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4667042 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_4667042 : Nat := 118140960795 + 4667042 * 2 ^ 59
def prefixEnd_4667042 : Nat := 4983230072969 + 3 ^ 40 * 4667042 * 2
def baseEnd_4667042 : Nat := 798811926906944803470557

theorem tailTrace_4667042 : CollatzResearch.WordTrace tailWord_4667042 prefixEnd_4667042 798811926906944803470557 := by
  unfold tailWord_4667042
  simp only [CollatzResearch.WordTrace]
  refine ⟨42555251489527844040234845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113480670638740917440626253 42555251489527844040234845)
  ·
    refine ⟨15958219308572941515088067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42555251489527844040234845 15958219308572941515088067)
    ·
      refine ⟨23937328962859412272632101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15958219308572941515088067 23937328962859412272632101)
      ·
        refine ⟨4488249180536139801118519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23937328962859412272632101 4488249180536139801118519)
        ·
          refine ⟨6732373770804209701677779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4488249180536139801118519 6732373770804209701677779)
          ·
            refine ⟨10098560656206314552516669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6732373770804209701677779 10098560656206314552516669)
            ·
              refine ⟨3786960246077367957193751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10098560656206314552516669 3786960246077367957193751)
              ·
                refine ⟨5680440369116051935790627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3786960246077367957193751 5680440369116051935790627)
                ·
                  refine ⟨8520660553674077903685941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5680440369116051935790627 8520660553674077903685941)
                  ·
                    refine ⟨798811926906944803470557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8520660553674077903685941 798811926906944803470557)
                    ·
                      rfl

theorem cell23_4667042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_4667042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667042 prefixEnd_4667042 := by exact prefixLift 4667042
  have htrace : WordTrace (prefixWord ++ tailWord_4667042) baseStart_4667042 baseEnd_4667042 := by
    simpa [prefixWord, tailWord_4667042, baseEnd_4667042] using wordTrace_append hprefix tailTrace_4667042
  have hstable : (prefixWord ++ tailWord_4667042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667042).length < 2 ^ (prefixWord ++ tailWord_4667042).sum := by decide
  have hdescent : baseEnd_4667042 < baseStart_4667042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667085 : List Nat := [1, 6, 2, 1, 1, 2, 3, 7]
def baseStart_4667085 : Nat := 118140960795 + 4667085 * 2 ^ 59
def prefixEnd_4667085 : Nat := 4983230072969 + 3 ^ 40 * 4667085 * 2
def baseEnd_4667085 : Nat := 88757698532925101561999

theorem tailTrace_4667085 : CollatzResearch.WordTrace tailWord_4667085 prefixEnd_4667085 88757698532925101561999 := by
  unfold tailWord_4667085
  simp only [CollatzResearch.WordTrace]
  refine ⟨170222574296955594504754709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113481716197970396336503139 170222574296955594504754709)
  ·
    refine ⟨7979183170169793492410377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 170222574296955594504754709 7979183170169793492410377)
    ·
      refine ⟨5984387377627345119307783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7979183170169793492410377 5984387377627345119307783)
      ·
        refine ⟨8976581066441017678961675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5984387377627345119307783 8976581066441017678961675)
        ·
          refine ⟨13464871599661526518442513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8976581066441017678961675 13464871599661526518442513)
          ·
            refine ⟨10098653699746144888831885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13464871599661526518442513 10098653699746144888831885)
            ·
              refine ⟨3786995137404804333311957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10098653699746144888831885 3786995137404804333311957)
              ·
                refine ⟨88757698532925101561999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3786995137404804333311957 88757698532925101561999)
                ·
                  rfl

theorem cell23_4667085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 7].length) (baseStart_4667085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667085 prefixEnd_4667085 := by exact prefixLift 4667085
  have htrace : WordTrace (prefixWord ++ tailWord_4667085) baseStart_4667085 baseEnd_4667085 := by
    simpa [prefixWord, tailWord_4667085, baseEnd_4667085] using wordTrace_append hprefix tailTrace_4667085
  have hstable : (prefixWord ++ tailWord_4667085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667085).length < 2 ^ (prefixWord ++ tailWord_4667085).sum := by decide
  have hdescent : baseEnd_4667085 < baseStart_4667085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667112 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_4667112 : Nat := 118140960795 + 4667112 * 2 ^ 59
def prefixEnd_4667112 : Nat := 4983230072969 + 3 ^ 40 * 4667112 * 2
def baseEnd_4667112 : Nat := 2396471724366649136536349

theorem tailTrace_4667112 : CollatzResearch.WordTrace tailWord_4667112 prefixEnd_4667112 2396471724366649136536349 := by
  unfold tailWord_4667112
  simp only [CollatzResearch.WordTrace]
  refine ⟨85111779533928889057993795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113482372711905185410658393 85111779533928889057993795)
  ·
    refine ⟨127667669300893333586990693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85111779533928889057993795 127667669300893333586990693)
    ·
      refine ⟨23937687993917500047560755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127667669300893333586990693 23937687993917500047560755)
      ·
        refine ⟨35906531990876250071341133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23937687993917500047560755 35906531990876250071341133)
        ·
          refine ⟨13464949496578593776752925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35906531990876250071341133 13464949496578593776752925)
          ·
            refine ⟨5049356061216972666282347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13464949496578593776752925 5049356061216972666282347)
            ·
              refine ⟨7574034091825458999423521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049356061216972666282347 7574034091825458999423521)
              ·
                refine ⟨5680525568869094249567641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7574034091825458999423521 5680525568869094249567641)
                ·
                  refine ⟨4260394176651820687175731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5680525568869094249567641 4260394176651820687175731)
                  ·
                    refine ⟨6390591264977731030763597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4260394176651820687175731 6390591264977731030763597)
                    ·
                      refine ⟨2396471724366649136536349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6390591264977731030763597 2396471724366649136536349)
                      ·
                        rfl

theorem cell23_4667112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_4667112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667112 prefixEnd_4667112 := by exact prefixLift 4667112
  have htrace : WordTrace (prefixWord ++ tailWord_4667112) baseStart_4667112 baseEnd_4667112 := by
    simpa [prefixWord, tailWord_4667112, baseEnd_4667112] using wordTrace_append hprefix tailTrace_4667112
  have hstable : (prefixWord ++ tailWord_4667112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667112).length < 2 ^ (prefixWord ++ tailWord_4667112).sum := by decide
  have hdescent : baseEnd_4667112 < baseStart_4667112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667135 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 2, 2, 2]
def baseStart_4667135 : Nat := 118140960795 + 4667135 * 2 ^ 59
def prefixEnd_4667135 : Nat := 4983230072969 + 3 ^ 40 * 4667135 * 2
def baseEnd_4667135 : Nat := 2396483534421702546548743

theorem tailTrace_4667135 : CollatzResearch.WordTrace tailWord_4667135 prefixEnd_4667135 2396483534421702546548743 := by
  unfold tailWord_4667135
  simp only [CollatzResearch.WordTrace]
  refine ⟨170224397946774453044074859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113482931964516302029383239 170224397946774453044074859)
  ·
    refine ⟨255336596920161679566112289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170224397946774453044074859 255336596920161679566112289)
    ·
      refine ⟨191502447690121259674584217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255336596920161679566112289 191502447690121259674584217)
      ·
        refine ⟨143626835767590944755938163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191502447690121259674584217 143626835767590944755938163)
        ·
          refine ⟨215440253651386417133907245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143626835767590944755938163 215440253651386417133907245)
          ·
            refine ⟨80790095119269906425215217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215440253651386417133907245 80790095119269906425215217)
            ·
              refine ⟨60592571339452429818911413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80790095119269906425215217 60592571339452429818911413)
              ·
                refine ⟨5680553563073665295522945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60592571339452429818911413 5680553563073665295522945)
                ·
                  refine ⟨4260415172305248971642209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5680553563073665295522945 4260415172305248971642209)
                  ·
                    refine ⟨3195311379228936728731657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4260415172305248971642209 3195311379228936728731657)
                    ·
                      refine ⟨2396483534421702546548743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3195311379228936728731657 2396483534421702546548743)
                      ·
                        rfl

theorem cell23_4667135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 2, 2].length) (baseStart_4667135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667135 prefixEnd_4667135 := by exact prefixLift 4667135
  have htrace : WordTrace (prefixWord ++ tailWord_4667135) baseStart_4667135 baseEnd_4667135 := by
    simpa [prefixWord, tailWord_4667135, baseEnd_4667135] using wordTrace_append hprefix tailTrace_4667135
  have hstable : (prefixWord ++ tailWord_4667135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667135).length < 2 ^ (prefixWord ++ tailWord_4667135).sum := by decide
  have hdescent : baseEnd_4667135 < baseStart_4667135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667138 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_4667138 : Nat := 118140960795 + 4667138 * 2 ^ 59
def prefixEnd_4667138 : Nat := 4983230072969 + 3 ^ 40 * 4667138 * 2
def baseEnd_4667138 : Nat := 2396485074863666034811229

theorem tailTrace_4667138 : CollatzResearch.WordTrace tailWord_4667138 prefixEnd_4667138 2396485074863666034811229 := by
  unfold tailWord_4667138
  simp only [CollatzResearch.WordTrace]
  refine ⟨42556126841440896139108517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113483004910509056370956045 42556126841440896139108517)
  ·
    refine ⟨7979273782770168026082847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42556126841440896139108517 7979273782770168026082847)
    ·
      refine ⟨11968910674155252039124271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7979273782770168026082847 11968910674155252039124271)
      ·
        refine ⟨17953366011232878058686407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11968910674155252039124271 17953366011232878058686407)
        ·
          refine ⟨26930049016849317088029611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17953366011232878058686407 26930049016849317088029611)
          ·
            refine ⟨40395073525273975632044417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26930049016849317088029611 40395073525273975632044417)
            ·
              refine ⟨30296305143955481724033313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40395073525273975632044417 30296305143955481724033313)
              ·
                refine ⟨22722228857966611293024985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30296305143955481724033313 22722228857966611293024985)
                ·
                  refine ⟨17041671643474958469768739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22722228857966611293024985 17041671643474958469768739)
                  ·
                    refine ⟨25562507465212437704653109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17041671643474958469768739 25562507465212437704653109)
                    ·
                      refine ⟨2396485074863666034811229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25562507465212437704653109 2396485074863666034811229)
                      ·
                        rfl

theorem cell23_4667138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_4667138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667138 prefixEnd_4667138 := by exact prefixLift 4667138
  have htrace : WordTrace (prefixWord ++ tailWord_4667138) baseStart_4667138 baseEnd_4667138 := by
    simpa [prefixWord, tailWord_4667138, baseEnd_4667138] using wordTrace_append hprefix tailTrace_4667138
  have hstable : (prefixWord ++ tailWord_4667138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667138).length < 2 ^ (prefixWord ++ tailWord_4667138).sum := by decide
  have hdescent : baseEnd_4667138 < baseStart_4667138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667151 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 3]
def baseStart_4667151 : Nat := 118140960795 + 4667151 * 2 ^ 59
def prefixEnd_4667151 : Nat := 4983230072969 + 3 ^ 40 * 4667151 * 2
def baseEnd_4667151 : Nat := 2396491750112174483948669

theorem tailTrace_4667151 : CollatzResearch.WordTrace tailWord_4667151 prefixEnd_4667151 2396491750112174483948669 := by
  unfold tailWord_4667151
  simp only [CollatzResearch.WordTrace]
  refine ⟨170224981514716487776657307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113483321009810991851104871 170224981514716487776657307)
  ·
    refine ⟨255337472272074731664985961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170224981514716487776657307 255337472272074731664985961)
    ·
      refine ⟨191503104204056048748739471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255337472272074731664985961 191503104204056048748739471)
      ·
        refine ⟨287254656306084073123109207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191503104204056048748739471 287254656306084073123109207)
        ·
          refine ⟨430881984459126109684663811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287254656306084073123109207 430881984459126109684663811)
          ·
            refine ⟨646322976688689164526995717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430881984459126109684663811 646322976688689164526995717)
            ·
              refine ⟨121185558129129218348811697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 646322976688689164526995717 121185558129129218348811697)
              ·
                refine ⟨90889168596846913761608773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121185558129129218348811697 90889168596846913761608773)
                ·
                  refine ⟨17041719111908796330301645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90889168596846913761608773 17041719111908796330301645)
                  ·
                    refine ⟨6390644666965798623863117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17041719111908796330301645 6390644666965798623863117)
                    ·
                      refine ⟨2396491750112174483948669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6390644666965798623863117 2396491750112174483948669)
                      ·
                        rfl

theorem cell23_4667151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 3].length) (baseStart_4667151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667151 prefixEnd_4667151 := by exact prefixLift 4667151
  have htrace : WordTrace (prefixWord ++ tailWord_4667151) baseStart_4667151 baseEnd_4667151 := by
    simpa [prefixWord, tailWord_4667151, baseEnd_4667151] using wordTrace_append hprefix tailTrace_4667151
  have hstable : (prefixWord ++ tailWord_4667151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667151).length < 2 ^ (prefixWord ++ tailWord_4667151).sum := by decide
  have hdescent : baseEnd_4667151 < baseStart_4667151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667171 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 4, 5]
def baseStart_4667171 : Nat := 118140960795 + 4667171 * 2 ^ 59
def prefixEnd_4667171 : Nat := 4983230072969 + 3 ^ 40 * 4667171 * 2
def baseEnd_4667171 : Nat := 798834006575088135232859

theorem tailTrace_4667171 : CollatzResearch.WordTrace tailWord_4667171 prefixEnd_4667171 798834006575088135232859 := by
  unfold tailWord_4667171
  simp only [CollatzResearch.WordTrace]
  refine ⟨170225710974644031192385367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113483807316429354128256911 170225710974644031192385367)
  ·
    refine ⟨255338566461966046788578051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170225710974644031192385367 255338566461966046788578051)
    ·
      refine ⟨383007849692949070182867077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255338566461966046788578051 383007849692949070182867077)
      ·
        refine ⟨71813971817427950659287577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 383007849692949070182867077 71813971817427950659287577)
        ·
          refine ⟨53860478863070962994465683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71813971817427950659287577 53860478863070962994465683)
          ·
            refine ⟨80790718294606444491698525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53860478863070962994465683 80790718294606444491698525)
            ·
              refine ⟨30296519360477416684386947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80790718294606444491698525 30296519360477416684386947)
              ·
                refine ⟨45444779040716125026580421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30296519360477416684386947 45444779040716125026580421)
                ·
                  refine ⟨8520896070134273442483829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45444779040716125026580421 8520896070134273442483829)
                  ·
                    refine ⟨798834006575088135232859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8520896070134273442483829 798834006575088135232859)
                    ·
                      rfl

theorem cell23_4667171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 5].length) (baseStart_4667171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667171 prefixEnd_4667171 := by exact prefixLift 4667171
  have htrace : WordTrace (prefixWord ++ tailWord_4667171) baseStart_4667171 baseEnd_4667171 := by
    simpa [prefixWord, tailWord_4667171, baseEnd_4667171] using wordTrace_append hprefix tailTrace_4667171
  have hstable : (prefixWord ++ tailWord_4667171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667171).length < 2 ^ (prefixWord ++ tailWord_4667171).sum := by decide
  have hdescent : baseEnd_4667171 < baseStart_4667171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667191 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_4667191 : Nat := 118140960795 + 4667191 * 2 ^ 59
def prefixEnd_4667191 : Nat := 4983230072969 + 3 ^ 40 * 4667191 * 2
def baseEnd_4667191 : Nat := 2396512289338354327448485

theorem tailTrace_4667191 : CollatzResearch.WordTrace tailWord_4667191 prefixEnd_4667191 2396512289338354327448485 := by
  unfold tailWord_4667191
  simp only [CollatzResearch.WordTrace]
  refine ⟨170226440434571574608113427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113484293623047716405408951 170226440434571574608113427)
  ·
    refine ⟨255339660651857361912170141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170226440434571574608113427 255339660651857361912170141)
    ·
      refine ⟨95752372744446510717063803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255339660651857361912170141 95752372744446510717063803)
      ·
        refine ⟨143628559116669766075595705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95752372744446510717063803 143628559116669766075595705)
        ·
          refine ⟨107721419337502324556696779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143628559116669766075595705 107721419337502324556696779)
          ·
            refine ⟨161582129006253486835045169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107721419337502324556696779 161582129006253486835045169)
            ·
              refine ⟨121186596754690115126283877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161582129006253486835045169 121186596754690115126283877)
              ·
                refine ⟨22722486891504396586178227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121186596754690115126283877 22722486891504396586178227)
                ·
                  refine ⟨34083730337256594879267341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22722486891504396586178227 34083730337256594879267341)
                  ·
                    refine ⟨12781398876471223079725253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34083730337256594879267341 12781398876471223079725253)
                    ·
                      refine ⟨2396512289338354327448485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12781398876471223079725253 2396512289338354327448485)
                      ·
                        rfl

theorem cell23_4667191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_4667191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667191 prefixEnd_4667191 := by exact prefixLift 4667191
  have htrace : WordTrace (prefixWord ++ tailWord_4667191) baseStart_4667191 baseEnd_4667191 := by
    simpa [prefixWord, tailWord_4667191, baseEnd_4667191] using wordTrace_append hprefix tailTrace_4667191
  have hstable : (prefixWord ++ tailWord_4667191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667191).length < 2 ^ (prefixWord ++ tailWord_4667191).sum := by decide
  have hdescent : baseEnd_4667191 < baseStart_4667191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667208 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_4667208 : Nat := 118140960795 + 4667208 * 2 ^ 59
def prefixEnd_4667208 : Nat := 4983230072969 + 3 ^ 40 * 4667208 * 2
def baseEnd_4667208 : Nat := 2396521018509480760935907

theorem tailTrace_4667208 : CollatzResearch.WordTrace tailWord_4667208 prefixEnd_4667208 2396521018509480760935907 := by
  unfold tailWord_4667208
  simp only [CollatzResearch.WordTrace]
  refine ⟨85113530237754993255741139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113484706983673324340988185 85113530237754993255741139)
  ·
    refine ⟨127670295356632489883611709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85113530237754993255741139 127670295356632489883611709)
    ·
      refine ⟨47876360758737183706354391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127670295356632489883611709 47876360758737183706354391)
      ·
        refine ⟨71814541138105775559531587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47876360758737183706354391 71814541138105775559531587)
        ·
          refine ⟨107721811707158663339297381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71814541138105775559531587 107721811707158663339297381)
          ·
            refine ⟨20197839695092249376118259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107721811707158663339297381 20197839695092249376118259)
            ·
              refine ⟨30296759542638374064177389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20197839695092249376118259 30296759542638374064177389)
              ·
                refine ⟨11361284828489390274066521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30296759542638374064177389 11361284828489390274066521)
                ·
                  refine ⟨8520963621367042705549891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11361284828489390274066521 8520963621367042705549891)
                  ·
                    refine ⟨12781445432050564058324837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8520963621367042705549891 12781445432050564058324837)
                    ·
                      refine ⟨2396521018509480760935907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12781445432050564058324837 2396521018509480760935907)
                      ·
                        rfl

theorem cell23_4667208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_4667208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667208 prefixEnd_4667208 := by exact prefixLift 4667208
  have htrace : WordTrace (prefixWord ++ tailWord_4667208) baseStart_4667208 baseEnd_4667208 := by
    simpa [prefixWord, tailWord_4667208, baseEnd_4667208] using wordTrace_append hprefix tailTrace_4667208
  have hstable : (prefixWord ++ tailWord_4667208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667208).length < 2 ^ (prefixWord ++ tailWord_4667208).sum := by decide
  have hdescent : baseEnd_4667208 < baseStart_4667208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667262 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4667262 : Nat := 118140960795 + 4667262 * 2 ^ 59
def prefixEnd_4667262 : Nat := 4983230072969 + 3 ^ 40 * 4667262 * 2
def baseEnd_4667262 : Nat := 2396548746464823549660659

theorem tailTrace_4667262 : CollatzResearch.WordTrace tailWord_4667262 prefixEnd_4667262 2396548746464823549660659 := by
  unfold tailWord_4667262
  simp only [CollatzResearch.WordTrace]
  refine ⟨21278628752164294216743505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113486020011542902489298693 21278628752164294216743505)
  ·
    refine ⟨15958971564123220662557629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21278628752164294216743505 15958971564123220662557629)
    ·
      refine ⟨5984614336546207748459111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15958971564123220662557629 5984614336546207748459111)
      ·
        refine ⟨8976921504819311622688667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5984614336546207748459111 8976921504819311622688667)
        ·
          refine ⟨13465382257228967434033001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8976921504819311622688667 13465382257228967434033001)
          ·
            refine ⟨10099036692921725575524751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13465382257228967434033001 10099036692921725575524751)
            ·
              refine ⟨15148555039382588363287127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10099036692921725575524751 15148555039382588363287127)
              ·
                refine ⟨22722832559073882544930691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15148555039382588363287127 22722832559073882544930691)
                ·
                  refine ⟨34084248838610823817396037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22722832559073882544930691 34084248838610823817396037)
                  ·
                    refine ⟨6390796657239529465761757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34084248838610823817396037 6390796657239529465761757)
                    ·
                      refine ⟨2396548746464823549660659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6390796657239529465761757 2396548746464823549660659)
                      ·
                        rfl

theorem cell23_4667262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4667262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667262 prefixEnd_4667262 := by exact prefixLift 4667262
  have htrace : WordTrace (prefixWord ++ tailWord_4667262) baseStart_4667262 baseEnd_4667262 := by
    simpa [prefixWord, tailWord_4667262, baseEnd_4667262] using wordTrace_append hprefix tailTrace_4667262
  have hstable : (prefixWord ++ tailWord_4667262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667262).length < 2 ^ (prefixWord ++ tailWord_4667262).sum := by decide
  have hdescent : baseEnd_4667262 < baseStart_4667262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667282 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 6]
def baseStart_4667282 : Nat := 118140960795 + 4667282 * 2 ^ 59
def prefixEnd_4667282 : Nat := 4983230072969 + 3 ^ 40 * 4667282 * 2
def baseEnd_4667282 : Nat := 266284335119768163490063

theorem tailTrace_4667282 : CollatzResearch.WordTrace tailWord_4667282 prefixEnd_4667282 266284335119768163490063 := by
  unfold tailWord_4667282
  simp only [CollatzResearch.WordTrace]
  refine ⟨42557439869310474287419025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113486506318161264766450733 42557439869310474287419025)
  ·
    refine ⟨31918079901982855715564269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42557439869310474287419025 31918079901982855715564269)
    ·
      refine ⟨11969279963243570893336601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31918079901982855715564269 11969279963243570893336601)
      ·
        refine ⟨8976959972432678170002451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11969279963243570893336601 8976959972432678170002451)
        ·
          refine ⟨13465439958649017255003677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8976959972432678170002451 13465439958649017255003677)
          ·
            refine ⟨5049539984493381470626379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13465439958649017255003677 5049539984493381470626379)
            ·
              refine ⟨7574309976740072205939569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049539984493381470626379 7574309976740072205939569)
              ·
                refine ⟨5680732482555054154454677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7574309976740072205939569 5680732482555054154454677)
                ·
                  refine ⟨266284335119768163490063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5680732482555054154454677 266284335119768163490063)
                  ·
                    rfl

theorem cell23_4667282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_4667282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667282 prefixEnd_4667282 := by exact prefixLift 4667282
  have htrace : WordTrace (prefixWord ++ tailWord_4667282) baseStart_4667282 baseEnd_4667282 := by
    simpa [prefixWord, tailWord_4667282, baseEnd_4667282] using wordTrace_append hprefix tailTrace_4667282
  have hstable : (prefixWord ++ tailWord_4667282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667282).length < 2 ^ (prefixWord ++ tailWord_4667282).sum := by decide
  have hdescent : baseEnd_4667282 < baseStart_4667282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667285 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 4, 3, 2]
def baseStart_4667285 : Nat := 118140960795 + 4667285 * 2 ^ 59
def prefixEnd_4667285 : Nat := 4983230072969 + 3 ^ 40 * 4667285 * 2
def baseEnd_4667285 : Nat := 2396560556519876959673053

theorem tailTrace_4667285 : CollatzResearch.WordTrace tailWord_4667285 prefixEnd_4667285 2396560556519876959673053 := by
  unfold tailWord_4667285
  simp only [CollatzResearch.WordTrace]
  refine ⟨170229868896231028662035309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113486579264154019108023539 170229868896231028662035309)
  ·
    refine ⟨63836200836086635748263241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170229868896231028662035309 63836200836086635748263241)
    ·
      refine ⟨47877150627064976811197431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63836200836086635748263241 47877150627064976811197431)
      ·
        refine ⟨71815725940597465216796147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47877150627064976811197431 71815725940597465216796147)
        ·
          refine ⟨107723588910896197825194221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71815725940597465216796147 107723588910896197825194221)
          ·
            refine ⟨40396345841586074184447833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107723588910896197825194221 40396345841586074184447833)
            ·
              refine ⟨30297259381189555638335875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40396345841586074184447833 30297259381189555638335875)
              ·
                refine ⟨45445889071784333457503813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30297259381189555638335875 45445889071784333457503813)
                ·
                  refine ⟨8521104200959562523281965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45445889071784333457503813 8521104200959562523281965)
                  ·
                    refine ⟨3195414075359835946230737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8521104200959562523281965 3195414075359835946230737)
                    ·
                      refine ⟨2396560556519876959673053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3195414075359835946230737 2396560556519876959673053)
                      ·
                        rfl

theorem cell23_4667285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_4667285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667285 prefixEnd_4667285 := by exact prefixLift 4667285
  have htrace : WordTrace (prefixWord ++ tailWord_4667285) baseStart_4667285 baseEnd_4667285 := by
    simpa [prefixWord, tailWord_4667285, baseEnd_4667285] using wordTrace_append hprefix tailTrace_4667285
  have hstable : (prefixWord ++ tailWord_4667285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667285).length < 2 ^ (prefixWord ++ tailWord_4667285).sum := by decide
  have hdescent : baseEnd_4667285 < baseStart_4667285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667286 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_4667286 : Nat := 118140960795 + 4667286 * 2 ^ 59
def prefixEnd_4667286 : Nat := 4983230072969 + 3 ^ 40 * 4667286 * 2
def baseEnd_4667286 : Nat := 798853690000177151920183

theorem tailTrace_4667286 : CollatzResearch.WordTrace tailWord_4667286 prefixEnd_4667286 798853690000177151920183 := by
  unfold tailWord_4667286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10639369085576712864551357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113486603579484937221881141 10639369085576712864551357)
  ·
    refine ⟨3989763407091267324206759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10639369085576712864551357 3989763407091267324206759)
    ·
      refine ⟨5984645110636900986310139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3989763407091267324206759 5984645110636900986310139)
      ·
        refine ⟨8976967665955351479465209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5984645110636900986310139 8976967665955351479465209)
        ·
          refine ⟨6732725749466513609598907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8976967665955351479465209 6732725749466513609598907)
          ·
            refine ⟨10099088624199770414398361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6732725749466513609598907 10099088624199770414398361)
            ·
              refine ⟨7574316468149827810798771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10099088624199770414398361 7574316468149827810798771)
              ·
                refine ⟨11361474702224741716198157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7574316468149827810798771 11361474702224741716198157)
                ·
                  refine ⟨4260553013334278143574309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11361474702224741716198157 4260553013334278143574309)
                  ·
                    refine ⟨798853690000177151920183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4260553013334278143574309 798853690000177151920183)
                    ·
                      rfl

theorem cell23_4667286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_4667286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667286 prefixEnd_4667286 := by exact prefixLift 4667286
  have htrace : WordTrace (prefixWord ++ tailWord_4667286) baseStart_4667286 baseEnd_4667286 := by
    simpa [prefixWord, tailWord_4667286, baseEnd_4667286] using wordTrace_append hprefix tailTrace_4667286
  have hstable : (prefixWord ++ tailWord_4667286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667286).length < 2 ^ (prefixWord ++ tailWord_4667286).sum := by decide
  have hdescent : baseEnd_4667286 < baseStart_4667286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667292 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_4667292 : Nat := 118140960795 + 4667292 * 2 ^ 59
def prefixEnd_4667292 : Nat := 4983230072969 + 3 ^ 40 * 4667292 * 2
def baseEnd_4667292 : Nat := 2396564150884458432285521

theorem tailTrace_4667292 : CollatzResearch.WordTrace tailWord_4667292 prefixEnd_4667292 2396564150884458432285521 := by
  unfold tailWord_4667292
  simp only [CollatzResearch.WordTrace]
  refine ⟨85115062103602834428770065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113486749471470445905026753 85115062103602834428770065)
  ·
    refine ⟨63836296577702125821577549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85115062103602834428770065 63836296577702125821577549)
    ·
      refine ⟨23938611216638297183091581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63836296577702125821577549 23938611216638297183091581)
      ·
        refine ⟨8976979206239361443659343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23938611216638297183091581 8976979206239361443659343)
        ·
          refine ⟨13465468809359042165489015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8976979206239361443659343 13465468809359042165489015)
          ·
            refine ⟨20198203214038563248233523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13465468809359042165489015 20198203214038563248233523)
            ·
              refine ⟨30297304821057844872350285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20198203214038563248233523 30297304821057844872350285)
              ·
                refine ⟨11361489307896691827131357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30297304821057844872350285 11361489307896691827131357)
                ·
                  refine ⟨4260558490461259435174259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11361489307896691827131357 4260558490461259435174259)
                  ·
                    refine ⟨6390837735691889152761389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4260558490461259435174259 6390837735691889152761389)
                    ·
                      refine ⟨2396564150884458432285521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6390837735691889152761389 2396564150884458432285521)
                      ·
                        rfl

theorem cell23_4667292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_4667292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667292 prefixEnd_4667292 := by exact prefixLift 4667292
  have htrace : WordTrace (prefixWord ++ tailWord_4667292) baseStart_4667292 baseEnd_4667292 := by
    simpa [prefixWord, tailWord_4667292, baseEnd_4667292] using wordTrace_append hprefix tailTrace_4667292
  have hstable : (prefixWord ++ tailWord_4667292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667292).length < 2 ^ (prefixWord ++ tailWord_4667292).sum := by decide
  have hdescent : baseEnd_4667292 < baseStart_4667292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667308 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 8, 4]
def baseStart_4667308 : Nat := 118140960795 + 4667308 * 2 ^ 59
def prefixEnd_4667308 : Nat := 4983230072969 + 3 ^ 40 * 4667308 * 2
def baseEnd_4667308 : Nat := 798857455524976789895149

theorem tailTrace_4667308 : CollatzResearch.WordTrace tailWord_4667308 prefixEnd_4667308 798857455524976789895149 := by
  unfold tailWord_4667308
  simp only [CollatzResearch.WordTrace]
  refine ⟨85115353887573851795061289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113487138516765135726748385 85115353887573851795061289)
  ·
    refine ⟨63836515415680388846295967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85115353887573851795061289 63836515415680388846295967)
    ·
      refine ⟨95754773123520583269443951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63836515415680388846295967 95754773123520583269443951)
      ·
        refine ⟨143632159685280874904165927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95754773123520583269443951 143632159685280874904165927)
        ·
          refine ⟨215448239527921312356248891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143632159685280874904165927 215448239527921312356248891)
          ·
            refine ⟨323172359291881968534373337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215448239527921312356248891 323172359291881968534373337)
            ·
              refine ⟨242379269468911476400780003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323172359291881968534373337 242379269468911476400780003)
              ·
                refine ⟨363568904203367214601170005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242379269468911476400780003 363568904203367214601170005)
                ·
                  refine ⟨4260573096133209546107461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 363568904203367214601170005 4260573096133209546107461)
                  ·
                    refine ⟨798857455524976789895149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4260573096133209546107461 798857455524976789895149)
                    ·
                      rfl

theorem cell23_4667308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_4667308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667308 prefixEnd_4667308 := by exact prefixLift 4667308
  have htrace : WordTrace (prefixWord ++ tailWord_4667308) baseStart_4667308 baseEnd_4667308 := by
    simpa [prefixWord, tailWord_4667308, baseEnd_4667308] using wordTrace_append hprefix tailTrace_4667308
  have hstable : (prefixWord ++ tailWord_4667308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667308).length < 2 ^ (prefixWord ++ tailWord_4667308).sum := by decide
  have hdescent : baseEnd_4667308 < baseStart_4667308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667315 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 4]
def baseStart_4667315 : Nat := 118140960795 + 4667315 * 2 ^ 59
def prefixEnd_4667315 : Nat := 4983230072969 + 3 ^ 40 * 4667315 * 2
def baseEnd_4667315 : Nat := 2396575960939511842297915

theorem tailTrace_4667315 : CollatzResearch.WordTrace tailWord_4667315 prefixEnd_4667315 2396575960939511842297915 := by
  unfold tailWord_4667315
  simp only [CollatzResearch.WordTrace]
  refine ⟨170230963086122343785627399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113487308724081562523751599 170230963086122343785627399)
  ·
    refine ⟨255346444629183515678441099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170230963086122343785627399 255346444629183515678441099)
    ·
      refine ⟨383019666943775273517661649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255346444629183515678441099 383019666943775273517661649)
      ·
        refine ⟨287264750207831455138246237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383019666943775273517661649 287264750207831455138246237)
        ·
          refine ⟨107724281327936795676842339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287264750207831455138246237 107724281327936795676842339)
          ·
            refine ⟨161586421991905193515263509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107724281327936795676842339 161586421991905193515263509)
            ·
              refine ⟨7574363530870555946027977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 161586421991905193515263509 7574363530870555946027977)
              ·
                refine ⟨5680772648152916959520983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7574363530870555946027977 5680772648152916959520983)
                ·
                  refine ⟨8521158972229375439281475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5680772648152916959520983 8521158972229375439281475)
                  ·
                    refine ⟨12781738458344063158922213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8521158972229375439281475 12781738458344063158922213)
                    ·
                      refine ⟨2396575960939511842297915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12781738458344063158922213 2396575960939511842297915)
                      ·
                        rfl

theorem cell23_4667315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 4].length) (baseStart_4667315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667315 prefixEnd_4667315 := by exact prefixLift 4667315
  have htrace : WordTrace (prefixWord ++ tailWord_4667315) baseStart_4667315 baseEnd_4667315 := by
    simpa [prefixWord, tailWord_4667315, baseEnd_4667315] using wordTrace_append hprefix tailTrace_4667315
  have hstable : (prefixWord ++ tailWord_4667315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667315).length < 2 ^ (prefixWord ++ tailWord_4667315).sum := by decide
  have hdescent : baseEnd_4667315 < baseStart_4667315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667325 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_4667325 : Nat := 118140960795 + 4667325 * 2 ^ 59
def prefixEnd_4667325 : Nat := 4983230072969 + 3 ^ 40 * 4667325 * 2
def baseEnd_4667325 : Nat := 798860365248685601057623

theorem tailTrace_4667325 : CollatzResearch.WordTrace tailWord_4667325 prefixEnd_4667325 798860365248685601057623 := by
  unfold tailWord_4667325
  simp only [CollatzResearch.WordTrace]
  refine ⟨170231327816086115493491429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113487551877390743662327619 170231327816086115493491429)
  ·
    refine ⟨31918373965516146655029643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170231327816086115493491429 31918373965516146655029643)
    ·
      refine ⟨47877560948274219982544465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31918373965516146655029643 47877560948274219982544465)
      ·
        refine ⟨35908170711205664986908349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47877560948274219982544465 35908170711205664986908349)
        ·
          refine ⟨13465564016702124370090631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35908170711205664986908349 13465564016702124370090631)
          ·
            refine ⟨20198346025053186555135947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13465564016702124370090631 20198346025053186555135947)
            ·
              refine ⟨30297519037579779832703921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20198346025053186555135947 30297519037579779832703921)
              ·
                refine ⟨22723139278184834874527941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30297519037579779832703921 22723139278184834874527941)
                ·
                  refine ⟨4260588614659656538973989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22723139278184834874527941 4260588614659656538973989)
                  ·
                    refine ⟨798860365248685601057623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4260588614659656538973989 798860365248685601057623)
                    ·
                      rfl

theorem cell23_4667325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_4667325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667325 prefixEnd_4667325 := by exact prefixLift 4667325
  have htrace : WordTrace (prefixWord ++ tailWord_4667325) baseStart_4667325 baseEnd_4667325 := by
    simpa [prefixWord, tailWord_4667325, baseEnd_4667325] using wordTrace_append hprefix tailTrace_4667325
  have hstable : (prefixWord ++ tailWord_4667325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667325).length < 2 ^ (prefixWord ++ tailWord_4667325).sum := by decide
  have hdescent : baseEnd_4667325 < baseStart_4667325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667326 : List Nat := [4, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_4667326 : Nat := 118140960795 + 4667326 * 2 ^ 59
def prefixEnd_4667326 : Nat := 4983230072969 + 3 ^ 40 * 4667326 * 2
def baseEnd_4667326 : Nat := 2396581609226711299260365

theorem tailTrace_4667326 : CollatzResearch.WordTrace tailWord_4667326 prefixEnd_4667326 2396581609226711299260365 := by
  unfold tailWord_4667326
  simp only [CollatzResearch.WordTrace]
  refine ⟨21278920536135311583034729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113487576192721661776185221 21278920536135311583034729)
  ·
    refine ⟨15959190402101483687276047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21278920536135311583034729 15959190402101483687276047)
    ·
      refine ⟨23938785603152225530914071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15959190402101483687276047 23938785603152225530914071)
      ·
        refine ⟨35908178404728338296371107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23938785603152225530914071 35908178404728338296371107)
        ·
          refine ⟨53862267607092507444556661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35908178404728338296371107 53862267607092507444556661)
          ·
            refine ⟨5049587588164922572927187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53862267607092507444556661 5049587588164922572927187)
            ·
              refine ⟨7574381382247383859390781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049587588164922572927187 7574381382247383859390781)
              ·
                refine ⟨2840393018342768947271543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7574381382247383859390781 2840393018342768947271543)
                ·
                  refine ⟨4260589527514153420907315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840393018342768947271543 4260589527514153420907315)
                  ·
                    refine ⟨6390884291271230131360973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4260589527514153420907315 6390884291271230131360973)
                    ·
                      refine ⟨2396581609226711299260365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6390884291271230131360973 2396581609226711299260365)
                      ·
                        rfl

theorem cell23_4667326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_4667326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667326 prefixEnd_4667326 := by exact prefixLift 4667326
  have htrace : WordTrace (prefixWord ++ tailWord_4667326) baseStart_4667326 baseEnd_4667326 := by
    simpa [prefixWord, tailWord_4667326, baseEnd_4667326] using wordTrace_append hprefix tailTrace_4667326
  have hstable : (prefixWord ++ tailWord_4667326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667326).length < 2 ^ (prefixWord ++ tailWord_4667326).sum := by decide
  have hdescent : baseEnd_4667326 < baseStart_4667326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667328 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 4]
def baseStart_4667328 : Nat := 118140960795 + 4667328 * 2 ^ 59
def prefixEnd_4667328 : Nat := 4983230072969 + 3 ^ 40 * 4667328 * 2
def baseEnd_4667328 : Nat := 2396582636188020291435355

theorem tailTrace_4667328 : CollatzResearch.WordTrace tailWord_4667328 prefixEnd_4667328 2396582636188020291435355 := by
  unfold tailWord_4667328
  simp only [CollatzResearch.WordTrace]
  refine ⟨85115718617537623502925319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113487624823383498003900425 85115718617537623502925319)
  ·
    refine ⟨127673577926306435254387979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85115718617537623502925319 127673577926306435254387979)
    ·
      refine ⟨191510366889459652881581969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127673577926306435254387979 191510366889459652881581969)
      ·
        refine ⟨143632775167094739661186477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191510366889459652881581969 143632775167094739661186477)
        ·
          refine ⟨53862290687660527372944929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143632775167094739661186477 53862290687660527372944929)
          ·
            refine ⟨40396718015745395529708697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53862290687660527372944929 40396718015745395529708697)
            ·
              refine ⟨30297538511809046647281523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40396718015745395529708697 30297538511809046647281523)
              ·
                refine ⟨45446307767713569970922285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30297538511809046647281523 45446307767713569970922285)
                ·
                  refine ⟨17042365412892588739095857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45446307767713569970922285 17042365412892588739095857)
                  ·
                    refine ⟨12781774059669441554321893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17042365412892588739095857 12781774059669441554321893)
                    ·
                      refine ⟨2396582636188020291435355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12781774059669441554321893 2396582636188020291435355)
                      ·
                        rfl

theorem cell23_4667328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_4667328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667328 prefixEnd_4667328 := by exact prefixLift 4667328
  have htrace : WordTrace (prefixWord ++ tailWord_4667328) baseStart_4667328 baseEnd_4667328 := by
    simpa [prefixWord, tailWord_4667328, baseEnd_4667328] using wordTrace_append hprefix tailTrace_4667328
  have hstable : (prefixWord ++ tailWord_4667328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667328).length < 2 ^ (prefixWord ++ tailWord_4667328).sum := by decide
  have hdescent : baseEnd_4667328 < baseStart_4667328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667349 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 3, 2, 2]
def baseStart_4667349 : Nat := 118140960795 + 4667349 * 2 ^ 59
def prefixEnd_4667349 : Nat := 4983230072969 + 3 ^ 40 * 4667349 * 2
def baseEnd_4667349 : Nat := 2396593419281764709272759

theorem tailTrace_4667349 : CollatzResearch.WordTrace tailWord_4667349 prefixEnd_4667349 2396593419281764709272759 := by
  unfold tailWord_4667349
  simp only [CollatzResearch.WordTrace]
  refine ⟨170232203167999167592365101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113488135445332778394910067 170232203167999167592365101)
  ·
    refine ⟨63837076187999687847136913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170232203167999167592365101 63837076187999687847136913)
    ·
      refine ⟨47877807140999765885352685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63837076187999687847136913 47877807140999765885352685)
      ·
        refine ⟨17954177677874912207007257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47877807140999765885352685 17954177677874912207007257)
        ·
          refine ⟨13465633258406184155255443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17954177677874912207007257 13465633258406184155255443)
          ·
            refine ⟨20198449887609276232883165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13465633258406184155255443 20198449887609276232883165)
            ·
              refine ⟨7574418707853478587331187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20198449887609276232883165 7574418707853478587331187)
              ·
                refine ⟨11361628061780217880996781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7574418707853478587331187 11361628061780217880996781)
                ·
                  refine ⟨4260610523167581705373793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11361628061780217880996781 4260610523167581705373793)
                  ·
                    refine ⟨3195457892375686279030345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4260610523167581705373793 3195457892375686279030345)
                    ·
                      refine ⟨2396593419281764709272759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3195457892375686279030345 2396593419281764709272759)
                      ·
                        rfl

theorem cell23_4667349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_4667349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667349 prefixEnd_4667349 := by exact prefixLift 4667349
  have htrace : WordTrace (prefixWord ++ tailWord_4667349) baseStart_4667349 baseEnd_4667349 := by
    simpa [prefixWord, tailWord_4667349, baseEnd_4667349] using wordTrace_append hprefix tailTrace_4667349
  have hstable : (prefixWord ++ tailWord_4667349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667349).length < 2 ^ (prefixWord ++ tailWord_4667349).sum := by decide
  have hdescent : baseEnd_4667349 < baseStart_4667349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667359 : List Nat := [1, 1, 2, 3, 4, 3, 2, 1, 2, 4]
def baseStart_4667359 : Nat := 118140960795 + 4667359 * 2 ^ 59
def prefixEnd_4667359 : Nat := 4983230072969 + 3 ^ 40 * 4667359 * 2
def baseEnd_4667359 : Nat := 798866184696103223382571

theorem tailTrace_4667359 : CollatzResearch.WordTrace tailWord_4667359 prefixEnd_4667359 798866184696103223382571 := by
  unfold tailWord_4667359
  simp only [CollatzResearch.WordTrace]
  refine ⟨170232567897962939300229131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113488378598641959533486087 170232567897962939300229131)
  ·
    refine ⟨255348851846944408950343697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170232567897962939300229131 255348851846944408950343697)
    ·
      refine ⟨191511638885208306712757773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255348851846944408950343697 191511638885208306712757773)
      ·
        refine ⟨71816864581953115017284165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191511638885208306712757773 71816864581953115017284165)
        ·
          refine ⟨13465662109116209065740781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71816864581953115017284165 13465662109116209065740781)
          ·
            refine ⟨5049623290918578399652793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13465662109116209065740781 5049623290918578399652793)
            ·
              refine ⟨3787217468188933799739595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5049623290918578399652793 3787217468188933799739595)
              ·
                refine ⟨5680826202283400699609393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3787217468188933799739595 5680826202283400699609393)
                ·
                  refine ⟨4260619651712550524707045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5680826202283400699609393 4260619651712550524707045)
                  ·
                    refine ⟨798866184696103223382571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4260619651712550524707045 798866184696103223382571)
                    ·
                      rfl

theorem cell23_4667359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 1, 2, 4].length) (baseStart_4667359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667359 prefixEnd_4667359 := by exact prefixLift 4667359
  have htrace : WordTrace (prefixWord ++ tailWord_4667359) baseStart_4667359 baseEnd_4667359 := by
    simpa [prefixWord, tailWord_4667359, baseEnd_4667359] using wordTrace_append hprefix tailTrace_4667359
  have hstable : (prefixWord ++ tailWord_4667359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667359).length < 2 ^ (prefixWord ++ tailWord_4667359).sum := by decide
  have hdescent : baseEnd_4667359 < baseStart_4667359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667399 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_4667399 : Nat := 118140960795 + 4667399 * 2 ^ 59
def prefixEnd_4667399 : Nat := 4983230072969 + 3 ^ 40 * 4667399 * 2
def baseEnd_4667399 : Nat := 2396619093314489513647529

theorem tailTrace_4667399 : CollatzResearch.WordTrace tailWord_4667399 prefixEnd_4667399 2396619093314489513647529 := by
  unfold tailWord_4667399
  simp only [CollatzResearch.WordTrace]
  refine ⟨170234026817818026131685251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113489351211878684087790167 170234026817818026131685251)
  ·
    refine ⟨255351040226727039197527877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170234026817818026131685251 255351040226727039197527877)
    ·
      refine ⟨47878320042511319849536477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255351040226727039197527877 47878320042511319849536477)
      ·
        refine ⟨17954370015941744943576179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47878320042511319849536477 17954370015941744943576179)
        ·
          refine ⟨26931555023912617415364269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17954370015941744943576179 26931555023912617415364269)
          ·
            refine ⟨10099333133967231530761601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26931555023912617415364269 10099333133967231530761601)
            ·
              refine ⟨7574499850475423648071201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10099333133967231530761601 7574499850475423648071201)
              ·
                refine ⟨5680874887856567736053401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7574499850475423648071201 5680874887856567736053401)
                ·
                  refine ⟨4260656165892425802040051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5680874887856567736053401 4260656165892425802040051)
                  ·
                    refine ⟨6390984248838638703060077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4260656165892425802040051 6390984248838638703060077)
                    ·
                      refine ⟨2396619093314489513647529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6390984248838638703060077 2396619093314489513647529)
                      ·
                        rfl

theorem cell23_4667399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_4667399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667399 prefixEnd_4667399 := by exact prefixLift 4667399
  have htrace : WordTrace (prefixWord ++ tailWord_4667399) baseStart_4667399 baseEnd_4667399 := by
    simpa [prefixWord, tailWord_4667399, baseEnd_4667399] using wordTrace_append hprefix tailTrace_4667399
  have hstable : (prefixWord ++ tailWord_4667399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667399).length < 2 ^ (prefixWord ++ tailWord_4667399).sum := by decide
  have hdescent : baseEnd_4667399 < baseStart_4667399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667455 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 3]
def baseStart_4667455 : Nat := 118140960795 + 4667455 * 2 ^ 59
def prefixEnd_4667455 : Nat := 4983230072969 + 3 ^ 40 * 4667455 * 2
def baseEnd_4667455 : Nat := 2396647848231141294547271

theorem tailTrace_4667455 : CollatzResearch.WordTrace tailWord_4667455 prefixEnd_4667455 2396647848231141294547271 := by
  unfold tailWord_4667455
  simp only [CollatzResearch.WordTrace]
  refine ⟨170236069305615147695723819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113490712870410098463815879 170236069305615147695723819)
  ·
    refine ⟨255354103958422721543585729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170236069305615147695723819 255354103958422721543585729)
    ·
      refine ⟨191515577968817041157689297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255354103958422721543585729 191515577968817041157689297)
      ·
        refine ⟨143636683476612780868266973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191515577968817041157689297 143636683476612780868266973)
        ·
          refine ⟨53863756303729792825600115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143636683476612780868266973 53863756303729792825600115)
          ·
            refine ⟨80795634455594689238400173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53863756303729792825600115 80795634455594689238400173)
            ·
              refine ⟨30298362920848008464400065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80795634455594689238400173 30298362920848008464400065)
              ·
                refine ⟨22723772190636006348300049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30298362920848008464400065 22723772190636006348300049)
                ·
                  refine ⟨17042829142977004761225037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22723772190636006348300049 17042829142977004761225037)
                  ·
                    refine ⟨6391060928616376785459389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17042829142977004761225037 6391060928616376785459389)
                    ·
                      refine ⟨2396647848231141294547271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6391060928616376785459389 2396647848231141294547271)
                      ·
                        rfl

theorem cell23_4667455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_4667455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667455 prefixEnd_4667455 := by exact prefixLift 4667455
  have htrace : WordTrace (prefixWord ++ tailWord_4667455) baseStart_4667455 baseEnd_4667455 := by
    simpa [prefixWord, tailWord_4667455, baseEnd_4667455] using wordTrace_append hprefix tailTrace_4667455
  have hstable : (prefixWord ++ tailWord_4667455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667455).length < 2 ^ (prefixWord ++ tailWord_4667455).sum := by decide
  have hdescent : baseEnd_4667455 < baseStart_4667455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667456 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 2, 2, 2]
def baseStart_4667456 : Nat := 118140960795 + 4667456 * 2 ^ 59
def prefixEnd_4667456 : Nat := 4983230072969 + 3 ^ 40 * 4667456 * 2
def baseEnd_4667456 : Nat := 2396648361711795790634767

theorem tailTrace_4667456 : CollatzResearch.WordTrace tailWord_4667456 prefixEnd_4667456 2396648361711795790634767 := by
  unfold tailWord_4667456
  simp only [CollatzResearch.WordTrace]
  refine ⟨85118052889305762433255111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113490737185741016577673481 85118052889305762433255111)
  ·
    refine ⟨127677079333958643649882667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85118052889305762433255111 127677079333958643649882667)
    ·
      refine ⟨191515619000937965474824001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127677079333958643649882667 191515619000937965474824001)
      ·
        refine ⟨143636714250703474106118001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191515619000937965474824001 143636714250703474106118001)
        ·
          refine ⟨107727535688027605579588501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143636714250703474106118001 107727535688027605579588501)
          ·
            refine ⟨5049728235376294011543211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107727535688027605579588501 5049728235376294011543211)
            ·
              refine ⟨7574592353064441017314817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049728235376294011543211 7574592353064441017314817)
              ·
                refine ⟨5680944264798330762986113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7574592353064441017314817 5680944264798330762986113)
                ·
                  refine ⟨4260708198598748072239585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5680944264798330762986113 4260708198598748072239585)
                  ·
                    refine ⟨3195531148949061054179689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4260708198598748072239585 3195531148949061054179689)
                    ·
                      refine ⟨2396648361711795790634767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3195531148949061054179689 2396648361711795790634767)
                      ·
                        rfl

theorem cell23_4667456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2, 2, 2].length) (baseStart_4667456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667456 prefixEnd_4667456 := by exact prefixLift 4667456
  have htrace : WordTrace (prefixWord ++ tailWord_4667456) baseStart_4667456 baseEnd_4667456 := by
    simpa [prefixWord, tailWord_4667456, baseEnd_4667456] using wordTrace_append hprefix tailTrace_4667456
  have hstable : (prefixWord ++ tailWord_4667456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667456).length < 2 ^ (prefixWord ++ tailWord_4667456).sum := by decide
  have hdescent : baseEnd_4667456 < baseStart_4667456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667495 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_4667495 : Nat := 118140960795 + 4667495 * 2 ^ 59
def prefixEnd_4667495 : Nat := 4983230072969 + 3 ^ 40 * 4667495 * 2
def baseEnd_4667495 : Nat := 2396668387457321138047087

theorem tailTrace_4667495 : CollatzResearch.WordTrace tailWord_4667495 prefixEnd_4667495 2396668387457321138047087 := by
  unfold tailWord_4667495
  simp only [CollatzResearch.WordTrace]
  refine ⟨170237528225470234527179939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113491685483646823018119959 170237528225470234527179939)
  ·
    refine ⟨255356292338205351790769909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170237528225470234527179939 255356292338205351790769909)
    ·
      refine ⟨23939652406706751730384679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 255356292338205351790769909 23939652406706751730384679)
      ·
        refine ⟨35909478610060127595577019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23939652406706751730384679 35909478610060127595577019)
        ·
          refine ⟨53864217915090191393365529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35909478610060127595577019 53864217915090191393365529)
          ·
            refine ⟨40398163436317643545024147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53864217915090191393365529 40398163436317643545024147)
            ·
              refine ⟨60597245154476465317536221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40398163436317643545024147 60597245154476465317536221)
              ·
                refine ⟨22723966932928674494076083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60597245154476465317536221 22723966932928674494076083)
                ·
                  refine ⟨34085950399393011741114125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22723966932928674494076083 34085950399393011741114125)
                  ·
                    refine ⟨12782231399772379402917797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34085950399393011741114125 12782231399772379402917797)
                    ·
                      refine ⟨2396668387457321138047087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12782231399772379402917797 2396668387457321138047087)
                      ·
                        rfl

theorem cell23_4667495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_4667495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667495 prefixEnd_4667495 := by exact prefixLift 4667495
  have htrace : WordTrace (prefixWord ++ tailWord_4667495) baseStart_4667495 baseEnd_4667495 := by
    simpa [prefixWord, tailWord_4667495, baseEnd_4667495] using wordTrace_append hprefix tailTrace_4667495
  have hstable : (prefixWord ++ tailWord_4667495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667495).length < 2 ^ (prefixWord ++ tailWord_4667495).sum := by decide
  have hdescent : baseEnd_4667495 < baseStart_4667495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667545 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 2, 5, 3]
def baseStart_4667545 : Nat := 118140960795 + 4667545 * 2 ^ 59
def prefixEnd_4667545 : Nat := 4983230072969 + 3 ^ 40 * 4667545 * 2
def baseEnd_4667545 : Nat := 2396694061490045942421857

theorem tailTrace_4667545 : CollatzResearch.WordTrace tailWord_4667545 prefixEnd_4667545 2396694061490045942421857 := by
  unfold tailWord_4667545
  simp only [CollatzResearch.WordTrace]
  refine ⟨170239351875289093066500089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113492901250192728711000059 170239351875289093066500089)
  ·
    refine ⟨127679513906466819799875067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170239351875289093066500089 127679513906466819799875067)
    ·
      refine ⟨191519270859700229699812601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127679513906466819799875067 191519270859700229699812601)
      ·
        refine ⟨143639453144775172274859451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191519270859700229699812601 143639453144775172274859451)
        ·
          refine ⟨215459179717162758412289177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143639453144775172274859451 215459179717162758412289177)
          ·
            refine ⟨161594384787872068809216883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215459179717162758412289177 161594384787872068809216883)
            ·
              refine ⟨242391577181808103213825325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161594384787872068809216883 242391577181808103213825325)
              ·
                refine ⟨90896841443178038705184497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242391577181808103213825325 90896841443178038705184497)
                ·
                  refine ⟨68172631082383529028888373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90896841443178038705184497 68172631082383529028888373)
                  ·
                    refine ⟨6391184163973455846458285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68172631082383529028888373 6391184163973455846458285)
                    ·
                      refine ⟨2396694061490045942421857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6391184163973455846458285 2396694061490045942421857)
                      ·
                        rfl

theorem cell23_4667545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_4667545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667545 prefixEnd_4667545 := by exact prefixLift 4667545
  have htrace : WordTrace (prefixWord ++ tailWord_4667545) baseStart_4667545 baseEnd_4667545 := by
    simpa [prefixWord, tailWord_4667545, baseEnd_4667545] using wordTrace_append hprefix tailTrace_4667545
  have hstable : (prefixWord ++ tailWord_4667545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667545).length < 2 ^ (prefixWord ++ tailWord_4667545).sum := by decide
  have hdescent : baseEnd_4667545 < baseStart_4667545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667549 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_4667549 : Nat := 118140960795 + 4667549 * 2 ^ 59
def prefixEnd_4667549 : Nat := 4983230072969 + 3 ^ 40 * 4667549 * 2
def baseEnd_4667549 : Nat := 2396696115412663926771839

theorem tailTrace_4667549 : CollatzResearch.WordTrace tailWord_4667549 prefixEnd_4667549 2396696115412663926771839 := by
  unfold tailWord_4667549
  simp only [CollatzResearch.WordTrace]
  refine ⟨170239497767274601749645701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113492998511516401166430467 170239497767274601749645701)
  ·
    refine ⟨31919905831363987828058569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170239497767274601749645701 31919905831363987828058569)
    ·
      refine ⟨23939929373522990871043927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31919905831363987828058569 23939929373522990871043927)
      ·
        refine ⟨35909894060284486306565891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23939929373522990871043927 35909894060284486306565891)
        ·
          refine ⟨53864841090426729459848837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35909894060284486306565891 53864841090426729459848837)
          ·
            refine ⟨10099657704455011773721657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53864841090426729459848837 10099657704455011773721657)
            ·
              refine ⟨7574743278341258830291243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10099657704455011773721657 7574743278341258830291243)
              ·
                refine ⟨11362114917511888245436865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7574743278341258830291243 11362114917511888245436865)
                ·
                  refine ⟨8521586188133916184077649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11362114917511888245436865 8521586188133916184077649)
                  ·
                    refine ⟨6391189641100437138058237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8521586188133916184077649 6391189641100437138058237)
                    ·
                      refine ⟨2396696115412663926771839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6391189641100437138058237 2396696115412663926771839)
                      ·
                        rfl

theorem cell23_4667549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_4667549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667549 prefixEnd_4667549 := by exact prefixLift 4667549
  have htrace : WordTrace (prefixWord ++ tailWord_4667549) baseStart_4667549 baseEnd_4667549 := by
    simpa [prefixWord, tailWord_4667549, baseEnd_4667549] using wordTrace_append hprefix tailTrace_4667549
  have hstable : (prefixWord ++ tailWord_4667549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667549).length < 2 ^ (prefixWord ++ tailWord_4667549).sum := by decide
  have hdescent : baseEnd_4667549 < baseStart_4667549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667569 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 6]
def baseStart_4667569 : Nat := 118140960795 + 4667569 * 2 ^ 59
def prefixEnd_4667569 : Nat := 4983230072969 + 3 ^ 40 * 4667569 * 2
def baseEnd_4667569 : Nat := 266300709447305983169083

theorem tailTrace_4667569 : CollatzResearch.WordTrace tailWord_4667569 prefixEnd_4667569 266300709447305983169083 := by
  unfold tailWord_4667569
  simp only [CollatzResearch.WordTrace]
  refine ⟨170240227227202145165373761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113493484818134763443582507 170240227227202145165373761)
  ·
    refine ⟨127680170420401608874030321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170240227227202145165373761 127680170420401608874030321)
    ·
      refine ⟨95760127815301206655522741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127680170420401608874030321 95760127815301206655522741)
      ·
        refine ⟨8977511982684488123955257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95760127815301206655522741 8977511982684488123955257)
        ·
          refine ⟨6733133987013366092966443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8977511982684488123955257 6733133987013366092966443)
          ·
            refine ⟨10099700980520049139449665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6733133987013366092966443 10099700980520049139449665)
            ·
              refine ⟨7574775735390036854587249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10099700980520049139449665 7574775735390036854587249)
              ·
                refine ⟨5681081801542527640940437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7574775735390036854587249 5681081801542527640940437)
                ·
                  refine ⟨266300709447305983169083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5681081801542527640940437 266300709447305983169083)
                  ·
                    rfl

theorem cell23_4667569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 6].length) (baseStart_4667569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667569 prefixEnd_4667569 := by exact prefixLift 4667569
  have htrace : WordTrace (prefixWord ++ tailWord_4667569) baseStart_4667569 baseEnd_4667569 := by
    simpa [prefixWord, tailWord_4667569, baseEnd_4667569] using wordTrace_append hprefix tailTrace_4667569
  have hstable : (prefixWord ++ tailWord_4667569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667569).length < 2 ^ (prefixWord ++ tailWord_4667569).sum := by decide
  have hdescent : baseEnd_4667569 < baseStart_4667569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667573 : List Nat := [1, 3, 3, 4, 1, 1, 1, 4, 1, 4]
def baseStart_4667573 : Nat := 118140960795 + 4667573 * 2 ^ 59
def prefixEnd_4667573 : Nat := 4983230072969 + 3 ^ 40 * 4667573 * 2
def baseEnd_4667573 : Nat := 798902812982790610957243

theorem tailTrace_4667573 : CollatzResearch.WordTrace tailWord_4667573 prefixEnd_4667573 798902812982790610957243 := by
  unfold tailWord_4667573
  simp only [CollatzResearch.WordTrace]
  refine ⟨170240373119187653848519373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113493582079458435899012915 170240373119187653848519373)
  ·
    refine ⟨63840139919695370193194765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170240373119187653848519373 63840139919695370193194765)
    ·
      refine ⟨23940052469885763822448037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63840139919695370193194765 23940052469885763822448037)
      ·
        refine ⟨4488759838103580716709007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23940052469885763822448037 4488759838103580716709007)
        ·
          refine ⟨6733139757155371075063511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4488759838103580716709007 6733139757155371075063511)
          ·
            refine ⟨10099709635733056612595267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6733139757155371075063511 10099709635733056612595267)
            ·
              refine ⟨15149564453599584918892901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10099709635733056612595267 15149564453599584918892901)
              ·
                refine ⟨2840543335049922172292419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15149564453599584918892901 2840543335049922172292419)
                ·
                  refine ⟨4260815002574883258438629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840543335049922172292419 4260815002574883258438629)
                  ·
                    refine ⟨798902812982790610957243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4260815002574883258438629 798902812982790610957243)
                    ·
                      rfl

theorem cell23_4667573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_4667573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667573 prefixEnd_4667573 := by exact prefixLift 4667573
  have htrace : WordTrace (prefixWord ++ tailWord_4667573) baseStart_4667573 baseEnd_4667573 := by
    simpa [prefixWord, tailWord_4667573, baseEnd_4667573] using wordTrace_append hprefix tailTrace_4667573
  have hstable : (prefixWord ++ tailWord_4667573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667573).length < 2 ^ (prefixWord ++ tailWord_4667573).sum := by decide
  have hdescent : baseEnd_4667573 < baseStart_4667573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667586 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 6]
def baseStart_4667586 : Nat := 118140960795 + 4667586 * 2 ^ 59
def prefixEnd_4667586 : Nat := 4983230072969 + 3 ^ 40 * 4667586 * 2
def baseEnd_4667586 : Nat := 266301679355208920223241

theorem tailTrace_4667586 : CollatzResearch.WordTrace tailWord_4667586 prefixEnd_4667586 266301679355208920223241 := by
  unfold tailWord_4667586
  simp only [CollatzResearch.WordTrace]
  refine ⟨42560211817035139267185653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113493898178760371379161741 42560211817035139267185653)
  ·
    refine ⟨3990019857847044306298655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42560211817035139267185653 3990019857847044306298655)
    ·
      refine ⟨5985029786770566459447983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3990019857847044306298655 5985029786770566459447983)
      ·
        refine ⟨8977544680155849689171975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5985029786770566459447983 8977544680155849689171975)
        ·
          refine ⟨13466317020233774533757963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8977544680155849689171975 13466317020233774533757963)
          ·
            refine ⟨20199475530350661800636945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13466317020233774533757963 20199475530350661800636945)
            ·
              refine ⟨15149606647762996350477709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20199475530350661800636945 15149606647762996350477709)
              ·
                refine ⟨5681102492911123631429141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15149606647762996350477709 5681102492911123631429141)
                ·
                  refine ⟨266301679355208920223241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5681102492911123631429141 266301679355208920223241)
                  ·
                    rfl

theorem cell23_4667586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_4667586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667586 prefixEnd_4667586 := by exact prefixLift 4667586
  have htrace : WordTrace (prefixWord ++ tailWord_4667586) baseStart_4667586 baseEnd_4667586 := by
    simpa [prefixWord, tailWord_4667586, baseEnd_4667586] using wordTrace_append hprefix tailTrace_4667586
  have hstable : (prefixWord ++ tailWord_4667586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667586).length < 2 ^ (prefixWord ++ tailWord_4667586).sum := by decide
  have hdescent : baseEnd_4667586 < baseStart_4667586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667613 : List Nat := [1, 4, 3, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_4667613 : Nat := 118140960795 + 4667613 * 2 ^ 59
def prefixEnd_4667613 : Nat := 4983230072969 + 3 ^ 40 * 4667613 * 2
def baseEnd_4667613 : Nat := 2396728978174551676371545

theorem tailTrace_4667613 : CollatzResearch.WordTrace tailWord_4667613 prefixEnd_4667613 2396728978174551676371545 := by
  unfold tailWord_4667613
  simp only [CollatzResearch.WordTrace]
  refine ⟨170241832039042740679975493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113494554692695160453316995 170241832039042740679975493)
  ·
    refine ⟨31920343507320513877495405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170241832039042740679975493 31920343507320513877495405)
    ·
      refine ⟨11970128815245192704060777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31920343507320513877495405 11970128815245192704060777)
      ·
        refine ⟨8977596611433894528045583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11970128815245192704060777 8977596611433894528045583)
        ·
          refine ⟨13466394917150841792068375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8977596611433894528045583 13466394917150841792068375)
          ·
            refine ⟨20199592375726262688102563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13466394917150841792068375 20199592375726262688102563)
            ·
              refine ⟨30299388563589394032153845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20199592375726262688102563 30299388563589394032153845)
              ·
                refine ⟨2840567677836505690514423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30299388563589394032153845 2840567677836505690514423)
                ·
                  refine ⟨4260851516754758535771635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840567677836505690514423 4260851516754758535771635)
                  ·
                    refine ⟨6391277275132137803657453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4260851516754758535771635 6391277275132137803657453)
                    ·
                      refine ⟨2396728978174551676371545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6391277275132137803657453 2396728978174551676371545)
                      ·
                        rfl

theorem cell23_4667613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_4667613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667613 prefixEnd_4667613 := by exact prefixLift 4667613
  have htrace : WordTrace (prefixWord ++ tailWord_4667613) baseStart_4667613 baseEnd_4667613 := by
    simpa [prefixWord, tailWord_4667613, baseEnd_4667613] using wordTrace_append hprefix tailTrace_4667613
  have hstable : (prefixWord ++ tailWord_4667613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667613).length < 2 ^ (prefixWord ++ tailWord_4667613).sum := by decide
  have hdescent : baseEnd_4667613 < baseStart_4667613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667615 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_4667615 : Nat := 118140960795 + 4667615 * 2 ^ 59
def prefixEnd_4667615 : Nat := 4983230072969 + 3 ^ 40 * 4667615 * 2
def baseEnd_4667615 : Nat := 2396730005135860668546535

theorem tailTrace_4667615 : CollatzResearch.WordTrace tailWord_4667615 prefixEnd_4667615 2396730005135860668546535 := by
  unfold tailWord_4667615
  simp only [CollatzResearch.WordTrace]
  refine ⟨170241904985035495021548299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113494603323356996681032199 170241904985035495021548299)
  ·
    refine ⟨255362857477553242532322449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170241904985035495021548299 255362857477553242532322449)
    ·
      refine ⟨191522143108164931899241837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255362857477553242532322449 191522143108164931899241837)
      ·
        refine ⟨71820803665561849462215689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191522143108164931899241837 71820803665561849462215689)
        ·
          refine ⟨53865602749171387096661767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71820803665561849462215689 53865602749171387096661767)
          ·
            refine ⟨80798404123757080644992651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53865602749171387096661767 80798404123757080644992651)
            ·
              refine ⟨121197606185635620967488977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80798404123757080644992651 121197606185635620967488977)
              ·
                refine ⟨90898204639226715725616733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121197606185635620967488977 90898204639226715725616733)
                ·
                  refine ⟨34086826739710018397106275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90898204639226715725616733 34086826739710018397106275)
                  ·
                    refine ⟨51130240109565027595659413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34086826739710018397106275 51130240109565027595659413)
                    ·
                      refine ⟨2396730005135860668546535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51130240109565027595659413 2396730005135860668546535)
                      ·
                        rfl

theorem cell23_4667615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_4667615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667615 prefixEnd_4667615 := by exact prefixLift 4667615
  have htrace : WordTrace (prefixWord ++ tailWord_4667615) baseStart_4667615 baseEnd_4667615 := by
    simpa [prefixWord, tailWord_4667615, baseEnd_4667615] using wordTrace_append hprefix tailTrace_4667615
  have hstable : (prefixWord ++ tailWord_4667615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667615).length < 2 ^ (prefixWord ++ tailWord_4667615).sum := by decide
  have hdescent : baseEnd_4667615 < baseStart_4667615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667656 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_4667656 : Nat := 118140960795 + 4667656 * 2 ^ 59
def prefixEnd_4667656 : Nat := 4983230072969 + 3 ^ 40 * 4667656 * 2
def baseEnd_4667656 : Nat := 2396751057842695008133847

theorem tailTrace_4667656 : CollatzResearch.WordTrace tailWord_4667656 prefixEnd_4667656 2396751057842695008133847 := by
  unfold tailWord_4667656
  simp only [CollatzResearch.WordTrace]
  refine ⟨85121700188943479511895411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113495600251924639349193881 85121700188943479511895411)
  ·
    refine ⟨127682550283415219267843117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85121700188943479511895411 127682550283415219267843117)
    ·
      refine ⟨47880956356280707225441169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127682550283415219267843117 47880956356280707225441169)
      ·
        refine ⟨35910717267210530419080877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47880956356280707225441169 35910717267210530419080877)
        ·
          refine ⟨13466518975203948907155329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35910717267210530419080877 13466518975203948907155329)
          ·
            refine ⟨10099889231402961680366497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13466518975203948907155329 10099889231402961680366497)
            ·
              refine ⟨7574916923552221260274873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10099889231402961680366497 7574916923552221260274873)
              ·
                refine ⟨5681187692664165945206155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7574916923552221260274873 5681187692664165945206155)
                ·
                  refine ⟨8521781538996248917809233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5681187692664165945206155 8521781538996248917809233)
                  ·
                    refine ⟨6391336154247186688356925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8521781538996248917809233 6391336154247186688356925)
                    ·
                      refine ⟨2396751057842695008133847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6391336154247186688356925 2396751057842695008133847)
                      ·
                        rfl

theorem cell23_4667656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_4667656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667656 prefixEnd_4667656 := by exact prefixLift 4667656
  have htrace : WordTrace (prefixWord ++ tailWord_4667656) baseStart_4667656 baseEnd_4667656 := by
    simpa [prefixWord, tailWord_4667656, baseEnd_4667656] using wordTrace_append hprefix tailTrace_4667656
  have hstable : (prefixWord ++ tailWord_4667656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667656).length < 2 ^ (prefixWord ++ tailWord_4667656).sum := by decide
  have hdescent : baseEnd_4667656 < baseStart_4667656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667669 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_4667669 : Nat := 118140960795 + 4667669 * 2 ^ 59
def prefixEnd_4667669 : Nat := 4983230072969 + 3 ^ 40 * 4667669 * 2
def baseEnd_4667669 : Nat := 2396757733091203457271287

theorem tailTrace_4667669 : CollatzResearch.WordTrace tailWord_4667669 prefixEnd_4667669 2396757733091203457271287 := by
  unfold tailWord_4667669
  simp only [CollatzResearch.WordTrace]
  refine ⟨170243874526839862244014061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113495916351226574829342707 170243874526839862244014061)
  ·
    refine ⟨63841452947564948341505273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170243874526839862244014061 63841452947564948341505273)
    ·
      refine ⟨47881089710673711256128955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63841452947564948341505273 47881089710673711256128955)
      ·
        refine ⟨71821634566010566884193433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47881089710673711256128955 71821634566010566884193433)
        ·
          refine ⟨53866225924507925163145075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71821634566010566884193433 53866225924507925163145075)
          ·
            refine ⟨80799338886761887744717613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53866225924507925163145075 80799338886761887744717613)
            ·
              refine ⟨30299752082535707904269105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80799338886761887744717613 30299752082535707904269105)
              ·
                refine ⟨22724814061901780928201829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30299752082535707904269105 22724814061901780928201829)
                ·
                  refine ⟨4260902636606583924037843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22724814061901780928201829 4260902636606583924037843)
                  ·
                    refine ⟨6391353954909875886056765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4260902636606583924037843 6391353954909875886056765)
                    ·
                      refine ⟨2396757733091203457271287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6391353954909875886056765 2396757733091203457271287)
                      ·
                        rfl

theorem cell23_4667669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_4667669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667669 prefixEnd_4667669 := by exact prefixLift 4667669
  have htrace : WordTrace (prefixWord ++ tailWord_4667669) baseStart_4667669 baseEnd_4667669 := by
    simpa [prefixWord, tailWord_4667669, baseEnd_4667669] using wordTrace_append hprefix tailTrace_4667669
  have hstable : (prefixWord ++ tailWord_4667669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667669).length < 2 ^ (prefixWord ++ tailWord_4667669).sum := by decide
  have hdescent : baseEnd_4667669 < baseStart_4667669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667712 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 3]
def baseStart_4667712 : Nat := 118140960795 + 4667712 * 2 ^ 59
def prefixEnd_4667712 : Nat := 4983230072969 + 3 ^ 40 * 4667712 * 2
def baseEnd_4667712 : Nat := 2396779812759346789033589

theorem tailTrace_4667712 : CollatzResearch.WordTrace tailWord_4667712 prefixEnd_4667712 2396779812759346789033589 := by
  unfold tailWord_4667712
  simp only [CollatzResearch.WordTrace]
  refine ⟨85122721432842040293914695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113496961910456053725219593 85122721432842040293914695)
  ·
    refine ⟨127684082149263060440872043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85122721432842040293914695 127684082149263060440872043)
    ·
      refine ⟨191526123223894590661308065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127684082149263060440872043 191526123223894590661308065)
      ·
        refine ⟨143644592417920942995981049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191526123223894590661308065 143644592417920942995981049)
        ·
          refine ⟨107733444313440707246985787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143644592417920942995981049 107733444313440707246985787)
          ·
            refine ⟨161600166470161060870478681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107733444313440707246985787 161600166470161060870478681)
            ·
              refine ⟨121200124852620795652859011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161600166470161060870478681 121200124852620795652859011)
              ·
                refine ⟨181800187278931193479288517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121200124852620795652859011 181800187278931193479288517)
                ·
                  refine ⟨34087535114799598777366597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181800187278931193479288517 34087535114799598777366597)
                  ·
                    refine ⟨6391412834024924770756237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34087535114799598777366597 6391412834024924770756237)
                    ·
                      refine ⟨2396779812759346789033589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6391412834024924770756237 2396779812759346789033589)
                      ·
                        rfl

theorem cell23_4667712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_4667712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667712 prefixEnd_4667712 := by exact prefixLift 4667712
  have htrace : WordTrace (prefixWord ++ tailWord_4667712) baseStart_4667712 baseEnd_4667712 := by
    simpa [prefixWord, tailWord_4667712, baseEnd_4667712] using wordTrace_append hprefix tailTrace_4667712
  have hstable : (prefixWord ++ tailWord_4667712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667712).length < 2 ^ (prefixWord ++ tailWord_4667712).sum := by decide
  have hdescent : baseEnd_4667712 < baseStart_4667712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667713 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4667713 : Nat := 118140960795 + 4667713 * 2 ^ 59
def prefixEnd_4667713 : Nat := 4983230072969 + 3 ^ 40 * 4667713 * 2
def baseEnd_4667713 : Nat := 2396780326240001285121085

theorem tailTrace_4667713 : CollatzResearch.WordTrace tailWord_4667713 prefixEnd_4667713 2396780326240001285121085 := by
  unfold tailWord_4667713
  simp only [CollatzResearch.WordTrace]
  refine ⟨170245479338680457758615793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113496986225786971839077195 170245479338680457758615793)
  ·
    refine ⟨127684109504010343318961845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170245479338680457758615793 127684109504010343318961845)
    ·
      refine ⟨11970385266000969686152673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127684109504010343318961845 11970385266000969686152673)
      ·
        refine ⟨8977788949500727264614505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11970385266000969686152673 8977788949500727264614505)
        ·
          refine ⟨6733341712125545448460879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8977788949500727264614505 6733341712125545448460879)
          ·
            refine ⟨10100012568188318172691319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6733341712125545448460879 10100012568188318172691319)
            ·
              refine ⟨15150018852282477259036979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10100012568188318172691319 15150018852282477259036979)
              ·
                refine ⟨22725028278423715888555469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15150018852282477259036979 22725028278423715888555469)
                ·
                  refine ⟨8521885604408893458208301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22725028278423715888555469 8521885604408893458208301)
                  ·
                    refine ⟨3195707101653335046828113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8521885604408893458208301 3195707101653335046828113)
                    ·
                      refine ⟨2396780326240001285121085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3195707101653335046828113 2396780326240001285121085)
                      ·
                        rfl

theorem cell23_4667713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4667713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667713 prefixEnd_4667713 := by exact prefixLift 4667713
  have htrace : WordTrace (prefixWord ++ tailWord_4667713) baseStart_4667713 baseEnd_4667713 := by
    simpa [prefixWord, tailWord_4667713, baseEnd_4667713] using wordTrace_append hprefix tailTrace_4667713
  have hstable : (prefixWord ++ tailWord_4667713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667713).length < 2 ^ (prefixWord ++ tailWord_4667713).sum := by decide
  have hdescent : baseEnd_4667713 < baseStart_4667713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667722 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_4667722 : Nat := 118140960795 + 4667722 * 2 ^ 59
def prefixEnd_4667722 : Nat := 4983230072969 + 3 ^ 40 * 4667722 * 2
def baseEnd_4667722 : Nat := 2396784947565891749908543

theorem tailTrace_4667722 : CollatzResearch.WordTrace tailWord_4667722 prefixEnd_4667722 2396784947565891749908543 := by
  unfold tailWord_4667722
  simp only [CollatzResearch.WordTrace]
  refine ⟨42561451898911963073923355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113497205063765234863795613 42561451898911963073923355)
  ·
    refine ⟨63842177848367944610885033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42561451898911963073923355 63842177848367944610885033)
    ·
      refine ⟨47881633386275958458163775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63842177848367944610885033 47881633386275958458163775)
      ·
        refine ⟨71822450079413937687245663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47881633386275958458163775 71822450079413937687245663)
        ·
          refine ⟨107733675119120906530868495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71822450079413937687245663 107733675119120906530868495)
          ·
            refine ⟨161600512678681359796302743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107733675119120906530868495 161600512678681359796302743)
            ·
              refine ⟨242400769018022039694454115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161600512678681359796302743 242400769018022039694454115)
              ·
                refine ⟨363601153527033059541681173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242400769018022039694454115 363601153527033059541681173)
                ·
                  refine ⟨17043804071579674666016305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 363601153527033059541681173 17043804071579674666016305)
                  ·
                    refine ⟨12782853053684755999512229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17043804071579674666016305 12782853053684755999512229)
                    ·
                      refine ⟨2396784947565891749908543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12782853053684755999512229 2396784947565891749908543)
                      ·
                        rfl

theorem cell23_4667722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_4667722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667722 prefixEnd_4667722 := by exact prefixLift 4667722
  have htrace : WordTrace (prefixWord ++ tailWord_4667722) baseStart_4667722 baseEnd_4667722 := by
    simpa [prefixWord, tailWord_4667722, baseEnd_4667722] using wordTrace_append hprefix tailTrace_4667722
  have hstable : (prefixWord ++ tailWord_4667722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667722).length < 2 ^ (prefixWord ++ tailWord_4667722).sum := by decide
  have hdescent : baseEnd_4667722 < baseStart_4667722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667726 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2]
def baseStart_4667726 : Nat := 118140960795 + 4667726 * 2 ^ 59
def prefixEnd_4667726 : Nat := 4983230072969 + 3 ^ 40 * 4667726 * 2
def baseEnd_4667726 : Nat := 2396787001488509734258525

theorem tailTrace_4667726 : CollatzResearch.WordTrace tailWord_4667726 prefixEnd_4667726 2396787001488509734258525 := by
  unfold tailWord_4667726
  simp only [CollatzResearch.WordTrace]
  refine ⟨21280744185954170122354879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113497302325088907319226021 21280744185954170122354879)
  ·
    refine ⟨31921116278931255183532319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21280744185954170122354879 31921116278931255183532319)
    ·
      refine ⟨47881674418396882775298479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31921116278931255183532319 47881674418396882775298479)
      ·
        refine ⟨71822511627595324162947719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47881674418396882775298479 71822511627595324162947719)
        ·
          refine ⟨107733767441392986244421579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71822511627595324162947719 107733767441392986244421579)
          ·
            refine ⟨161600651162089479366632369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107733767441392986244421579 161600651162089479366632369)
            ·
              refine ⟨121200488371567109524974277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161600651162089479366632369 121200488371567109524974277)
              ·
                refine ⟨22725091569668833035932677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121200488371567109524974277 22725091569668833035932677)
                ·
                  refine ⟨4260954669312906194237377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22725091569668833035932677 4260954669312906194237377)
                  ·
                    refine ⟨3195716001984679645678033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4260954669312906194237377 3195716001984679645678033)
                    ·
                      refine ⟨2396787001488509734258525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3195716001984679645678033 2396787001488509734258525)
                      ·
                        rfl

theorem cell23_4667726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_4667726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667726 prefixEnd_4667726 := by exact prefixLift 4667726
  have htrace : WordTrace (prefixWord ++ tailWord_4667726) baseStart_4667726 baseEnd_4667726 := by
    simpa [prefixWord, tailWord_4667726, baseEnd_4667726] using wordTrace_append hprefix tailTrace_4667726
  have hstable : (prefixWord ++ tailWord_4667726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667726).length < 2 ^ (prefixWord ++ tailWord_4667726).sum := by decide
  have hdescent : baseEnd_4667726 < baseStart_4667726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667769 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 4, 5, 2]
def baseStart_4667769 : Nat := 118140960795 + 4667769 * 2 ^ 59
def prefixEnd_4667769 : Nat := 4983230072969 + 3 ^ 40 * 4667769 * 2
def baseEnd_4667769 : Nat := 2396809081156653066020827

theorem tailTrace_4667769 : CollatzResearch.WordTrace tailWord_4667769 prefixEnd_4667769 2396809081156653066020827 := by
  unfold tailWord_4667769
  simp only [CollatzResearch.WordTrace]
  refine ⟨170247521826477579322654361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113498347884318386215102907 170247521826477579322654361)
  ·
    refine ⟨127685641369858184491990771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170247521826477579322654361 127685641369858184491990771)
    ·
      refine ⟨191528462054787276737986157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127685641369858184491990771 191528462054787276737986157)
      ·
        refine ⟨71823173270545228776744809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191528462054787276737986157 71823173270545228776744809)
        ·
          refine ⟨53867379952908921582558607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71823173270545228776744809 53867379952908921582558607)
          ·
            refine ⟨80801069929363382373837911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53867379952908921582558607 80801069929363382373837911)
            ·
              refine ⟨121201604894045073560756867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80801069929363382373837911 121201604894045073560756867)
              ·
                refine ⟨181802407341067610341135301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121201604894045073560756867 181802407341067610341135301)
                ·
                  refine ⟨34087951376450176938962869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181802407341067610341135301 34087951376450176938962869)
                  ·
                    refine ⟨3195745441542204088027769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34087951376450176938962869 3195745441542204088027769)
                    ·
                      refine ⟨2396809081156653066020827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3195745441542204088027769 2396809081156653066020827)
                      ·
                        rfl

theorem cell23_4667769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_4667769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667769 prefixEnd_4667769 := by exact prefixLift 4667769
  have htrace : WordTrace (prefixWord ++ tailWord_4667769) baseStart_4667769 baseEnd_4667769 := by
    simpa [prefixWord, tailWord_4667769, baseEnd_4667769] using wordTrace_append hprefix tailTrace_4667769
  have hstable : (prefixWord ++ tailWord_4667769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667769).length < 2 ^ (prefixWord ++ tailWord_4667769).sum := by decide
  have hdescent : baseEnd_4667769 < baseStart_4667769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667772 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_4667772 : Nat := 118140960795 + 4667772 * 2 ^ 59
def prefixEnd_4667772 : Nat := 4983230072969 + 3 ^ 40 * 4667772 * 2
def baseEnd_4667772 : Nat := 2396810621598616554283313

theorem tailTrace_4667772 : CollatzResearch.WordTrace tailWord_4667772 prefixEnd_4667772 2396810621598616554283313 := by
  unfold tailWord_4667772
  simp only [CollatzResearch.WordTrace]
  refine ⟨85123815622733355417506785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113498420830311140556675713 85123815622733355417506785)
  ·
    refine ⟨63842861717050016563130089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85123815622733355417506785 63842861717050016563130089)
    ·
      refine ⟨47882146287787512422347567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63842861717050016563130089 47882146287787512422347567)
      ·
        refine ⟨71823219431681268633521351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47882146287787512422347567 71823219431681268633521351)
        ·
          refine ⟨107734829147521902950282027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71823219431681268633521351 107734829147521902950282027)
          ·
            refine ⟨161602243721282854425423041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107734829147521902950282027 161602243721282854425423041)
            ·
              refine ⟨121201682790962140819067281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161602243721282854425423041 121201682790962140819067281)
              ·
                refine ⟨90901262093221605614300461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121201682790962140819067281 90901262093221605614300461)
                ·
                  refine ⟨34087973284958102105362673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90901262093221605614300461 34087973284958102105362673)
                  ·
                    refine ⟨25565979963718576579022005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34087973284958102105362673 25565979963718576579022005)
                    ·
                      refine ⟨2396810621598616554283313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25565979963718576579022005 2396810621598616554283313)
                      ·
                        rfl

theorem cell23_4667772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_4667772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667772 prefixEnd_4667772 := by exact prefixLift 4667772
  have htrace : WordTrace (prefixWord ++ tailWord_4667772) baseStart_4667772 baseEnd_4667772 := by
    simpa [prefixWord, tailWord_4667772, baseEnd_4667772] using wordTrace_append hprefix tailTrace_4667772
  have hstable : (prefixWord ++ tailWord_4667772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667772).length < 2 ^ (prefixWord ++ tailWord_4667772).sum := by decide
  have hdescent : baseEnd_4667772 < baseStart_4667772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667779 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 1, 7]
def baseStart_4667779 : Nat := 118140960795 + 4667779 * 2 ^ 59
def prefixEnd_4667779 : Nat := 4983230072969 + 3 ^ 40 * 4667779 * 2
def baseEnd_4667779 : Nat := 798938071987732675631927

theorem tailTrace_4667779 : CollatzResearch.WordTrace tailWord_4667779 prefixEnd_4667779 798938071987732675631927 := by
  unfold tailWord_4667779
  simp only [CollatzResearch.WordTrace]
  refine ⟨170247886556441351030518391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113498591037627567353678927 170247886556441351030518391)
  ·
    refine ⟨255371829834662026545777587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170247886556441351030518391 255371829834662026545777587)
    ·
      refine ⟨383057744751993039818666381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255371829834662026545777587 383057744751993039818666381)
      ·
        refine ⟨143646654281997389931999893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383057744751993039818666381 143646654281997389931999893)
        ·
          refine ⟨6733436919468627653062495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143646654281997389931999893 6733436919468627653062495)
          ·
            refine ⟨10100155379202941479593743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6733436919468627653062495 10100155379202941479593743)
            ·
              refine ⟨15150233068804412219390615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10100155379202941479593743 15150233068804412219390615)
              ·
                refine ⟨22725349603206618329085923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15150233068804412219390615 22725349603206618329085923)
                ·
                  refine ⟨34088024404809927493628885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22725349603206618329085923 34088024404809927493628885)
                  ·
                    refine ⟨798938071987732675631927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34088024404809927493628885 798938071987732675631927)
                    ·
                      rfl

theorem cell23_4667779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 7].length) (baseStart_4667779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667779 prefixEnd_4667779 := by exact prefixLift 4667779
  have htrace : WordTrace (prefixWord ++ tailWord_4667779) baseStart_4667779 baseEnd_4667779 := by
    simpa [prefixWord, tailWord_4667779, baseEnd_4667779] using wordTrace_append hprefix tailTrace_4667779
  have hstable : (prefixWord ++ tailWord_4667779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667779).length < 2 ^ (prefixWord ++ tailWord_4667779).sum := by decide
  have hdescent : baseEnd_4667779 < baseStart_4667779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667799 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_4667799 : Nat := 118140960795 + 4667799 * 2 ^ 59
def prefixEnd_4667799 : Nat := 4983230072969 + 3 ^ 40 * 4667799 * 2
def baseEnd_4667799 : Nat := 2396824485576287948645689

theorem tailTrace_4667799 : CollatzResearch.WordTrace tailWord_4667799 prefixEnd_4667799 2396824485576287948645689 := by
  unfold tailWord_4667799
  simp only [CollatzResearch.WordTrace]
  refine ⟨170248616016368894446246451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113499077344245929630830967 170248616016368894446246451)
  ·
    refine ⟨255372924024553341669369677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170248616016368894446246451 255372924024553341669369677)
    ·
      refine ⟨95764846509207503126013629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255372924024553341669369677 95764846509207503126013629)
      ·
        refine ⟨35911817440952813672255111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95764846509207503126013629 35911817440952813672255111)
        ·
          refine ⟨53867726161429220508382667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35911817440952813672255111 53867726161429220508382667)
          ·
            refine ⟨80801589242143830762574001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53867726161429220508382667 80801589242143830762574001)
            ·
              refine ⟨60601191931607873071930501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80801589242143830762574001 60601191931607873071930501)
              ·
                refine ⟨11362723487176476200986969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60601191931607873071930501 11362723487176476200986969)
                ·
                  refine ⟨8522042615382357150740227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11362723487176476200986969 8522042615382357150740227)
                  ·
                    refine ⟨12783063923073535726110341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8522042615382357150740227 12783063923073535726110341)
                    ·
                      refine ⟨2396824485576287948645689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12783063923073535726110341 2396824485576287948645689)
                      ·
                        rfl

theorem cell23_4667799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_4667799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667799 prefixEnd_4667799 := by exact prefixLift 4667799
  have htrace : WordTrace (prefixWord ++ tailWord_4667799) baseStart_4667799 baseEnd_4667799 := by
    simpa [prefixWord, tailWord_4667799, baseEnd_4667799] using wordTrace_append hprefix tailTrace_4667799
  have hstable : (prefixWord ++ tailWord_4667799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667799).length < 2 ^ (prefixWord ++ tailWord_4667799).sum := by decide
  have hdescent : baseEnd_4667799 < baseStart_4667799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667816 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4667816 : Nat := 118140960795 + 4667816 * 2 ^ 59
def prefixEnd_4667816 : Nat := 4983230072969 + 3 ^ 40 * 4667816 * 2
def baseEnd_4667816 : Nat := 2396833214747414382133111

theorem tailTrace_4667816 : CollatzResearch.WordTrace tailWord_4667816 prefixEnd_4667816 2396833214747414382133111 := by
  unfold tailWord_4667816
  simp only [CollatzResearch.WordTrace]
  refine ⟨85124618028653653174807651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113499490704871537566410201 85124618028653653174807651)
  ·
    refine ⟨127686927042980479762211477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85124618028653653174807651 127686927042980479762211477)
    ·
      refine ⟨5985324705139709988853663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127686927042980479762211477 5985324705139709988853663)
      ·
        refine ⟨8977987057709564983280495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5985324705139709988853663 8977987057709564983280495)
        ·
          refine ⟨13466980586564347474920743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8977987057709564983280495 13466980586564347474920743)
          ·
            refine ⟨20200470879846521212381115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13466980586564347474920743 20200470879846521212381115)
            ·
              refine ⟨30300706319769781818571673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20200470879846521212381115 30300706319769781818571673)
              ·
                refine ⟨22725529739827336363928755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30300706319769781818571673 22725529739827336363928755)
                ·
                  refine ⟨34088294609741004545893133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22725529739827336363928755 34088294609741004545893133)
                  ·
                    refine ⟨12783110478652876704709925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34088294609741004545893133 12783110478652876704709925)
                    ·
                      refine ⟨2396833214747414382133111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12783110478652876704709925 2396833214747414382133111)
                      ·
                        rfl

theorem cell23_4667816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4667816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667816 prefixEnd_4667816 := by exact prefixLift 4667816
  have htrace : WordTrace (prefixWord ++ tailWord_4667816) baseStart_4667816 baseEnd_4667816 := by
    simpa [prefixWord, tailWord_4667816, baseEnd_4667816] using wordTrace_append hprefix tailTrace_4667816
  have hstable : (prefixWord ++ tailWord_4667816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667816).length < 2 ^ (prefixWord ++ tailWord_4667816).sum := by decide
  have hdescent : baseEnd_4667816 < baseStart_4667816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667836 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_4667836 : Nat := 118140960795 + 4667836 * 2 ^ 59
def prefixEnd_4667836 : Nat := 4983230072969 + 3 ^ 40 * 4667836 * 2
def baseEnd_4667836 : Nat := 2396843484360504303883019

theorem tailTrace_4667836 : CollatzResearch.WordTrace tailWord_4667836 prefixEnd_4667836 2396843484360504303883019 := by
  unfold tailWord_4667836
  simp only [CollatzResearch.WordTrace]
  refine ⟨85124982758617424882671681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113499977011489899843562241 85124982758617424882671681)
  ·
    refine ⟨63843737068963068662003761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85124982758617424882671681 63843737068963068662003761)
    ·
      refine ⟨47882802801722301496502821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63843737068963068662003761 47882802801722301496502821)
      ·
        refine ⟨8978025525322931530594279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47882802801722301496502821 8978025525322931530594279)
        ·
          refine ⟨13467038287984397295891419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8978025525322931530594279 13467038287984397295891419)
          ·
            refine ⟨20200557431976595943837129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13467038287984397295891419 20200557431976595943837129)
            ·
              refine ⟨15150418073982446957877847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20200557431976595943837129 15150418073982446957877847)
              ·
                refine ⟨22725627110973670436816771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15150418073982446957877847 22725627110973670436816771)
                ·
                  refine ⟨34088440666460505655225157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22725627110973670436816771 34088440666460505655225157)
                  ·
                    refine ⟨6391582624961344810354717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34088440666460505655225157 6391582624961344810354717)
                    ·
                      refine ⟨2396843484360504303883019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6391582624961344810354717 2396843484360504303883019)
                      ·
                        rfl

theorem cell23_4667836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_4667836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667836 prefixEnd_4667836 := by exact prefixLift 4667836
  have htrace : WordTrace (prefixWord ++ tailWord_4667836) baseStart_4667836 baseEnd_4667836 := by
    simpa [prefixWord, tailWord_4667836, baseEnd_4667836] using wordTrace_append hprefix tailTrace_4667836
  have hstable : (prefixWord ++ tailWord_4667836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667836).length < 2 ^ (prefixWord ++ tailWord_4667836).sum := by decide
  have hdescent : baseEnd_4667836 < baseStart_4667836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667886 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_4667886 : Nat := 118140960795 + 4667886 * 2 ^ 59
def prefixEnd_4667886 : Nat := 4983230072969 + 3 ^ 40 * 4667886 * 2
def baseEnd_4667886 : Nat := 798956386131076369419263

theorem tailTrace_4667886 : CollatzResearch.WordTrace tailWord_4667886 prefixEnd_4667886 798956386131076369419263 := by
  unfold tailWord_4667886
  simp only [CollatzResearch.WordTrace]
  refine ⟨21281473645881713538082939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113501192778035805536442341 21281473645881713538082939)
  ·
    refine ⟨31922210468822570307124409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21281473645881713538082939 31922210468822570307124409)
    ·
      refine ⟨23941657851616927730343307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31922210468822570307124409 23941657851616927730343307)
      ·
        refine ⟨35912486777425391595514961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23941657851616927730343307 35912486777425391595514961)
        ·
          refine ⟨26934365083069043696636221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35912486777425391595514961 26934365083069043696636221)
          ·
            refine ⟨10100386906150891386238583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26934365083069043696636221 10100386906150891386238583)
            ·
              refine ⟨15150580359226337079357875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10100386906150891386238583 15150580359226337079357875)
              ·
                refine ⟨22725870538839505619036813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15150580359226337079357875 22725870538839505619036813)
                ·
                  refine ⟨8522201452064814607138805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22725870538839505619036813 8522201452064814607138805)
                  ·
                    refine ⟨798956386131076369419263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8522201452064814607138805 798956386131076369419263)
                    ·
                      rfl

theorem cell23_4667886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_4667886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667886 prefixEnd_4667886 := by exact prefixLift 4667886
  have htrace : WordTrace (prefixWord ++ tailWord_4667886) baseStart_4667886 baseEnd_4667886 := by
    simpa [prefixWord, tailWord_4667886, baseEnd_4667886] using wordTrace_append hprefix tailTrace_4667886
  have hstable : (prefixWord ++ tailWord_4667886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667886).length < 2 ^ (prefixWord ++ tailWord_4667886).sum := by decide
  have hdescent : baseEnd_4667886 < baseStart_4667886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667923 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 3, 2, 2]
def baseStart_4667923 : Nat := 118140960795 + 4667923 * 2 ^ 59
def prefixEnd_4667923 : Nat := 4983230072969 + 3 ^ 40 * 4667923 * 2
def baseEnd_4667923 : Nat := 2396888157177445463495119

theorem tailTrace_4667923 : CollatzResearch.WordTrace tailWord_4667923 prefixEnd_4667923 2396888157177445463495119 := by
  unfold tailWord_4667923
  simp only [CollatzResearch.WordTrace]
  refine ⟨170253138667919663623760423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113502092445279775749173615 170253138667919663623760423)
  ·
    refine ⟨255379708001879495435640635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170253138667919663623760423 255379708001879495435640635)
    ·
      refine ⟨383069562002819243153460953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255379708001879495435640635 383069562002819243153460953)
      ·
        refine ⟨287302171502114432365095715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383069562002819243153460953 287302171502114432365095715)
        ·
          refine ⟨430953257253171648547643573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287302171502114432365095715 430953257253171648547643573)
          ·
            refine ⟨40401867867484842051341585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 430953257253171648547643573 40401867867484842051341585)
            ·
              refine ⟨30301400900613631538506189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40401867867484842051341585 30301400900613631538506189)
              ·
                refine ⟨11363025337730111826939821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30301400900613631538506189 11363025337730111826939821)
                ·
                  refine ⟨4261134501648791935102433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11363025337730111826939821 4261134501648791935102433)
                  ·
                    refine ⟨3195850876236593951326825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4261134501648791935102433 3195850876236593951326825)
                    ·
                      refine ⟨2396888157177445463495119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3195850876236593951326825 2396888157177445463495119)
                      ·
                        rfl

theorem cell23_4667923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 2, 2].length) (baseStart_4667923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667923 prefixEnd_4667923 := by exact prefixLift 4667923
  have htrace : WordTrace (prefixWord ++ tailWord_4667923) baseStart_4667923 baseEnd_4667923 := by
    simpa [prefixWord, tailWord_4667923, baseEnd_4667923] using wordTrace_append hprefix tailTrace_4667923
  have hstable : (prefixWord ++ tailWord_4667923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667923).length < 2 ^ (prefixWord ++ tailWord_4667923).sum := by decide
  have hdescent : baseEnd_4667923 < baseStart_4667923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667933 : List Nat := [1, 4, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_4667933 : Nat := 118140960795 + 4667933 * 2 ^ 59
def prefixEnd_4667933 : Nat := 4983230072969 + 3 ^ 40 * 4667933 * 2
def baseEnd_4667933 : Nat := 798964430661330141456691

theorem tailTrace_4667933 : CollatzResearch.WordTrace tailWord_4667933 prefixEnd_4667933 798964430661330141456691 := by
  unfold tailWord_4667933
  simp only [CollatzResearch.WordTrace]
  refine ⟨170253503397883435331624453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113502335598588956887749635 170253503397883435331624453)
  ·
    refine ⟨31922531887103144124679585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170253503397883435331624453 31922531887103144124679585)
    ·
      refine ⟨23941898915327358093509689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31922531887103144124679585 23941898915327358093509689)
      ·
        refine ⟨17956424186495518570132267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23941898915327358093509689 17956424186495518570132267)
        ·
          refine ⟨26934636279743277855198401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17956424186495518570132267 26934636279743277855198401)
          ·
            refine ⟨20200977209807458391398801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26934636279743277855198401 20200977209807458391398801)
            ·
              refine ⟨15150732907355593793549101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20200977209807458391398801 15150732907355593793549101)
              ·
                refine ⟨5681524840258347672580913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15150732907355593793549101 5681524840258347672580913)
                ·
                  refine ⟨4261143630193760754435685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5681524840258347672580913 4261143630193760754435685)
                  ·
                    refine ⟨798964430661330141456691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4261143630193760754435685 798964430661330141456691)
                    ·
                      rfl

theorem cell23_4667933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_4667933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667933 prefixEnd_4667933 := by exact prefixLift 4667933
  have htrace : WordTrace (prefixWord ++ tailWord_4667933) baseStart_4667933 baseEnd_4667933 := by
    simpa [prefixWord, tailWord_4667933, baseEnd_4667933] using wordTrace_append hprefix tailTrace_4667933
  have hstable : (prefixWord ++ tailWord_4667933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667933).length < 2 ^ (prefixWord ++ tailWord_4667933).sum := by decide
  have hdescent : baseEnd_4667933 < baseStart_4667933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667957 : List Nat := [1, 3, 3, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_4667957 : Nat := 118140960795 + 4667957 * 2 ^ 59
def prefixEnd_4667957 : Nat := 4983230072969 + 3 ^ 40 * 4667957 * 2
def baseEnd_4667957 : Nat := 2396905615519698330469963

theorem tailTrace_4667957 : CollatzResearch.WordTrace tailWord_4667957 prefixEnd_4667957 2396905615519698330469963 := by
  unfold tailWord_4667957
  simp only [CollatzResearch.WordTrace]
  refine ⟨170254378749796487430498125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113502919166530991620332083 170254378749796487430498125)
  ·
    refine ⟨63845392031173682786436797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170254378749796487430498125 63845392031173682786436797)
    ·
      refine ⟨23942022011690131044913799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63845392031173682786436797 23942022011690131044913799)
      ·
        refine ⟨35913033017535196567370699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23942022011690131044913799 35913033017535196567370699)
        ·
          refine ⟨53869549526302794851056049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35913033017535196567370699 53869549526302794851056049)
          ·
            refine ⟨40402162144727096138292037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53869549526302794851056049 40402162144727096138292037)
            ·
              refine ⟨7575405402136330525929757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40402162144727096138292037 7575405402136330525929757)
              ·
                refine ⟨2840777025801123947223659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7575405402136330525929757 2840777025801123947223659)
                ·
                  refine ⟨4261165538701685920835489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840777025801123947223659 4261165538701685920835489)
                  ·
                    refine ⟨3195874154026264440626617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4261165538701685920835489 3195874154026264440626617)
                    ·
                      refine ⟨2396905615519698330469963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3195874154026264440626617 2396905615519698330469963)
                      ·
                        rfl

theorem cell23_4667957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_4667957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667957 prefixEnd_4667957 := by exact prefixLift 4667957
  have htrace : WordTrace (prefixWord ++ tailWord_4667957) baseStart_4667957 baseEnd_4667957 := by
    simpa [prefixWord, tailWord_4667957, baseEnd_4667957] using wordTrace_append hprefix tailTrace_4667957
  have hstable : (prefixWord ++ tailWord_4667957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667957).length < 2 ^ (prefixWord ++ tailWord_4667957).sum := by decide
  have hdescent : baseEnd_4667957 < baseStart_4667957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667973 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 4, 1, 3]
def baseStart_4667973 : Nat := 118140960795 + 4667973 * 2 ^ 59
def prefixEnd_4667973 : Nat := 4983230072969 + 3 ^ 40 * 4667973 * 2
def baseEnd_4667973 : Nat := 2396913831210170267869889

theorem tailTrace_4667973 : CollatzResearch.WordTrace tailWord_4667973 prefixEnd_4667973 2396913831210170267869889 := by
  unfold tailWord_4667973
  simp only [CollatzResearch.WordTrace]
  refine ⟨170254962317738522163080573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113503308211825681442053715 170254962317738522163080573)
  ·
    refine ⟨63845610869151945811155215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170254962317738522163080573 63845610869151945811155215)
    ·
      refine ⟨95768416303727918716732823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63845610869151945811155215 95768416303727918716732823)
      ·
        refine ⟨143652624455591878075099235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95768416303727918716732823 143652624455591878075099235)
        ·
          refine ⟨215478936683387817112648853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143652624455591878075099235 215478936683387817112648853)
          ·
            refine ⟨10100575157033803927155415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 215478936683387817112648853 10100575157033803927155415)
            ·
              refine ⟨15150862735550705890733123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10100575157033803927155415 15150862735550705890733123)
              ·
                refine ⟨22726294103326058836099685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15150862735550705890733123 22726294103326058836099685)
                ·
                  refine ⟨4261180144373636031768691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22726294103326058836099685 4261180144373636031768691)
                  ·
                    refine ⟨6391770216560454047653037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4261180144373636031768691 6391770216560454047653037)
                    ·
                      refine ⟨2396913831210170267869889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6391770216560454047653037 2396913831210170267869889)
                      ·
                        rfl

theorem cell23_4667973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_4667973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667973 prefixEnd_4667973 := by exact prefixLift 4667973
  have htrace : WordTrace (prefixWord ++ tailWord_4667973) baseStart_4667973 baseEnd_4667973 := by
    simpa [prefixWord, tailWord_4667973, baseEnd_4667973] using wordTrace_append hprefix tailTrace_4667973
  have hstable : (prefixWord ++ tailWord_4667973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667973).length < 2 ^ (prefixWord ++ tailWord_4667973).sum := by decide
  have hdescent : baseEnd_4667973 < baseStart_4667973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667974 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_4667974 : Nat := 118140960795 + 4667974 * 2 ^ 59
def prefixEnd_4667974 : Nat := 4983230072969 + 3 ^ 40 * 4667974 * 2
def baseEnd_4667974 : Nat := 2396914344690824763957385

theorem tailTrace_4667974 : CollatzResearch.WordTrace tailWord_4667974 prefixEnd_4667974 2396914344690824763957385 := by
  unfold tailWord_4667974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5320468712210465604183343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113503332527156599555911317 5320468712210465604183343)
  ·
    refine ⟨7980703068315698406275015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5320468712210465604183343 7980703068315698406275015)
    ·
      refine ⟨11971054602473547609412523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7980703068315698406275015 11971054602473547609412523)
      ·
        refine ⟨17956581903710321414118785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11971054602473547609412523 17956581903710321414118785)
        ·
          refine ⟨13467436427782741060589089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17956581903710321414118785 13467436427782741060589089)
          ·
            refine ⟨10100577320837055795441817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13467436427782741060589089 10100577320837055795441817)
            ·
              refine ⟨7575432990627791846581363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10100577320837055795441817 7575432990627791846581363)
              ·
                refine ⟨11363149485941687769872045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7575432990627791846581363 11363149485941687769872045)
                ·
                  refine ⟨4261181057228132913702017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11363149485941687769872045 4261181057228132913702017)
                  ·
                    refine ⟨3195885792921099685276513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4261181057228132913702017 3195885792921099685276513)
                    ·
                      refine ⟨2396914344690824763957385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3195885792921099685276513 2396914344690824763957385)
                      ·
                        rfl

theorem cell23_4667974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_4667974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667974 prefixEnd_4667974 := by exact prefixLift 4667974
  have htrace : WordTrace (prefixWord ++ tailWord_4667974) baseStart_4667974 baseEnd_4667974 := by
    simpa [prefixWord, tailWord_4667974, baseEnd_4667974] using wordTrace_append hprefix tailTrace_4667974
  have hstable : (prefixWord ++ tailWord_4667974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667974).length < 2 ^ (prefixWord ++ tailWord_4667974).sum := by decide
  have hdescent : baseEnd_4667974 < baseStart_4667974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667979 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 4]
def baseStart_4667979 : Nat := 118140960795 + 4667979 * 2 ^ 59
def prefixEnd_4667979 : Nat := 4983230072969 + 3 ^ 40 * 4667979 * 2
def baseEnd_4667979 : Nat := 2396916912094097244394861

theorem tailTrace_4667979 : CollatzResearch.WordTrace tailWord_4667979 prefixEnd_4667979 2396916912094097244394861 := by
  unfold tailWord_4667979
  simp only [CollatzResearch.WordTrace]
  refine ⟨170255181155716785187798991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113503454103811190125199327 170255181155716785187798991)
  ·
    refine ⟨255382771733575177781698487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170255181155716785187798991 255382771733575177781698487)
    ·
      refine ⟨383074157600362766672547731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255382771733575177781698487 383074157600362766672547731)
      ·
        refine ⟨574611236400544150008821597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383074157600362766672547731 574611236400544150008821597)
        ·
          refine ⟨215479213650204056253308099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 574611236400544150008821597 215479213650204056253308099)
          ·
            refine ⟨323218820475306084379962149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215479213650204056253308099 323218820475306084379962149)
            ·
              refine ⟨60603528839119890821242903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 323218820475306084379962149 60603528839119890821242903)
              ·
                refine ⟨90905293258679836231864355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60603528839119890821242903 90905293258679836231864355)
                ·
                  refine ⟨136357939888019754347796533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90905293258679836231864355 136357939888019754347796533)
                  ·
                    refine ⟨12783556864501851970105925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 136357939888019754347796533 12783556864501851970105925)
                    ·
                      refine ⟨2396916912094097244394861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12783556864501851970105925 2396916912094097244394861)
                      ·
                        rfl

theorem cell23_4667979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 4].length) (baseStart_4667979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667979 prefixEnd_4667979 := by exact prefixLift 4667979
  have htrace : WordTrace (prefixWord ++ tailWord_4667979) baseStart_4667979 baseEnd_4667979 := by
    simpa [prefixWord, tailWord_4667979, baseEnd_4667979] using wordTrace_append hprefix tailTrace_4667979
  have hstable : (prefixWord ++ tailWord_4667979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667979).length < 2 ^ (prefixWord ++ tailWord_4667979).sum := by decide
  have hdescent : baseEnd_4667979 < baseStart_4667979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4667999 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_4667999 : Nat := 118140960795 + 4667999 * 2 ^ 59
def prefixEnd_4667999 : Nat := 4983230072969 + 3 ^ 40 * 4667999 * 2
def baseEnd_4667999 : Nat := 2396927181707187166144769

theorem tailTrace_4667999 : CollatzResearch.WordTrace tailWord_4667999 prefixEnd_4667999 2396927181707187166144769 := by
  unfold tailWord_4667999
  simp only [CollatzResearch.WordTrace]
  refine ⟨170255910615644328603527051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113503940410429552402351367 170255910615644328603527051)
  ·
    refine ⟨255383865923466492905290577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170255910615644328603527051 255383865923466492905290577)
    ·
      refine ⟨191537899442599869678967933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255383865923466492905290577 191537899442599869678967933)
      ·
        refine ⟨71826712290974951129612975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191537899442599869678967933 71826712290974951129612975)
        ·
          refine ⟨107740068436462426694419463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71826712290974951129612975 107740068436462426694419463)
          ·
            refine ⟨161610102654693640041629195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107740068436462426694419463 161610102654693640041629195)
            ·
              refine ⟨242415153982040460062443793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161610102654693640041629195 242415153982040460062443793)
              ·
                refine ⟨181811365486530345046832845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242415153982040460062443793 181811365486530345046832845)
                ·
                  refine ⟨68179262057448879392562317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181811365486530345046832845 68179262057448879392562317)
                  ·
                    refine ⟨25567223271543329772210869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68179262057448879392562317 25567223271543329772210869)
                    ·
                      refine ⟨2396927181707187166144769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25567223271543329772210869 2396927181707187166144769)
                      ·
                        rfl

theorem cell23_4667999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_4667999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4667999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4667999 prefixEnd_4667999 := by exact prefixLift 4667999
  have htrace : WordTrace (prefixWord ++ tailWord_4667999) baseStart_4667999 baseEnd_4667999 := by
    simpa [prefixWord, tailWord_4667999, baseEnd_4667999] using wordTrace_append hprefix tailTrace_4667999
  have hstable : (prefixWord ++ tailWord_4667999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4667999).length < 2 ^ (prefixWord ++ tailWord_4667999).sum := by decide
  have hdescent : baseEnd_4667999 < baseStart_4667999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4667999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668087 : List Nat := [1, 1, 3, 1, 6, 2, 2, 2, 5]
def baseStart_4668087 : Nat := 118140960795 + 4668087 * 2 ^ 59
def prefixEnd_4668087 : Nat := 4983230072969 + 3 ^ 40 * 4668087 * 2
def baseEnd_4668087 : Nat := 266330263111642535760485

theorem tailTrace_4668087 : CollatzResearch.WordTrace tailWord_4668087 prefixEnd_4668087 266330263111642535760485 := by
  unfold tailWord_4668087
  simp only [CollatzResearch.WordTrace]
  refine ⟨170259120239325519632730515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113506080159550346421820343 170259120239325519632730515)
  ·
    refine ⟨255388680358988279449095773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170259120239325519632730515 255388680358988279449095773)
    ·
      refine ⟨95770755134620604793410915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255388680358988279449095773 95770755134620604793410915)
      ·
        refine ⟨143656132701930907190116373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95770755134620604793410915 143656132701930907190116373)
        ·
          refine ⟨6733881220403011274536705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143656132701930907190116373 6733881220403011274536705)
          ·
            refine ⟨5050410915302258455902529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6733881220403011274536705 5050410915302258455902529)
            ·
              refine ⟨3787808186476693841926897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5050410915302258455902529 3787808186476693841926897)
              ·
                refine ⟨2840856139857520381445173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3787808186476693841926897 2840856139857520381445173)
                ·
                  refine ⟨266330263111642535760485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2840856139857520381445173 266330263111642535760485)
                  ·
                    rfl

theorem cell23_4668087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 5].length) (baseStart_4668087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668087 prefixEnd_4668087 := by exact prefixLift 4668087
  have htrace : WordTrace (prefixWord ++ tailWord_4668087) baseStart_4668087 baseEnd_4668087 := by
    simpa [prefixWord, tailWord_4668087, baseEnd_4668087] using wordTrace_append hprefix tailTrace_4668087
  have hstable : (prefixWord ++ tailWord_4668087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668087).length < 2 ^ (prefixWord ++ tailWord_4668087).sum := by decide
  have hdescent : baseEnd_4668087 < baseStart_4668087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668097 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4668097 : Nat := 118140960795 + 4668097 * 2 ^ 59
def prefixEnd_4668097 : Nat := 4983230072969 + 3 ^ 40 * 4668097 * 2
def baseEnd_4668097 : Nat := 2396977502811327782719319

theorem tailTrace_4668097 : CollatzResearch.WordTrace tailWord_4668097 prefixEnd_4668097 2396977502811327782719319 := by
  unfold tailWord_4668097
  simp only [CollatzResearch.WordTrace]
  refine ⟨170259484969289291340594545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113506323312859527560396363 170259484969289291340594545)
  ·
    refine ⟨127694613726966968505445909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170259484969289291340594545 127694613726966968505445909)
    ·
      refine ⟨5985685018451576648692777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127694613726966968505445909 5985685018451576648692777)
      ·
        refine ⟨4489263763838682486519583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5985685018451576648692777 4489263763838682486519583)
        ·
          refine ⟨6733895645758023729779375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4489263763838682486519583 6733895645758023729779375)
          ·
            refine ⟨10100843468637035594669063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6733895645758023729779375 10100843468637035594669063)
            ·
              refine ⟨15151265202955553392003595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10100843468637035594669063 15151265202955553392003595)
              ·
                refine ⟨22726897804433330088005393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15151265202955553392003595 22726897804433330088005393)
                ·
                  refine ⟨17045173353324997566004045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22726897804433330088005393 17045173353324997566004045)
                  ·
                    refine ⟨6391940007496874087251517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17045173353324997566004045 6391940007496874087251517)
                    ·
                      refine ⟨2396977502811327782719319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6391940007496874087251517 2396977502811327782719319)
                      ·
                        rfl

theorem cell23_4668097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4668097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668097 prefixEnd_4668097 := by exact prefixLift 4668097
  have htrace : WordTrace (prefixWord ++ tailWord_4668097) baseStart_4668097 baseEnd_4668097 := by
    simpa [prefixWord, tailWord_4668097, baseEnd_4668097] using wordTrace_append hprefix tailTrace_4668097
  have hstable : (prefixWord ++ tailWord_4668097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668097).length < 2 ^ (prefixWord ++ tailWord_4668097).sum := by decide
  have hdescent : baseEnd_4668097 < baseStart_4668097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668113 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 3, 4]
def baseStart_4668113 : Nat := 118140960795 + 4668113 * 2 ^ 59
def prefixEnd_4668113 : Nat := 4983230072969 + 3 ^ 40 * 4668113 * 2
def baseEnd_4668113 : Nat := 798995239500599906706415

theorem tailTrace_4668113 : CollatzResearch.WordTrace tailWord_4668113 prefixEnd_4668113 798995239500599906706415 := by
  unfold tailWord_4668113
  simp only [CollatzResearch.WordTrace]
  refine ⟨170260068537231326073176993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113506712358154217382117995 170260068537231326073176993)
  ·
    refine ⟨127695051402923494554882745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170260068537231326073176993 127695051402923494554882745)
    ·
      refine ⟨95771288552192620916162059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127695051402923494554882745 95771288552192620916162059)
      ·
        refine ⟨143656932828288931374243089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95771288552192620916162059 143656932828288931374243089)
        ·
          refine ⟨107742699621216698530682317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143656932828288931374243089 107742699621216698530682317)
          ·
            refine ⟨40403512357956261949005869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107742699621216698530682317 40403512357956261949005869)
            ·
              refine ⟨15151317134233598230877201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40403512357956261949005869 15151317134233598230877201)
              ·
                refine ⟨11363487850675198673157901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15151317134233598230877201 11363487850675198673157901)
                ·
                  refine ⟨4261307944003199502434213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11363487850675198673157901 4261307944003199502434213)
                  ·
                    refine ⟨798995239500599906706415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4261307944003199502434213 798995239500599906706415)
                    ·
                      rfl

theorem cell23_4668113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_4668113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668113 prefixEnd_4668113 := by exact prefixLift 4668113
  have htrace : WordTrace (prefixWord ++ tailWord_4668113) baseStart_4668113 baseEnd_4668113 := by
    simpa [prefixWord, tailWord_4668113, baseEnd_4668113] using wordTrace_append hprefix tailTrace_4668113
  have hstable : (prefixWord ++ tailWord_4668113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668113).length < 2 ^ (prefixWord ++ tailWord_4668113).sum := by decide
  have hdescent : baseEnd_4668113 < baseStart_4668113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668117 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 2, 5]
def baseStart_4668117 : Nat := 118140960795 + 4668117 * 2 ^ 59
def prefixEnd_4668117 : Nat := 4983230072969 + 3 ^ 40 * 4668117 * 2
def baseEnd_4668117 : Nat := 798995924141472568156409

theorem tailTrace_4668117 : CollatzResearch.WordTrace tailWord_4668117 prefixEnd_4668117 798995924141472568156409 := by
  unfold tailWord_4668117
  simp only [CollatzResearch.WordTrace]
  refine ⟨170260214429216834756322605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113506809619477889837548403 170260214429216834756322605)
  ·
    refine ⟨63847580410956313033620977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170260214429216834756322605 63847580410956313033620977)
    ·
      refine ⟨47885685308217234775215733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63847580410956313033620977 47885685308217234775215733)
      ·
        refine ⟨4489282997645365760176475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47885685308217234775215733 4489282997645365760176475)
        ·
          refine ⟨6733924496468048640264713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4489282997645365760176475 6733924496468048640264713)
          ·
            refine ⟨5050443372351036480198535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6733924496468048640264713 5050443372351036480198535)
            ·
              refine ⟨7575665058526554720297803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5050443372351036480198535 7575665058526554720297803)
              ·
                refine ⟨11363497587789832080446705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7575665058526554720297803 11363497587789832080446705)
                ·
                  refine ⟨8522623190842374060335029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11363497587789832080446705 8522623190842374060335029)
                  ·
                    refine ⟨798995924141472568156409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8522623190842374060335029 798995924141472568156409)
                    ·
                      rfl

theorem cell23_4668117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_4668117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668117 prefixEnd_4668117 := by exact prefixLift 4668117
  have htrace : WordTrace (prefixWord ++ tailWord_4668117) baseStart_4668117 baseEnd_4668117 := by
    simpa [prefixWord, tailWord_4668117, baseEnd_4668117] using wordTrace_append hprefix tailTrace_4668117
  have hstable : (prefixWord ++ tailWord_4668117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668117).length < 2 ^ (prefixWord ++ tailWord_4668117).sum := by decide
  have hdescent : baseEnd_4668117 < baseStart_4668117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668120 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 2, 1, 4]
def baseStart_4668120 : Nat := 118140960795 + 4668120 * 2 ^ 59
def prefixEnd_4668120 : Nat := 4983230072969 + 3 ^ 40 * 4668120 * 2
def baseEnd_4668120 : Nat := 2396989312866381192731713

theorem tailTrace_4668120 : CollatzResearch.WordTrace tailWord_4668120 prefixEnd_4668120 2396989312866381192731713 := by
  unfold tailWord_4668120
  simp only [CollatzResearch.WordTrace]
  refine ⟨85130161924102983134340907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113506882565470644179121209 85130161924102983134340907)
  ·
    refine ⟨127695242886154474701511361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85130161924102983134340907 127695242886154474701511361)
    ·
      refine ⟨95771432164615856026133521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127695242886154474701511361 95771432164615856026133521)
      ·
        refine ⟨71828574123461892019600141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95771432164615856026133521 71828574123461892019600141)
        ·
          refine ⟨26935715296298209507350053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71828574123461892019600141 26935715296298209507350053)
          ·
            refine ⟨5050446618055914282628135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26935715296298209507350053 5050446618055914282628135)
            ·
              refine ⟨7575669927083871423942203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5050446618055914282628135 7575669927083871423942203)
              ·
                refine ⟨11363504890625807135913305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7575669927083871423942203 11363504890625807135913305)
                ·
                  refine ⟨8522628667969355351934979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11363504890625807135913305 8522628667969355351934979)
                  ·
                    refine ⟨12783943001954033027902469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8522628667969355351934979 12783943001954033027902469)
                    ·
                      refine ⟨2396989312866381192731713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12783943001954033027902469 2396989312866381192731713)
                      ·
                        rfl

theorem cell23_4668120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_4668120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668120 prefixEnd_4668120 := by exact prefixLift 4668120
  have htrace : WordTrace (prefixWord ++ tailWord_4668120) baseStart_4668120 baseEnd_4668120 := by
    simpa [prefixWord, tailWord_4668120, baseEnd_4668120] using wordTrace_append hprefix tailTrace_4668120
  have hstable : (prefixWord ++ tailWord_4668120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668120).length < 2 ^ (prefixWord ++ tailWord_4668120).sum := by decide
  have hdescent : baseEnd_4668120 < baseStart_4668120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668143 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 6]
def baseStart_4668143 : Nat := 118140960795 + 4668143 * 2 ^ 59
def prefixEnd_4668143 : Nat := 4983230072969 + 3 ^ 40 * 4668143 * 2
def baseEnd_4668143 : Nat := 266333458102381622527123

theorem tailTrace_4668143 : CollatzResearch.WordTrace tailWord_4668143 prefixEnd_4668143 266333458102381622527123 := by
  unfold tailWord_4668143
  simp only [CollatzResearch.WordTrace]
  refine ⟨170261162727122641196769083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113507441818081760797846055 170261162727122641196769083)
  ·
    refine ⟨255391744090683961795153625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170261162727122641196769083 255391744090683961795153625)
    ·
      refine ⟨191543808068012971346365219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255391744090683961795153625 191543808068012971346365219)
      ·
        refine ⟨287315712102019457019547829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191543808068012971346365219 287315712102019457019547829)
        ·
          refine ⟨26935848009564324095582609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 287315712102019457019547829 26935848009564324095582609)
          ·
            refine ⟨20201886007173243071686957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26935848009564324095582609 20201886007173243071686957)
            ·
              refine ⟨7575707252689966151882609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20201886007173243071686957 7575707252689966151882609)
              ·
                refine ⟨5681780439517474613911957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7575707252689966151882609 5681780439517474613911957)
                ·
                  refine ⟨266333458102381622527123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5681780439517474613911957 266333458102381622527123)
                  ·
                    rfl

theorem cell23_4668143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 6].length) (baseStart_4668143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668143 prefixEnd_4668143 := by exact prefixLift 4668143
  have htrace : WordTrace (prefixWord ++ tailWord_4668143) baseStart_4668143 baseEnd_4668143 := by
    simpa [prefixWord, tailWord_4668143, baseEnd_4668143] using wordTrace_append hprefix tailTrace_4668143
  have hstable : (prefixWord ++ tailWord_4668143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668143).length < 2 ^ (prefixWord ++ tailWord_4668143).sum := by decide
  have hdescent : baseEnd_4668143 < baseStart_4668143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668170 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_4668170 : Nat := 118140960795 + 4668170 * 2 ^ 59
def prefixEnd_4668170 : Nat := 4983230072969 + 3 ^ 40 * 4668170 * 2
def baseEnd_4668170 : Nat := 2397014986899105997106483

theorem tailTrace_4668170 : CollatzResearch.WordTrace tailWord_4668170 prefixEnd_4668170 2397014986899105997106483 := by
  unfold tailWord_4668170
  simp only [CollatzResearch.WordTrace]
  refine ⟨42565536874506206202000491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113508098332016549872001309 42565536874506206202000491)
  ·
    refine ⟨63848305311759309303000737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42565536874506206202000491 63848305311759309303000737)
    ·
      refine ⟨47886228983819481977250553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63848305311759309303000737 47886228983819481977250553)
      ·
        refine ⟨35914671737864611482937915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47886228983819481977250553 35914671737864611482937915)
        ·
          refine ⟨53872007606796917224406873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35914671737864611482937915 53872007606796917224406873)
          ·
            refine ⟨40404005705097687918305155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53872007606796917224406873 40404005705097687918305155)
            ·
              refine ⟨60606008557646531877457733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40404005705097687918305155 60606008557646531877457733)
              ·
                refine ⟨11363626604558724727023325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60606008557646531877457733 11363626604558724727023325)
                ·
                  refine ⟨4261359976709521772633747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11363626604558724727023325 4261359976709521772633747)
                  ·
                    refine ⟨6392039965064282658950621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4261359976709521772633747 6392039965064282658950621)
                    ·
                      refine ⟨2397014986899105997106483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6392039965064282658950621 2397014986899105997106483)
                      ·
                        rfl

theorem cell23_4668170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_4668170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668170 prefixEnd_4668170 := by exact prefixLift 4668170
  have htrace : WordTrace (prefixWord ++ tailWord_4668170) baseStart_4668170 baseEnd_4668170 := by
    simpa [prefixWord, tailWord_4668170, baseEnd_4668170] using wordTrace_append hprefix tailTrace_4668170
  have hstable : (prefixWord ++ tailWord_4668170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668170).length < 2 ^ (prefixWord ++ tailWord_4668170).sum := by decide
  have hdescent : baseEnd_4668170 < baseStart_4668170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668204 : List Nat := [2, 2, 1, 1, 1, 4, 5, 2, 1, 1, 3]
def baseStart_4668204 : Nat := 118140960795 + 4668204 * 2 ^ 59
def prefixEnd_4668204 : Nat := 4983230072969 + 3 ^ 40 * 4668204 * 2
def baseEnd_4668204 : Nat := 2397032445241358864081327

theorem tailTrace_4668204 : CollatzResearch.WordTrace tailWord_4668204 prefixEnd_4668204 2397032445241358864081327 := by
  unfold tailWord_4668204
  simp only [CollatzResearch.WordTrace]
  refine ⟨85131693789950824307369833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113508925053267765743159777 85131693789950824307369833)
  ·
    refine ⟨63848770342463118230527375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85131693789950824307369833 63848770342463118230527375)
    ·
      refine ⟨95773155513694677345791063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63848770342463118230527375 95773155513694677345791063)
      ·
        refine ⟨143659733270542016018686595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95773155513694677345791063 143659733270542016018686595)
        ·
          refine ⟨215489599905813024028029893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143659733270542016018686595 215489599905813024028029893)
          ·
            refine ⟨40404299982339942005255605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215489599905813024028029893 40404299982339942005255605)
            ·
              refine ⟨3787903123344369562992713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40404299982339942005255605 3787903123344369562992713)
              ·
                refine ⟨2840927342508277172244535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3787903123344369562992713 2840927342508277172244535)
                ·
                  refine ⟨4261391013762415758366803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840927342508277172244535 4261391013762415758366803)
                  ·
                    refine ⟨6392086520643623637550205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4261391013762415758366803 6392086520643623637550205)
                    ·
                      refine ⟨2397032445241358864081327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6392086520643623637550205 2397032445241358864081327)
                      ·
                        rfl

theorem cell23_4668204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 1, 1, 3].length) (baseStart_4668204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668204 prefixEnd_4668204 := by exact prefixLift 4668204
  have htrace : WordTrace (prefixWord ++ tailWord_4668204) baseStart_4668204 baseEnd_4668204 := by
    simpa [prefixWord, tailWord_4668204, baseEnd_4668204] using wordTrace_append hprefix tailTrace_4668204
  have hstable : (prefixWord ++ tailWord_4668204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668204).length < 2 ^ (prefixWord ++ tailWord_4668204).sum := by decide
  have hdescent : baseEnd_4668204 < baseStart_4668204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668223 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 6]
def baseStart_4668223 : Nat := 118140960795 + 4668223 * 2 ^ 59
def prefixEnd_4668223 : Nat := 4983230072969 + 3 ^ 40 * 4668223 * 2
def baseEnd_4668223 : Nat := 2397042201373794289743739

theorem tailTrace_4668223 : CollatzResearch.WordTrace tailWord_4668223 prefixEnd_4668223 2397042201373794289743739 := by
  unfold tailWord_4668223
  simp only [CollatzResearch.WordTrace]
  refine ⟨170264080566832814859681323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113509387044555209906454215 170264080566832814859681323)
  ·
    refine ⟨255396120850249222289521985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170264080566832814859681323 255396120850249222289521985)
    ·
      refine ⟨191547090637686916717141489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255396120850249222289521985 191547090637686916717141489)
      ·
        refine ⟨143660317978265187537856117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191547090637686916717141489 143660317978265187537856117)
        ·
          refine ⟨13468154810462361331674011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143660317978265187537856117 13468154810462361331674011)
          ·
            refine ⟨20202232215693541997511017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13468154810462361331674011 20202232215693541997511017)
            ·
              refine ⟨15151674161770156498133263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20202232215693541997511017 15151674161770156498133263)
              ·
                refine ⟨22727511242655234747199895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15151674161770156498133263 22727511242655234747199895)
                ·
                  refine ⟨34091266863982852120799843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22727511242655234747199895 34091266863982852120799843)
                  ·
                    refine ⟨51136900295974278181199765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34091266863982852120799843 51136900295974278181199765)
                    ·
                      refine ⟨2397042201373794289743739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51136900295974278181199765 2397042201373794289743739)
                      ·
                        rfl

theorem cell23_4668223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_4668223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668223 prefixEnd_4668223 := by exact prefixLift 4668223
  have htrace : WordTrace (prefixWord ++ tailWord_4668223) baseStart_4668223 baseEnd_4668223 := by
    simpa [prefixWord, tailWord_4668223, baseEnd_4668223] using wordTrace_append hprefix tailTrace_4668223
  have hstable : (prefixWord ++ tailWord_4668223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668223).length < 2 ^ (prefixWord ++ tailWord_4668223).sum := by decide
  have hdescent : baseEnd_4668223 < baseStart_4668223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668237 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_4668237 : Nat := 118140960795 + 4668237 * 2 ^ 59
def prefixEnd_4668237 : Nat := 4983230072969 + 3 ^ 40 * 4668237 * 2
def baseEnd_4668237 : Nat := 799016463367652411656225

theorem tailTrace_4668237 : CollatzResearch.WordTrace tailWord_4668237 prefixEnd_4668237 799016463367652411656225 := by
  unfold tailWord_4668237
  simp only [CollatzResearch.WordTrace]
  refine ⟨170264591188782095250690965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113509727459188063500460643 170264591188782095250690965)
  ·
    refine ⟨7981152711974160714876139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 170264591188782095250690965 7981152711974160714876139)
    ·
      refine ⟨11971729067961241072314209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7981152711974160714876139 11971729067961241072314209)
      ·
        refine ⟨8978796800970930804235657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11971729067961241072314209 8978796800970930804235657)
        ·
          refine ⟨6734097600728198103176743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8978796800970930804235657 6734097600728198103176743)
          ·
            refine ⟨10101146401092297154765115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6734097600728198103176743 10101146401092297154765115)
            ·
              refine ⟨15151719601638445732147673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10101146401092297154765115 15151719601638445732147673)
              ·
                refine ⟨11363789701228834299110755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15151719601638445732147673 11363789701228834299110755)
                ·
                  refine ⟨17045684551843251448666133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11363789701228834299110755 17045684551843251448666133)
                  ·
                    refine ⟨799016463367652411656225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17045684551843251448666133 799016463367652411656225)
                    ·
                      rfl

theorem cell23_4668237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_4668237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668237 prefixEnd_4668237 := by exact prefixLift 4668237
  have htrace : WordTrace (prefixWord ++ tailWord_4668237) baseStart_4668237 baseEnd_4668237 := by
    simpa [prefixWord, tailWord_4668237, baseEnd_4668237] using wordTrace_append hprefix tailTrace_4668237
  have hstable : (prefixWord ++ tailWord_4668237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668237).length < 2 ^ (prefixWord ++ tailWord_4668237).sum := by decide
  have hdescent : baseEnd_4668237 < baseStart_4668237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668244 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_4668244 : Nat := 118140960795 + 4668244 * 2 ^ 59
def prefixEnd_4668244 : Nat := 4983230072969 + 3 ^ 40 * 4668244 * 2
def baseEnd_4668244 : Nat := 2397052984467538707581143

theorem tailTrace_4668244 : CollatzResearch.WordTrace tailWord_4668244 prefixEnd_4668244 2397052984467538707581143 := by
  unfold tailWord_4668244
  simp only [CollatzResearch.WordTrace]
  refine ⟨85132423249878367723097893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113509897666504490297463857 85132423249878367723097893)
  ·
    refine ⟨15962329359352193948080855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85132423249878367723097893 15962329359352193948080855)
    ·
      refine ⟨23943494039028290922121283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15962329359352193948080855 23943494039028290922121283)
      ·
        refine ⟨35915241058542436383181925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23943494039028290922121283 35915241058542436383181925)
        ·
          refine ⟨6734107698476706821846611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35915241058542436383181925 6734107698476706821846611)
          ·
            refine ⟨10101161547715060232769917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6734107698476706821846611 10101161547715060232769917)
            ·
              refine ⟨3787935580393147587288719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10101161547715060232769917 3787935580393147587288719)
              ·
                refine ⟨5681903370589721380933079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3787935580393147587288719 5681903370589721380933079)
                ·
                  refine ⟨8522855055884582071399619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5681903370589721380933079 8522855055884582071399619)
                  ·
                    refine ⟨12784282583826873107099429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8522855055884582071399619 12784282583826873107099429)
                    ·
                      refine ⟨2397052984467538707581143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12784282583826873107099429 2397052984467538707581143)
                      ·
                        rfl

theorem cell23_4668244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_4668244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668244 prefixEnd_4668244 := by exact prefixLift 4668244
  have htrace : WordTrace (prefixWord ++ tailWord_4668244) baseStart_4668244 baseEnd_4668244 := by
    simpa [prefixWord, tailWord_4668244, baseEnd_4668244] using wordTrace_append hprefix tailTrace_4668244
  have hstable : (prefixWord ++ tailWord_4668244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668244).length < 2 ^ (prefixWord ++ tailWord_4668244).sum := by decide
  have hdescent : baseEnd_4668244 < baseStart_4668244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668261 : List Nat := [1, 3, 1, 3, 1, 1, 6, 2, 1, 2, 2]
def baseStart_4668261 : Nat := 118140960795 + 4668261 * 2 ^ 59
def prefixEnd_4668261 : Nat := 4983230072969 + 3 ^ 40 * 4668261 * 2
def baseEnd_4668261 : Nat := 2397061713638665141068565

theorem tailTrace_4668261 : CollatzResearch.WordTrace tailWord_4668261 prefixEnd_4668261 2397061713638665141068565 := by
  unfold tailWord_4668261
  simp only [CollatzResearch.WordTrace]
  refine ⟨170265466540695147349564637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113510311027130098233043091 170265466540695147349564637)
  ·
    refine ⟨63849549952760680256086739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170265466540695147349564637 63849549952760680256086739)
    ·
      refine ⟨95774324929141020384130109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63849549952760680256086739 95774324929141020384130109)
      ·
        refine ⟨35915371848427882644048791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95774324929141020384130109 35915371848427882644048791)
        ·
          refine ⟨53873057772641823966073187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35915371848427882644048791 53873057772641823966073187)
          ·
            refine ⟨80809586658962735949109781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53873057772641823966073187 80809586658962735949109781)
            ·
              refine ⟨3787949374638878247614521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80809586658962735949109781 3787949374638878247614521)
              ·
                refine ⟨2840962030979158685710891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3787949374638878247614521 2840962030979158685710891)
                ·
                  refine ⟨4261443046468738028566337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840962030979158685710891 4261443046468738028566337)
                  ·
                    refine ⟨3196082284851553521424753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4261443046468738028566337 3196082284851553521424753)
                    ·
                      refine ⟨2397061713638665141068565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196082284851553521424753 2397061713638665141068565)
                      ·
                        rfl

theorem cell23_4668261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_4668261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668261 prefixEnd_4668261 := by exact prefixLift 4668261
  have htrace : WordTrace (prefixWord ++ tailWord_4668261) baseStart_4668261 baseEnd_4668261 := by
    simpa [prefixWord, tailWord_4668261, baseEnd_4668261] using wordTrace_append hprefix tailTrace_4668261
  have hstable : (prefixWord ++ tailWord_4668261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668261).length < 2 ^ (prefixWord ++ tailWord_4668261).sum := by decide
  have hdescent : baseEnd_4668261 < baseStart_4668261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668263 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 2, 7]
def baseStart_4668263 : Nat := 118140960795 + 4668263 * 2 ^ 59
def prefixEnd_4668263 : Nat := 4983230072969 + 3 ^ 40 * 4668263 * 2
def baseEnd_4668263 : Nat := 799020913533324711081185

theorem tailTrace_4668263 : CollatzResearch.WordTrace tailWord_4668263 prefixEnd_4668263 799020913533324711081185 := by
  unfold tailWord_4668263
  simp only [CollatzResearch.WordTrace]
  refine ⟨170265539486687901691137443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113510359657791934460758295 170265539486687901691137443)
  ·
    refine ⟨255398309230031852536706165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170265539486687901691137443 255398309230031852536706165)
    ·
      refine ⟨23943591490315486175316203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 255398309230031852536706165 23943591490315486175316203)
      ·
        refine ⟨35915387235473229262974305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23943591490315486175316203 35915387235473229262974305)
        ·
          refine ⟨26936540426604921947230729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35915387235473229262974305 26936540426604921947230729)
          ·
            refine ⟨20202405319953691460423047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26936540426604921947230729 20202405319953691460423047)
            ·
              refine ⟨30303607979930537190634571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20202405319953691460423047 30303607979930537190634571)
              ·
                refine ⟨45455411969895805785951857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30303607979930537190634571 45455411969895805785951857)
                ·
                  refine ⟨34091558977421854339463893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45455411969895805785951857 34091558977421854339463893)
                  ·
                    refine ⟨799020913533324711081185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34091558977421854339463893 799020913533324711081185)
                    ·
                      rfl

theorem cell23_4668263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_4668263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668263 prefixEnd_4668263 := by exact prefixLift 4668263
  have htrace : WordTrace (prefixWord ++ tailWord_4668263) baseStart_4668263 baseEnd_4668263 := by
    simpa [prefixWord, tailWord_4668263, baseEnd_4668263] using wordTrace_append hprefix tailTrace_4668263
  have hstable : (prefixWord ++ tailWord_4668263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668263).length < 2 ^ (prefixWord ++ tailWord_4668263).sum := by decide
  have hdescent : baseEnd_4668263 < baseStart_4668263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668277 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_4668277 : Nat := 118140960795 + 4668277 * 2 ^ 59
def prefixEnd_4668277 : Nat := 4983230072969 + 3 ^ 40 * 4668277 * 2
def baseEnd_4668277 : Nat := 2397069929329137078468491

theorem tailTrace_4668277 : CollatzResearch.WordTrace tailWord_4668277 prefixEnd_4668277 2397069929329137078468491 := by
  unfold tailWord_4668277
  simp only [CollatzResearch.WordTrace]
  refine ⟨170266050108637182082147085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113510700072424788054764723 170266050108637182082147085)
  ·
    refine ⟨63849768790738943280805157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170266050108637182082147085 63849768790738943280805157)
    ·
      refine ⟨11971831648263551865150967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63849768790738943280805157 11971831648263551865150967)
      ·
        refine ⟨17957747472395327797726451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11971831648263551865150967 17957747472395327797726451)
        ·
          refine ⟨26936621208592991696589677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17957747472395327797726451 26936621208592991696589677)
          ·
            refine ⟨10101232953222371886221129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26936621208592991696589677 10101232953222371886221129)
            ·
              refine ⟨7575924714916778914665847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10101232953222371886221129 7575924714916778914665847)
              ·
                refine ⟨11363887072375168371998771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7575924714916778914665847 11363887072375168371998771)
                ·
                  refine ⟨17045830608562752557998157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11363887072375168371998771 17045830608562752557998157)
                  ·
                    refine ⟨6392186478211032209249309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17045830608562752557998157 6392186478211032209249309)
                    ·
                      refine ⟨2397069929329137078468491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6392186478211032209249309 2397069929329137078468491)
                      ·
                        rfl

theorem cell23_4668277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_4668277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668277 prefixEnd_4668277 := by exact prefixLift 4668277
  have htrace : WordTrace (prefixWord ++ tailWord_4668277) baseStart_4668277 baseEnd_4668277 := by
    simpa [prefixWord, tailWord_4668277, baseEnd_4668277] using wordTrace_append hprefix tailTrace_4668277
  have hstable : (prefixWord ++ tailWord_4668277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668277).length < 2 ^ (prefixWord ++ tailWord_4668277).sum := by decide
  have hdescent : baseEnd_4668277 < baseStart_4668277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668323 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 7]
def baseStart_4668323 : Nat := 118140960795 + 4668323 * 2 ^ 59
def prefixEnd_4668323 : Nat := 4983230072969 + 3 ^ 40 * 4668323 * 2
def baseEnd_4668323 : Nat := 266343727715471544277031

theorem tailTrace_4668323 : CollatzResearch.WordTrace tailWord_4668323 prefixEnd_4668323 266343727715471544277031 := by
  unfold tailWord_4668323
  simp only [CollatzResearch.WordTrace]
  refine ⟨170267727866470531938321623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113511818577647021292214415 170267727866470531938321623)
  ·
    refine ⟨255401591799705797907482435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170267727866470531938321623 255401591799705797907482435)
    ·
      refine ⟨383102387699558696861223653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255401591799705797907482435 383102387699558696861223653)
      ·
        refine ⟨71831697693667255661479435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 383102387699558696861223653 71831697693667255661479435)
        ·
          refine ⟨107747546540500883492219153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71831697693667255661479435 107747546540500883492219153)
          ·
            refine ⟨80810659905375662619164365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107747546540500883492219153 80810659905375662619164365)
            ·
              refine ⟨30303997464515873482186637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80810659905375662619164365 30303997464515873482186637)
              ·
                refine ⟨11363999049193452555819989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30303997464515873482186637 11363999049193452555819989)
                ·
                  refine ⟨266343727715471544277031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11363999049193452555819989 266343727715471544277031)
                  ·
                    rfl

theorem cell23_4668323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 7].length) (baseStart_4668323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668323 prefixEnd_4668323 := by exact prefixLift 4668323
  have htrace : WordTrace (prefixWord ++ tailWord_4668323) baseStart_4668323 baseEnd_4668323 := by
    simpa [prefixWord, tailWord_4668323, baseEnd_4668323] using wordTrace_append hprefix tailTrace_4668323
  have hstable : (prefixWord ++ tailWord_4668323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668323).length < 2 ^ (prefixWord ++ tailWord_4668323).sum := by decide
  have hdescent : baseEnd_4668323 < baseStart_4668323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668374 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_4668374 : Nat := 118140960795 + 4668374 * 2 ^ 59
def prefixEnd_4668374 : Nat := 4983230072969 + 3 ^ 40 * 4668374 * 2
def baseEnd_4668374 : Nat := 266346637439180355439505

theorem tailTrace_4668374 : CollatzResearch.WordTrace tailWord_4668374 prefixEnd_4668374 266346637439180355439505 := by
  unfold tailWord_4668374
  simp only [CollatzResearch.WordTrace]
  refine ⟨10641849249330360478026761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113513058659523845098952117 10641849249330360478026761)
  ·
    refine ⟨7981386936997770358520071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10641849249330360478026761 7981386936997770358520071)
    ·
      refine ⟨11972080405496655537780107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7981386936997770358520071 11972080405496655537780107)
      ·
        refine ⟨17958120608244983306670161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11972080405496655537780107 17958120608244983306670161)
        ·
          refine ⟨13468590456183737480002621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17958120608244983306670161 13468590456183737480002621)
          ·
            refine ⟨5050721421068901555000983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13468590456183737480002621 5050721421068901555000983)
            ·
              refine ⟨7576082131603352332501475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5050721421068901555000983 7576082131603352332501475)
              ·
                refine ⟨11364123197405028498752213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7576082131603352332501475 11364123197405028498752213)
                ·
                  refine ⟨266346637439180355439505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11364123197405028498752213 266346637439180355439505)
                  ·
                    rfl

theorem cell23_4668374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_4668374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668374 prefixEnd_4668374 := by exact prefixLift 4668374
  have htrace : WordTrace (prefixWord ++ tailWord_4668374) baseStart_4668374 baseEnd_4668374 := by
    simpa [prefixWord, tailWord_4668374, baseEnd_4668374] using wordTrace_append hprefix tailTrace_4668374
  have hstable : (prefixWord ++ tailWord_4668374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668374).length < 2 ^ (prefixWord ++ tailWord_4668374).sum := by decide
  have hdescent : baseEnd_4668374 < baseStart_4668374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668393 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_4668393 : Nat := 118140960795 + 4668393 * 2 ^ 59
def prefixEnd_4668393 : Nat := 4983230072969 + 3 ^ 40 * 4668393 * 2
def baseEnd_4668393 : Nat := 2397129493085058624617957

theorem tailTrace_4668393 : CollatzResearch.WordTrace tailWord_4668393 prefixEnd_4668393 2397129493085058624617957 := by
  unfold tailWord_4668393
  simp only [CollatzResearch.WordTrace]
  refine ⟨170270280976216933893369833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113513520650811289262246555 170270280976216933893369833)
  ·
    refine ⟨127702710732162700420027375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170270280976216933893369833 127702710732162700420027375)
    ·
      refine ⟨191554066098244050630041063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127702710732162700420027375 191554066098244050630041063)
      ·
        refine ⟨287331099147366075945061595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191554066098244050630041063 287331099147366075945061595)
        ·
          refine ⟨430996648721049113917592393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287331099147366075945061595 430996648721049113917592393)
          ·
            refine ⟨323247486540786835438194295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430996648721049113917592393 323247486540786835438194295)
            ·
              refine ⟨484871229811180253157291443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323247486540786835438194295 484871229811180253157291443)
              ·
                refine ⟨727306844716770379735937165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484871229811180253157291443 727306844716770379735937165)
                ·
                  refine ⟨272740066768788892400976437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 727306844716770379735937165 272740066768788892400976437)
                  ·
                    refine ⟨25569381259573958662591541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 272740066768788892400976437 25569381259573958662591541)
                    ·
                      refine ⟨2397129493085058624617957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25569381259573958662591541 2397129493085058624617957)
                      ·
                        rfl

theorem cell23_4668393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_4668393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668393 prefixEnd_4668393 := by exact prefixLift 4668393
  have htrace : WordTrace (prefixWord ++ tailWord_4668393) baseStart_4668393 baseEnd_4668393 := by
    simpa [prefixWord, tailWord_4668393, baseEnd_4668393] using wordTrace_append hprefix tailTrace_4668393
  have hstable : (prefixWord ++ tailWord_4668393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668393).length < 2 ^ (prefixWord ++ tailWord_4668393).sum := by decide
  have hdescent : baseEnd_4668393 < baseStart_4668393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668400 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 5, 4]
def baseStart_4668400 : Nat := 118140960795 + 4668400 * 2 ^ 59
def prefixEnd_4668400 : Nat := 4983230072969 + 3 ^ 40 * 4668400 * 2
def baseEnd_4668400 : Nat := 799044362483213365743475

theorem tailTrace_4668400 : CollatzResearch.WordTrace tailWord_4668400 prefixEnd_4668400 799044362483213365743475 := by
  unfold tailWord_4668400
  simp only [CollatzResearch.WordTrace]
  refine ⟨85135268143595787044437327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113513690858127716059249769 85135268143595787044437327)
  ·
    refine ⟨127702902215393680566655991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85135268143595787044437327 127702902215393680566655991)
    ·
      refine ⟨191554353323090520849983987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127702902215393680566655991 191554353323090520849983987)
      ·
        refine ⟨287331529984635781274975981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191554353323090520849983987 287331529984635781274975981)
        ·
          refine ⟨107749323744238417978115993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287331529984635781274975981 107749323744238417978115993)
          ·
            refine ⟨80811992808178813483586995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107749323744238417978115993 80811992808178813483586995)
            ·
              refine ⟨121217989212268220225380493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80811992808178813483586995 121217989212268220225380493)
              ·
                refine ⟨45456745954600582584517685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121217989212268220225380493 45456745954600582584517685)
                ·
                  refine ⟨4261569933243804617298533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45456745954600582584517685 4261569933243804617298533)
                  ·
                    refine ⟨799044362483213365743475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4261569933243804617298533 799044362483213365743475)
                    ·
                      rfl

theorem cell23_4668400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 5, 4].length) (baseStart_4668400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668400 prefixEnd_4668400 := by exact prefixLift 4668400
  have htrace : WordTrace (prefixWord ++ tailWord_4668400) baseStart_4668400 baseEnd_4668400 := by
    simpa [prefixWord, tailWord_4668400, baseEnd_4668400] using wordTrace_append hprefix tailTrace_4668400
  have hstable : (prefixWord ++ tailWord_4668400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668400).length < 2 ^ (prefixWord ++ tailWord_4668400).sum := by decide
  have hdescent : baseEnd_4668400 < baseStart_4668400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668403 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 6]
def baseStart_4668403 : Nat := 118140960795 + 4668403 * 2 ^ 59
def prefixEnd_4668403 : Nat := 4983230072969 + 3 ^ 40 * 4668403 * 2
def baseEnd_4668403 : Nat := 2397134627891603585492911

theorem tailTrace_4668403 : CollatzResearch.WordTrace tailWord_4668403 prefixEnd_4668403 2397134627891603585492911 := by
  unfold tailWord_4668403
  simp only [CollatzResearch.WordTrace]
  refine ⟨170270645706180705601233863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113513763804120470400822575 170270645706180705601233863)
  ·
    refine ⟨255405968559271058401850795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170270645706180705601233863 255405968559271058401850795)
    ·
      refine ⟨383108952838906587602776193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255405968559271058401850795 383108952838906587602776193)
      ·
        refine ⟨287331714629179940702082145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383108952838906587602776193 287331714629179940702082145)
        ·
          refine ⟨215498785971884955526561609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287331714629179940702082145 215498785971884955526561609)
          ·
            refine ⟨161624089478913716644921207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215498785971884955526561609 161624089478913716644921207)
            ·
              refine ⟨242436134218370574967381811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161624089478913716644921207 242436134218370574967381811)
              ·
                refine ⟨363654201327555862451072717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242436134218370574967381811 363654201327555862451072717)
                ·
                  refine ⟨136370325497833448419152269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363654201327555862451072717 136370325497833448419152269)
                  ·
                    refine ⟨51138872061687543157182101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 136370325497833448419152269 51138872061687543157182101)
                    ·
                      refine ⟨2397134627891603585492911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51138872061687543157182101 2397134627891603585492911)
                      ·
                        rfl

theorem cell23_4668403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_4668403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668403 prefixEnd_4668403 := by exact prefixLift 4668403
  have htrace : WordTrace (prefixWord ++ tailWord_4668403) baseStart_4668403 baseEnd_4668403 := by
    simpa [prefixWord, tailWord_4668403, baseEnd_4668403] using wordTrace_append hprefix tailTrace_4668403
  have hstable : (prefixWord ++ tailWord_4668403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668403).length < 2 ^ (prefixWord ++ tailWord_4668403).sum := by decide
  have hdescent : baseEnd_4668403 < baseStart_4668403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668410 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3]
def baseStart_4668410 : Nat := 118140960795 + 4668410 * 2 ^ 59
def prefixEnd_4668410 : Nat := 4983230072969 + 3 ^ 40 * 4668410 * 2
def baseEnd_4668410 : Nat := 2397138222256185058105379

theorem tailTrace_4668410 : CollatzResearch.WordTrace tailWord_4668410 prefixEnd_4668410 2397138222256185058105379 := by
  unfold tailWord_4668410
  simp only [CollatzResearch.WordTrace]
  refine ⟨42567725254288836449184671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113513934011436897197825789 42567725254288836449184671)
  ·
    refine ⟨63851587881433254673777007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42567725254288836449184671 63851587881433254673777007)
    ·
      refine ⟨95777381822149882010665511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63851587881433254673777007 95777381822149882010665511)
      ·
        refine ⟨143666072733224823015998267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95777381822149882010665511 143666072733224823015998267)
        ·
          refine ⟨215499109099837234523997401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143666072733224823015998267 215499109099837234523997401)
          ·
            refine ⟨161624331824877925892998051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215499109099837234523997401 161624331824877925892998051)
            ·
              refine ⟨242436497737316888839497077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161624331824877925892998051 242436497737316888839497077)
              ·
                refine ⟨22728421662873458328702851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 242436497737316888839497077 22728421662873458328702851)
                ·
                  refine ⟨34092632494310187493054277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22728421662873458328702851 34092632494310187493054277)
                  ·
                    refine ⟨6392368592683160154947677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34092632494310187493054277 6392368592683160154947677)
                    ·
                      refine ⟨2397138222256185058105379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6392368592683160154947677 2397138222256185058105379)
                      ·
                        rfl

theorem cell23_4668410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_4668410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668410 prefixEnd_4668410 := by exact prefixLift 4668410
  have htrace : WordTrace (prefixWord ++ tailWord_4668410) baseStart_4668410 baseEnd_4668410 := by
    simpa [prefixWord, tailWord_4668410, baseEnd_4668410] using wordTrace_append hprefix tailTrace_4668410
  have hstable : (prefixWord ++ tailWord_4668410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668410).length < 2 ^ (prefixWord ++ tailWord_4668410).sum := by decide
  have hdescent : baseEnd_4668410 < baseStart_4668410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668427 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 3]
def baseStart_4668427 : Nat := 118140960795 + 4668427 * 2 ^ 59
def prefixEnd_4668427 : Nat := 4983230072969 + 3 ^ 40 * 4668427 * 2
def baseEnd_4668427 : Nat := 2397146951427311491592801

theorem tailTrace_4668427 : CollatzResearch.WordTrace tailWord_4668427 prefixEnd_4668427 2397146951427311491592801 := by
  unfold tailWord_4668427
  simp only [CollatzResearch.WordTrace]
  refine ⟨170271521058093757700107535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113514347372062505133405023 170271521058093757700107535)
  ·
    refine ⟨255407281587140636550161303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170271521058093757700107535 255407281587140636550161303)
    ·
      refine ⟨383110922380710954825241955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255407281587140636550161303 383110922380710954825241955)
      ·
        refine ⟨574666383571066432237862933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383110922380710954825241955 574666383571066432237862933)
        ·
          refine ⟨26937486729893739011149825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 574666383571066432237862933 26937486729893739011149825)
          ·
            refine ⟨20203115047420304258362369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26937486729893739011149825 20203115047420304258362369)
            ·
              refine ⟨15152336285565228193771777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20203115047420304258362369 15152336285565228193771777)
              ·
                refine ⟨11364252214173921145328833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15152336285565228193771777 11364252214173921145328833)
                ·
                  refine ⟨8523189160630440858996625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11364252214173921145328833 8523189160630440858996625)
                  ·
                    refine ⟨6392391870472830644247469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8523189160630440858996625 6392391870472830644247469)
                    ·
                      refine ⟨2397146951427311491592801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6392391870472830644247469 2397146951427311491592801)
                      ·
                        rfl

theorem cell23_4668427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 3].length) (baseStart_4668427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668427 prefixEnd_4668427 := by exact prefixLift 4668427
  have htrace : WordTrace (prefixWord ++ tailWord_4668427) baseStart_4668427 baseEnd_4668427 := by
    simpa [prefixWord, tailWord_4668427, baseEnd_4668427] using wordTrace_append hprefix tailTrace_4668427
  have hstable : (prefixWord ++ tailWord_4668427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668427).length < 2 ^ (prefixWord ++ tailWord_4668427).sum := by decide
  have hdescent : baseEnd_4668427 < baseStart_4668427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668460 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_4668460 : Nat := 118140960795 + 4668460 * 2 ^ 59
def prefixEnd_4668460 : Nat := 4983230072969 + 3 ^ 40 * 4668460 * 2
def baseEnd_4668460 : Nat := 799054632096303287493383

theorem tailTrace_4668460 : CollatzResearch.WordTrace tailWord_4668460 prefixEnd_4668460 799054632096303287493383 := by
  unfold tailWord_4668460
  simp only [CollatzResearch.WordTrace]
  refine ⟨85136362333487102168029417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113515149777982802890705889 85136362333487102168029417)
  ·
    refine ⟨63852271750115326626022063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85136362333487102168029417 63852271750115326626022063)
    ·
      refine ⟨95778407625172989939033095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63852271750115326626022063 95778407625172989939033095)
      ·
        refine ⟨143667611437759484908549643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95778407625172989939033095 143667611437759484908549643)
        ·
          refine ⟨215501417156639227362824465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143667611437759484908549643 215501417156639227362824465)
          ·
            refine ⟨161626062867479420522118349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215501417156639227362824465 161626062867479420522118349)
            ·
              refine ⟨60609773575304782695794381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161626062867479420522118349 60609773575304782695794381)
              ·
                refine ⟨22728665090739293510922893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60609773575304782695794381 22728665090739293510922893)
                ·
                  refine ⟨8523249409027235066596085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22728665090739293510922893 8523249409027235066596085)
                  ·
                    refine ⟨799054632096303287493383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8523249409027235066596085 799054632096303287493383)
                    ·
                      rfl

theorem cell23_4668460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_4668460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668460 prefixEnd_4668460 := by exact prefixLift 4668460
  have htrace : WordTrace (prefixWord ++ tailWord_4668460) baseStart_4668460 baseEnd_4668460 := by
    simpa [prefixWord, tailWord_4668460, baseEnd_4668460] using wordTrace_append hprefix tailTrace_4668460
  have hstable : (prefixWord ++ tailWord_4668460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668460).length < 2 ^ (prefixWord ++ tailWord_4668460).sum := by decide
  have hdescent : baseEnd_4668460 < baseStart_4668460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668468 : List Nat := [2, 5, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_4668468 : Nat := 118140960795 + 4668468 * 2 ^ 59
def prefixEnd_4668468 : Nat := 4983230072969 + 3 ^ 40 * 4668468 * 2
def baseEnd_4668468 : Nat := 799056001378048610393371

theorem tailTrace_4668468 : CollatzResearch.WordTrace tailWord_4668468 prefixEnd_4668468 799056001378048610393371 := by
  unfold tailWord_4668468
  simp only [CollatzResearch.WordTrace]
  refine ⟨85136508225472610851175029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113515344300630147801566705 85136508225472610851175029)
  ·
    refine ⟨7981547646138057267297659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85136508225472610851175029 7981547646138057267297659)
    ·
      refine ⟨11972321469207085900946489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7981547646138057267297659 11972321469207085900946489)
      ·
        refine ⟨8979241101905314425709867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11972321469207085900946489 8979241101905314425709867)
        ·
          refine ⟨13468861652857971638564801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8979241101905314425709867 13468861652857971638564801)
          ·
            refine ⟨10101646239643478728923601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13468861652857971638564801 10101646239643478728923601)
            ·
              refine ⟨7576234679732609046692701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10101646239643478728923601 7576234679732609046692701)
              ·
                refine ⟨2841088004899728392509763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7576234679732609046692701 2841088004899728392509763)
                ·
                  refine ⟨4261632007349592588764645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841088004899728392509763 4261632007349592588764645)
                  ·
                    refine ⟨799056001378048610393371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4261632007349592588764645 799056001378048610393371)
                    ·
                      rfl

theorem cell23_4668468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_4668468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668468 prefixEnd_4668468 := by exact prefixLift 4668468
  have htrace : WordTrace (prefixWord ++ tailWord_4668468) baseStart_4668468 baseEnd_4668468 := by
    simpa [prefixWord, tailWord_4668468, baseEnd_4668468] using wordTrace_append hprefix tailTrace_4668468
  have hstable : (prefixWord ++ tailWord_4668468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668468).length < 2 ^ (prefixWord ++ tailWord_4668468).sum := by decide
  have hdescent : baseEnd_4668468 < baseStart_4668468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668481 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 6]
def baseStart_4668481 : Nat := 118140960795 + 4668481 * 2 ^ 59
def prefixEnd_4668481 : Nat := 4983230072969 + 3 ^ 40 * 4668481 * 2
def baseEnd_4668481 : Nat := 266352742153628253368617

theorem tailTrace_4668481 : CollatzResearch.WordTrace tailWord_4668481 prefixEnd_4668481 266352742153628253368617 := by
  unfold tailWord_4668481
  simp only [CollatzResearch.WordTrace]
  refine ⟨170273490599898124922573297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113515660399932083281715531 170273490599898124922573297)
  ·
    refine ⟨127705117949923593691929973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170273490599898124922573297 127705117949923593691929973)
    ·
      refine ⟨11972354807805336908618435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127705117949923593691929973 11972354807805336908618435)
      ·
        refine ⟨17958532211708005362927653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11972354807805336908618435 17958532211708005362927653)
        ·
          refine ⟨3367224789695251005548935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17958532211708005362927653 3367224789695251005548935)
          ·
            refine ⟨5050837184542876508323403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3367224789695251005548935 5050837184542876508323403)
            ·
              refine ⟨7576255776814314762485105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5050837184542876508323403 7576255776814314762485105)
              ·
                refine ⟨5682191832610736071863829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7576255776814314762485105 5682191832610736071863829)
                ·
                  refine ⟨266352742153628253368617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5682191832610736071863829 266352742153628253368617)
                  ·
                    rfl

theorem cell23_4668481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 6].length) (baseStart_4668481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668481 prefixEnd_4668481 := by exact prefixLift 4668481
  have htrace : WordTrace (prefixWord ++ tailWord_4668481) baseStart_4668481 baseEnd_4668481 := by
    simpa [prefixWord, tailWord_4668481, baseEnd_4668481] using wordTrace_append hprefix tailTrace_4668481
  have hstable : (prefixWord ++ tailWord_4668481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668481).length < 2 ^ (prefixWord ++ tailWord_4668481).sum := by decide
  have hdescent : baseEnd_4668481 < baseStart_4668481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668490 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_4668490 : Nat := 118140960795 + 4668490 * 2 ^ 59
def prefixEnd_4668490 : Nat := 4983230072969 + 3 ^ 40 * 4668490 * 2
def baseEnd_4668490 : Nat := 799059766902848248368337

theorem tailTrace_4668490 : CollatzResearch.WordTrace tailWord_4668490 prefixEnd_4668490 799059766902848248368337 := by
  unfold tailWord_4668490
  simp only [CollatzResearch.WordTrace]
  refine ⟨42568454714216379864912731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113515879237910346306433949 42568454714216379864912731)
  ·
    refine ⟨63852682071324569797369097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42568454714216379864912731 63852682071324569797369097)
    ·
      refine ⟨47889511553493427348026823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63852682071324569797369097 47889511553493427348026823)
      ·
        refine ⟨71834267330240141022040235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47889511553493427348026823 71834267330240141022040235)
        ·
          refine ⟨107751400995360211533060353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71834267330240141022040235 107751400995360211533060353)
          ·
            refine ⟨80813550746520158649795265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107751400995360211533060353 80813550746520158649795265)
            ·
              refine ⟨60610163059890118987346449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80813550746520158649795265 60610163059890118987346449)
              ·
                refine ⟨45457622294917589240509837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60610163059890118987346449 45457622294917589240509837)
                ·
                  refine ⟨17046608360594095965191189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45457622294917589240509837 17046608360594095965191189)
                  ·
                    refine ⟨799059766902848248368337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17046608360594095965191189 799059766902848248368337)
                    ·
                      rfl

theorem cell23_4668490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_4668490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668490 prefixEnd_4668490 := by exact prefixLift 4668490
  have htrace : WordTrace (prefixWord ++ tailWord_4668490) baseStart_4668490 baseEnd_4668490 := by
    simpa [prefixWord, tailWord_4668490, baseEnd_4668490] using wordTrace_append hprefix tailTrace_4668490
  have hstable : (prefixWord ++ tailWord_4668490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668490).length < 2 ^ (prefixWord ++ tailWord_4668490).sum := by decide
  have hdescent : baseEnd_4668490 < baseStart_4668490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668534 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_4668534 : Nat := 118140960795 + 4668534 * 2 ^ 59
def prefixEnd_4668534 : Nat := 4983230072969 + 3 ^ 40 * 4668534 * 2
def baseEnd_4668534 : Nat := 2397201893857342572954809

theorem tailTrace_4668534 : CollatzResearch.WordTrace tailWord_4668534 prefixEnd_4668534 2397201893857342572954809 := by
  unfold tailWord_4668534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10642213979294132185890791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113516949112470743316168437 10642213979294132185890791)
  ·
    refine ⟨15963320968941198278836187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10642213979294132185890791 15963320968941198278836187)
    ·
      refine ⟨23944981453411797418254281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15963320968941198278836187 23944981453411797418254281)
      ·
        refine ⟨17958736090058848063690711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23944981453411797418254281 17958736090058848063690711)
        ·
          refine ⟨26938104135088272095536067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17958736090058848063690711 26938104135088272095536067)
          ·
            refine ⟨40407156202632408143304101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26938104135088272095536067 40407156202632408143304101)
            ·
              refine ⟨7576341787993576526869519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40407156202632408143304101 7576341787993576526869519)
              ·
                refine ⟨11364512681990364790304279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7576341787993576526869519 11364512681990364790304279)
                ·
                  refine ⟨17046769022985547185456419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11364512681990364790304279 17046769022985547185456419)
                  ·
                    refine ⟨25570153534478320778184629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17046769022985547185456419 25570153534478320778184629)
                    ·
                      refine ⟨2397201893857342572954809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25570153534478320778184629 2397201893857342572954809)
                      ·
                        rfl

theorem cell23_4668534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_4668534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668534 prefixEnd_4668534 := by exact prefixLift 4668534
  have htrace : WordTrace (prefixWord ++ tailWord_4668534) baseStart_4668534 baseEnd_4668534 := by
    simpa [prefixWord, tailWord_4668534, baseEnd_4668534] using wordTrace_append hprefix tailTrace_4668534
  have hstable : (prefixWord ++ tailWord_4668534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668534).length < 2 ^ (prefixWord ++ tailWord_4668534).sum := by decide
  have hdescent : baseEnd_4668534 < baseStart_4668534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668537 : List Nat := [1, 2, 1, 3, 5, 2, 9]
def baseStart_4668537 : Nat := 118140960795 + 4668537 * 2 ^ 59
def prefixEnd_4668537 : Nat := 4983230072969 + 3 ^ 40 * 4668537 * 2
def baseEnd_4668537 : Nat := 29595104127151926681695

theorem tailTrace_4668537 : CollatzResearch.WordTrace tailWord_4668537 prefixEnd_4668537 29595104127151926681695 := by
  unfold tailWord_4668537
  simp only [CollatzResearch.WordTrace]
  refine ⟨170275533087695246486611865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113517022058463497657741243 170275533087695246486611865)
  ·
    refine ⟨127706649815771434864958899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170275533087695246486611865 127706649815771434864958899)
    ·
      refine ⟨191559974723657152297438349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127706649815771434864958899 191559974723657152297438349)
      ·
        refine ⟨71834990521371432111539381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191559974723657152297438349 71834990521371432111539381)
        ·
          refine ⟨6734530361378571760456817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71834990521371432111539381 6734530361378571760456817)
          ·
            refine ⟨5050897771033928820342613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6734530361378571760456817 5050897771033928820342613)
            ·
              refine ⟨29595104127151926681695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5050897771033928820342613 29595104127151926681695)
              ·
                rfl

theorem cell23_4668537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 9].length) (baseStart_4668537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668537 prefixEnd_4668537 := by exact prefixLift 4668537
  have htrace : WordTrace (prefixWord ++ tailWord_4668537) baseStart_4668537 baseEnd_4668537 := by
    simpa [prefixWord, tailWord_4668537, baseEnd_4668537] using wordTrace_append hprefix tailTrace_4668537
  have hstable : (prefixWord ++ tailWord_4668537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668537).length < 2 ^ (prefixWord ++ tailWord_4668537).sum := by decide
  have hdescent : baseEnd_4668537 < baseStart_4668537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668542 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4668542 : Nat := 118140960795 + 4668542 * 2 ^ 59
def prefixEnd_4668542 : Nat := 4983230072969 + 3 ^ 40 * 4668542 * 2
def baseEnd_4668542 : Nat := 2397206001702578541654773

theorem tailTrace_4668542 : CollatzResearch.WordTrace tailWord_4668542 prefixEnd_4668542 2397206001702578541654773 := by
  unfold tailWord_4668542
  simp only [CollatzResearch.WordTrace]
  refine ⟨21284464431584641542567985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113517143635118088227029253 21284464431584641542567985)
  ·
    refine ⟨15963348323688481156925989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21284464431584641542567985 15963348323688481156925989)
    ·
      refine ⟨2993127810691590216923623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15963348323688481156925989 2993127810691590216923623)
      ·
        refine ⟨4489691716037385325385435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2993127810691590216923623 4489691716037385325385435)
        ·
          refine ⟨6734537574056077988078153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4489691716037385325385435 6734537574056077988078153)
          ·
            refine ⟨5050903180542058491058615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6734537574056077988078153 5050903180542058491058615)
            ·
              refine ⟨7576354770813087736587923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5050903180542058491058615 7576354770813087736587923)
              ·
                refine ⟨11364532156219631604881885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7576354770813087736587923 11364532156219631604881885)
                ·
                  refine ⟨4261699558582361851830707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11364532156219631604881885 4261699558582361851830707)
                  ·
                    refine ⟨6392549337873542777746061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4261699558582361851830707 6392549337873542777746061)
                    ·
                      refine ⟨2397206001702578541654773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6392549337873542777746061 2397206001702578541654773)
                      ·
                        rfl

theorem cell23_4668542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4668542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668542 prefixEnd_4668542 := by exact prefixLift 4668542
  have htrace : WordTrace (prefixWord ++ tailWord_4668542) baseStart_4668542 baseEnd_4668542 := by
    simpa [prefixWord, tailWord_4668542, baseEnd_4668542] using wordTrace_append hprefix tailTrace_4668542
  have hstable : (prefixWord ++ tailWord_4668542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668542).length < 2 ^ (prefixWord ++ tailWord_4668542).sum := by decide
  have hdescent : baseEnd_4668542 < baseStart_4668542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668548 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_4668548 : Nat := 118140960795 + 4668548 * 2 ^ 59
def prefixEnd_4668548 : Nat := 4983230072969 + 3 ^ 40 * 4668548 * 2
def baseEnd_4668548 : Nat := 2397209082586505518179745

theorem tailTrace_4668548 : CollatzResearch.WordTrace tailWord_4668548 prefixEnd_4668548 2397209082586505518179745 := by
  unfold tailWord_4668548
  simp only [CollatzResearch.WordTrace]
  refine ⟨85137967145327697682631149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113517289527103596910174865 85137967145327697682631149)
  ·
    refine ⟨31926737679497886630986681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85137967145327697682631149 31926737679497886630986681)
    ·
      refine ⟨23945053259623414973240011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31926737679497886630986681 23945053259623414973240011)
      ·
        refine ⟨35917579889435122459860017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23945053259623414973240011 35917579889435122459860017)
        ·
          refine ⟨26938184917076341844895013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35917579889435122459860017 26938184917076341844895013)
          ·
            refine ⟨5050909671951814095917815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26938184917076341844895013 5050909671951814095917815)
            ·
              refine ⟨7576364507927721143876723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5050909671951814095917815 7576364507927721143876723)
              ·
                refine ⟨11364546761891581715815085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7576364507927721143876723 11364546761891581715815085)
                ·
                  refine ⟨4261705035709343143430657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11364546761891581715815085 4261705035709343143430657)
                  ·
                    refine ⟨3196278776782007357572993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4261705035709343143430657 3196278776782007357572993)
                    ·
                      refine ⟨2397209082586505518179745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196278776782007357572993 2397209082586505518179745)
                      ·
                        rfl

theorem cell23_4668548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_4668548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668548 prefixEnd_4668548 := by exact prefixLift 4668548
  have htrace : WordTrace (prefixWord ++ tailWord_4668548) baseStart_4668548 baseEnd_4668548 := by
    simpa [prefixWord, tailWord_4668548, baseEnd_4668548] using wordTrace_append hprefix tailTrace_4668548
  have hstable : (prefixWord ++ tailWord_4668548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668548).length < 2 ^ (prefixWord ++ tailWord_4668548).sum := by decide
  have hdescent : baseEnd_4668548 < baseStart_4668548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668558 : List Nat := [4, 1, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_4668558 : Nat := 118140960795 + 4668558 * 2 ^ 59
def prefixEnd_4668558 : Nat := 4983230072969 + 3 ^ 40 * 4668558 * 2
def baseEnd_4668558 : Nat := 799071405797683493018233

theorem tailTrace_4668558 : CollatzResearch.WordTrace tailWord_4668558 prefixEnd_4668558 799071405797683493018233 := by
  unfold tailWord_4668558
  simp only [CollatzResearch.WordTrace]
  refine ⟨21284537377577395884140791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113517532680412778048750885 21284537377577395884140791)
  ·
    refine ⟨31926806066366093826211187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21284537377577395884140791 31926806066366093826211187)
    ·
      refine ⟨47890209099549140739316781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31926806066366093826211187 47890209099549140739316781)
      ·
        refine ⟨17958828412330927777243793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47890209099549140739316781 17958828412330927777243793)
        ·
          refine ⟨13469121309248195832932845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17958828412330927777243793 13469121309248195832932845)
          ·
            refine ⟨5050920490968073437349817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13469121309248195832932845 5050920490968073437349817)
            ·
              refine ⟨3788190368226055078012363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5050920490968073437349817 3788190368226055078012363)
              ·
                refine ⟨5682285552339082617018545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788190368226055078012363 5682285552339082617018545)
                ·
                  refine ⟨4261714164254311962763909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5682285552339082617018545 4261714164254311962763909)
                  ·
                    refine ⟨799071405797683493018233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4261714164254311962763909 799071405797683493018233)
                    ·
                      rfl

theorem cell23_4668558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_4668558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668558 prefixEnd_4668558 := by exact prefixLift 4668558
  have htrace : WordTrace (prefixWord ++ tailWord_4668558) baseStart_4668558 baseEnd_4668558 := by
    simpa [prefixWord, tailWord_4668558, baseEnd_4668558] using wordTrace_append hprefix tailTrace_4668558
  have hstable : (prefixWord ++ tailWord_4668558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668558).length < 2 ^ (prefixWord ++ tailWord_4668558).sum := by decide
  have hdescent : baseEnd_4668558 < baseStart_4668558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668560 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_4668560 : Nat := 118140960795 + 4668560 * 2 ^ 59
def prefixEnd_4668560 : Nat := 4983230072969 + 3 ^ 40 * 4668560 * 2
def baseEnd_4668560 : Nat := 2397215244354359471229689

theorem tailTrace_4668560 : CollatzResearch.WordTrace tailWord_4668560 prefixEnd_4668560 2397215244354359471229689 := by
  unfold tailWord_4668560
  simp only [CollatzResearch.WordTrace]
  refine ⟨85138185983305960707349567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113517581311074614276466089 85138185983305960707349567)
  ·
    refine ⟨127707278974958941061024351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85138185983305960707349567 127707278974958941061024351)
    ·
      refine ⟨191560918462438411591536527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127707278974958941061024351 191560918462438411591536527)
      ·
        refine ⟨287341377693657617387304791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191560918462438411591536527 287341377693657617387304791)
        ·
          refine ⟨431012066540486426080957187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287341377693657617387304791 431012066540486426080957187)
          ·
            refine ⟨646518099810729639121435781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431012066540486426080957187 646518099810729639121435781)
            ·
              refine ⟨121222143714511807335269209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 646518099810729639121435781 121222143714511807335269209)
              ·
                refine ⟨90916607785883855501451907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121222143714511807335269209 90916607785883855501451907)
                ·
                  refine ⟨136374911678825783252177861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90916607785883855501451907 136374911678825783252177861)
                  ·
                    refine ⟨25570295939779834359783349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136374911678825783252177861 25570295939779834359783349)
                    ·
                      refine ⟨2397215244354359471229689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25570295939779834359783349 2397215244354359471229689)
                      ·
                        rfl

theorem cell23_4668560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_4668560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668560 prefixEnd_4668560 := by exact prefixLift 4668560
  have htrace : WordTrace (prefixWord ++ tailWord_4668560) baseStart_4668560 baseEnd_4668560 := by
    simpa [prefixWord, tailWord_4668560, baseEnd_4668560] using wordTrace_append hprefix tailTrace_4668560
  have hstable : (prefixWord ++ tailWord_4668560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668560).length < 2 ^ (prefixWord ++ tailWord_4668560).sum := by decide
  have hdescent : baseEnd_4668560 < baseStart_4668560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668607 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 3]
def baseStart_4668607 : Nat := 118140960795 + 4668607 * 2 ^ 59
def prefixEnd_4668607 : Nat := 4983230072969 + 3 ^ 40 * 4668607 * 2
def baseEnd_4668607 : Nat := 2397239377945120787341973

theorem tailTrace_4668607 : CollatzResearch.WordTrace tailWord_4668607 prefixEnd_4668607 2397239377945120787341973 := by
  unfold tailWord_4668607
  simp only [CollatzResearch.WordTrace]
  refine ⟨170278086197441648441660075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113518724131627765627773383 170278086197441648441660075)
  ·
    refine ⟨255417129296162472662490113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170278086197441648441660075 255417129296162472662490113)
    ·
      refine ⟨191562846972121854496867585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255417129296162472662490113 191562846972121854496867585)
      ·
        refine ⟨143672135229091390872650689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191562846972121854496867585 143672135229091390872650689)
        ·
          refine ⟨107754101421818543154488017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143672135229091390872650689 107754101421818543154488017)
          ·
            refine ⟨80815576066363907365866013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107754101421818543154488017 80815576066363907365866013)
            ·
              refine ⟨30305841024886465262199755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80815576066363907365866013 30305841024886465262199755)
              ·
                refine ⟨45458761537329697893299633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30305841024886465262199755 45458761537329697893299633)
                ·
                  refine ⟨34094071152997273419974725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45458761537329697893299633 34094071152997273419974725)
                  ·
                    refine ⟨6392638341186988766245261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34094071152997273419974725 6392638341186988766245261)
                    ·
                      refine ⟨2397239377945120787341973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6392638341186988766245261 2397239377945120787341973)
                      ·
                        rfl

theorem cell23_4668607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_4668607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668607 prefixEnd_4668607 := by exact prefixLift 4668607
  have htrace : WordTrace (prefixWord ++ tailWord_4668607) baseStart_4668607 baseEnd_4668607 := by
    simpa [prefixWord, tailWord_4668607, baseEnd_4668607] using wordTrace_append hprefix tailTrace_4668607
  have hstable : (prefixWord ++ tailWord_4668607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668607).length < 2 ^ (prefixWord ++ tailWord_4668607).sum := by decide
  have hdescent : baseEnd_4668607 < baseStart_4668607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668644 : List Nat := [2, 3, 1, 1, 1, 2, 3, 5, 5]
def baseStart_4668644 : Nat := 118140960795 + 4668644 * 2 ^ 59
def prefixEnd_4668644 : Nat := 4983230072969 + 3 ^ 40 * 4668644 * 2
def baseEnd_4668644 : Nat := 266362041858815238064367

theorem tailTrace_4668644 : CollatzResearch.WordTrace tailWord_4668644 prefixEnd_4668644 266362041858815238064367 := by
  unfold tailWord_4668644
  simp only [CollatzResearch.WordTrace]
  refine ⟨85139717849153801880378493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113519623798871735840504657 85139717849153801880378493)
  ·
    refine ⟨31927394193432675705141935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85139717849153801880378493 31927394193432675705141935)
    ·
      refine ⟨47891091290149013557712903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31927394193432675705141935 47891091290149013557712903)
      ·
        refine ⟨71836636935223520336569355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47891091290149013557712903 71836636935223520336569355)
        ·
          refine ⟨107754955402835280504854033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71836636935223520336569355 107754955402835280504854033)
          ·
            refine ⟨80816216552126460378640525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107754955402835280504854033 80816216552126460378640525)
            ·
              refine ⟨30306081207047422641990197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80816216552126460378640525 30306081207047422641990197)
              ·
                refine ⟨2841195113160695872686581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30306081207047422641990197 2841195113160695872686581)
                ·
                  refine ⟨266362041858815238064367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2841195113160695872686581 266362041858815238064367)
                  ·
                    rfl

theorem cell23_4668644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_4668644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668644 prefixEnd_4668644 := by exact prefixLift 4668644
  have htrace : WordTrace (prefixWord ++ tailWord_4668644) baseStart_4668644 baseEnd_4668644 := by
    simpa [prefixWord, tailWord_4668644, baseEnd_4668644] using wordTrace_append hprefix tailTrace_4668644
  have hstable : (prefixWord ++ tailWord_4668644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668644).length < 2 ^ (prefixWord ++ tailWord_4668644).sum := by decide
  have hdescent : baseEnd_4668644 < baseStart_4668644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668654 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_4668654 : Nat := 118140960795 + 4668654 * 2 ^ 59
def prefixEnd_4668654 : Nat := 4983230072969 + 3 ^ 40 * 4668654 * 2
def baseEnd_4668654 : Nat := 2397263511535882103454257

theorem tailTrace_4668654 : CollatzResearch.WordTrace tailWord_4668654 prefixEnd_4668654 2397263511535882103454257 := by
  unfold tailWord_4668654
  simp only [CollatzResearch.WordTrace]
  refine ⟨21284975053533921933577627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113519866952180916979080677 21284975053533921933577627)
  ·
    refine ⟨31927462580300882900366441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21284975053533921933577627 31927462580300882900366441)
    ·
      refine ⟨23945596935225662175274831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31927462580300882900366441 23945596935225662175274831)
      ·
        refine ⟨35918395402838493262912247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23945596935225662175274831 35918395402838493262912247)
        ·
          refine ⟨53877593104257739894368371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35918395402838493262912247 53877593104257739894368371)
          ·
            refine ⟨80816389656386609841552557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53877593104257739894368371 80816389656386609841552557)
            ·
              refine ⟨30306146121144978690582209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80816389656386609841552557 30306146121144978690582209)
              ·
                refine ⟨22729609590858734017936657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30306146121144978690582209 22729609590858734017936657)
                ·
                  refine ⟨17047207193144050513452493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22729609590858734017936657 17047207193144050513452493)
                  ·
                    refine ⟨6392702697429018942544685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17047207193144050513452493 6392702697429018942544685)
                    ·
                      refine ⟨2397263511535882103454257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6392702697429018942544685 2397263511535882103454257)
                      ·
                        rfl

theorem cell23_4668654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_4668654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668654 prefixEnd_4668654 := by exact prefixLift 4668654
  have htrace : WordTrace (prefixWord ++ tailWord_4668654) baseStart_4668654 baseEnd_4668654 := by
    simpa [prefixWord, tailWord_4668654, baseEnd_4668654] using wordTrace_append hprefix tailTrace_4668654
  have hstable : (prefixWord ++ tailWord_4668654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668654).length < 2 ^ (prefixWord ++ tailWord_4668654).sum := by decide
  have hdescent : baseEnd_4668654 < baseStart_4668654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668655 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 2, 2, 2]
def baseStart_4668655 : Nat := 118140960795 + 4668655 * 2 ^ 59
def prefixEnd_4668655 : Nat := 4983230072969 + 3 ^ 40 * 4668655 * 2
def baseEnd_4668655 : Nat := 2397264025016536599541753

theorem tailTrace_4668655 : CollatzResearch.WordTrace tailWord_4668655 prefixEnd_4668655 2397264025016536599541753 := by
  unfold tailWord_4668655
  simp only [CollatzResearch.WordTrace]
  refine ⟨170279836901267752639407419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113519891267511835092938279 170279836901267752639407419)
  ·
    refine ⟨255419755351901628959111129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170279836901267752639407419 255419755351901628959111129)
    ·
      refine ⟨191564816513926221719333347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255419755351901628959111129 191564816513926221719333347)
      ·
        refine ⟨287347224770889332579000021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191564816513926221719333347 287347224770889332579000021)
        ·
          refine ⟨6734700580567718732320313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 287347224770889332579000021 6734700580567718732320313)
          ·
            refine ⟨5051025435425789049240235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6734700580567718732320313 5051025435425789049240235)
            ·
              refine ⟨7576538153138683573860353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5051025435425789049240235 7576538153138683573860353)
              ·
                refine ⟨5682403614854012680395265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7576538153138683573860353 5682403614854012680395265)
                ·
                  refine ⟨4261802711140509510296449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5682403614854012680395265 4261802711140509510296449)
                  ·
                    refine ⟨3196352033355382132722337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4261802711140509510296449 3196352033355382132722337)
                    ·
                      refine ⟨2397264025016536599541753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196352033355382132722337 2397264025016536599541753)
                      ·
                        rfl

theorem cell23_4668655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 2, 2].length) (baseStart_4668655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668655 prefixEnd_4668655 := by exact prefixLift 4668655
  have htrace : WordTrace (prefixWord ++ tailWord_4668655) baseStart_4668655 baseEnd_4668655 := by
    simpa [prefixWord, tailWord_4668655, baseEnd_4668655] using wordTrace_append hprefix tailTrace_4668655
  have hstable : (prefixWord ++ tailWord_4668655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668655).length < 2 ^ (prefixWord ++ tailWord_4668655).sum := by decide
  have hdescent : baseEnd_4668655 < baseStart_4668655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668657 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 4, 5]
def baseStart_4668657 : Nat := 118140960795 + 4668657 * 2 ^ 59
def prefixEnd_4668657 : Nat := 4983230072969 + 3 ^ 40 * 4668657 * 2
def baseEnd_4668657 : Nat := 799088350659281863905581

theorem tailTrace_4668657 : CollatzResearch.WordTrace tailWord_4668657 prefixEnd_4668657 799088350659281863905581 := by
  unfold tailWord_4668657
  simp only [CollatzResearch.WordTrace]
  refine ⟨170279909847260506980980225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113519939898173671320653483 170279909847260506980980225)
  ·
    refine ⟨127709932385445380235735169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170279909847260506980980225 127709932385445380235735169)
    ·
      refine ⟨95782449289084035176801377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127709932385445380235735169 95782449289084035176801377)
      ·
        refine ⟨71836836966813026382601033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95782449289084035176801377 71836836966813026382601033)
        ·
          refine ⟨53877627725109769786950775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71836836966813026382601033 53877627725109769786950775)
          ·
            refine ⟨80816441587664654680426163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53877627725109769786950775 80816441587664654680426163)
            ·
              refine ⟨121224662381496982020639245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80816441587664654680426163 121224662381496982020639245)
              ·
                refine ⟨45459248393061368257739717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121224662381496982020639245 45459248393061368257739717)
                ·
                  refine ⟨8523609073699006548326197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45459248393061368257739717 8523609073699006548326197)
                  ·
                    refine ⟨799088350659281863905581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8523609073699006548326197 799088350659281863905581)
                    ·
                      rfl

theorem cell23_4668657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_4668657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668657 prefixEnd_4668657 := by exact prefixLift 4668657
  have htrace : WordTrace (prefixWord ++ tailWord_4668657) baseStart_4668657 baseEnd_4668657 := by
    simpa [prefixWord, tailWord_4668657, baseEnd_4668657] using wordTrace_append hprefix tailTrace_4668657
  have hstable : (prefixWord ++ tailWord_4668657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668657).length < 2 ^ (prefixWord ++ tailWord_4668657).sum := by decide
  have hdescent : baseEnd_4668657 < baseStart_4668657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668677 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_4668677 : Nat := 118140960795 + 4668677 * 2 ^ 59
def prefixEnd_4668677 : Nat := 4983230072969 + 3 ^ 40 * 4668677 * 2
def baseEnd_4668677 : Nat := 2397275321590935513466651

theorem tailTrace_4668677 : CollatzResearch.WordTrace tailWord_4668677 prefixEnd_4668677 2397275321590935513466651 := by
  unfold tailWord_4668677
  simp only [CollatzResearch.WordTrace]
  refine ⟨170280639307188050396708285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113520426204792033597805523 170280639307188050396708285)
  ·
    refine ⟨63855239740195518898765607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170280639307188050396708285 63855239740195518898765607)
    ·
      refine ⟨95782859610293278348148411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63855239740195518898765607 95782859610293278348148411)
      ·
        refine ⟨143674289415439917522222617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95782859610293278348148411 143674289415439917522222617)
        ·
          refine ⟨107755717061579938141666963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143674289415439917522222617 107755717061579938141666963)
          ·
            refine ⟨161633575592369907212500445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107755717061579938141666963 161633575592369907212500445)
            ·
              refine ⟨60612590847138715204687667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161633575592369907212500445 60612590847138715204687667)
              ·
                refine ⟨90918886270708072807031501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60612590847138715204687667 90918886270708072807031501)
                ·
                  refine ⟨34094582351515527302636813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90918886270708072807031501 34094582351515527302636813)
                  ·
                    refine ⟨12785468381818322738488805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34094582351515527302636813 12785468381818322738488805)
                    ·
                      refine ⟨2397275321590935513466651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12785468381818322738488805 2397275321590935513466651)
                      ·
                        rfl

theorem cell23_4668677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_4668677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668677 prefixEnd_4668677 := by exact prefixLift 4668677
  have htrace : WordTrace (prefixWord ++ tailWord_4668677) baseStart_4668677 baseEnd_4668677 := by
    simpa [prefixWord, tailWord_4668677, baseEnd_4668677] using wordTrace_append hprefix tailTrace_4668677
  have hstable : (prefixWord ++ tailWord_4668677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668677).length < 2 ^ (prefixWord ++ tailWord_4668677).sum := by decide
  have hdescent : baseEnd_4668677 < baseStart_4668677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668721 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 3, 4]
def baseStart_4668721 : Nat := 118140960795 + 4668721 * 2 ^ 59
def prefixEnd_4668721 : Nat := 4983230072969 + 3 ^ 40 * 4668721 * 2
def baseEnd_4668721 : Nat := 799099304913244447105483

theorem tailTrace_4668721 : CollatzResearch.WordTrace tailWord_4668721 prefixEnd_4668721 799099304913244447105483 := by
  unfold tailWord_4668721
  simp only [CollatzResearch.WordTrace]
  refine ⟨170282244119028645911310017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113521496079352430607540011 170282244119028645911310017)
  ·
    refine ⟨127711683089271484433482513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170282244119028645911310017 127711683089271484433482513)
    ·
      refine ⟨95783762316953613325111885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127711683089271484433482513 95783762316953613325111885)
      ·
        refine ⟨35918910868857604996916957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95783762316953613325111885 35918910868857604996916957)
        ·
          refine ⟨13469591575821601873843859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35918910868857604996916957 13469591575821601873843859)
          ·
            refine ⟨20204387363732402810765789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13469591575821601873843859 20204387363732402810765789)
            ·
              refine ⟨7576645261399651054037171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20204387363732402810765789 7576645261399651054037171)
              ·
                refine ⟨11364967892099476581055757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7576645261399651054037171 11364967892099476581055757)
                ·
                  refine ⟨4261862959537303717895909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11364967892099476581055757 4261862959537303717895909)
                  ·
                    refine ⟨799099304913244447105483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4261862959537303717895909 799099304913244447105483)
                    ·
                      rfl

theorem cell23_4668721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_4668721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668721 prefixEnd_4668721 := by exact prefixLift 4668721
  have htrace : WordTrace (prefixWord ++ tailWord_4668721) baseStart_4668721 baseEnd_4668721 := by
    simpa [prefixWord, tailWord_4668721, baseEnd_4668721] using wordTrace_append hprefix tailTrace_4668721
  have hstable : (prefixWord ++ tailWord_4668721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668721).length < 2 ^ (prefixWord ++ tailWord_4668721).sum := by decide
  have hdescent : baseEnd_4668721 < baseStart_4668721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668784 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 4]
def baseStart_4668784 : Nat := 118140960795 + 4668784 * 2 ^ 59
def prefixEnd_4668784 : Nat := 4983230072969 + 3 ^ 40 * 4668784 * 2
def baseEnd_4668784 : Nat := 2397330264020966594828659

theorem tailTrace_4668784 : CollatzResearch.WordTrace tailWord_4668784 prefixEnd_4668784 2397330264020966594828659 := by
  unfold tailWord_4668784
  simp only [CollatzResearch.WordTrace]
  refine ⟨85142270958900203835426703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113523027945200271780568937 85142270958900203835426703)
  ·
    refine ⟨127713406438350305753140055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85142270958900203835426703 127713406438350305753140055)
    ·
      refine ⟨191570109657525458629710083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127713406438350305753140055 191570109657525458629710083)
      ·
        refine ⟨287355164486288187944565125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191570109657525458629710083 287355164486288187944565125)
        ·
          refine ⟨53879093341179035239605961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 287355164486288187944565125 53879093341179035239605961)
          ·
            refine ⟨40409320005884276429704471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53879093341179035239605961 40409320005884276429704471)
            ·
              refine ⟨60613980008826414644556707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40409320005884276429704471 60613980008826414644556707)
              ·
                refine ⟨90920970013239621966835061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60613980008826414644556707 90920970013239621966835061)
                ·
                  refine ⟨8523840938741214559390787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90920970013239621966835061 8523840938741214559390787)
                  ·
                    refine ⟨12785761408111821839086181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8523840938741214559390787 12785761408111821839086181)
                    ·
                      refine ⟨2397330264020966594828659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12785761408111821839086181 2397330264020966594828659)
                      ·
                        rfl

theorem cell23_4668784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_4668784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668784 prefixEnd_4668784 := by exact prefixLift 4668784
  have htrace : WordTrace (prefixWord ++ tailWord_4668784) baseStart_4668784 baseEnd_4668784 := by
    simpa [prefixWord, tailWord_4668784, baseEnd_4668784] using wordTrace_append hprefix tailTrace_4668784
  have hstable : (prefixWord ++ tailWord_4668784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668784).length < 2 ^ (prefixWord ++ tailWord_4668784).sum := by decide
  have hdescent : baseEnd_4668784 < baseStart_4668784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668835 : List Nat := [1, 1, 1, 4, 1, 3, 1, 6, 1, 2, 2]
def baseStart_4668835 : Nat := 118140960795 + 4668835 * 2 ^ 59
def prefixEnd_4668835 : Nat := 4983230072969 + 3 ^ 40 * 4668835 * 2
def baseEnd_4668835 : Nat := 2397356451534345895290925

theorem tailTrace_4668835 : CollatzResearch.WordTrace tailWord_4668835 prefixEnd_4668835 2397356451534345895290925 := by
  unfold tailWord_4668835
  simp only [CollatzResearch.WordTrace]
  refine ⟨170286402040615643380959959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113524268027077095587306639 170286402040615643380959959)
  ·
    refine ⟨255429603060923465071439939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170286402040615643380959959 255429603060923465071439939)
    ·
      refine ⟨383144404591385197607159909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255429603060923465071439939 383144404591385197607159909)
      ·
        refine ⟨71839575860884724551342483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 383144404591385197607159909 71839575860884724551342483)
        ·
          refine ⟨107759363791327086827013725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71839575860884724551342483 107759363791327086827013725)
          ·
            refine ⟨40409761421747657560130147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107759363791327086827013725 40409761421747657560130147)
            ·
              refine ⟨60614642132621486340195221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40409761421747657560130147 60614642132621486340195221)
              ·
                refine ⟨2841311349966632172196651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60614642132621486340195221 2841311349966632172196651)
                ·
                  refine ⟨4261967024949948258294977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841311349966632172196651 4261967024949948258294977)
                  ·
                    refine ⟨3196475268712461193721233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4261967024949948258294977 3196475268712461193721233)
                    ·
                      refine ⟨2397356451534345895290925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196475268712461193721233 2397356451534345895290925)
                      ·
                        rfl

theorem cell23_4668835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_4668835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668835 prefixEnd_4668835 := by exact prefixLift 4668835
  have htrace : WordTrace (prefixWord ++ tailWord_4668835) baseStart_4668835 baseEnd_4668835 := by
    simpa [prefixWord, tailWord_4668835, baseEnd_4668835] using wordTrace_append hprefix tailTrace_4668835
  have hstable : (prefixWord ++ tailWord_4668835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668835).length < 2 ^ (prefixWord ++ tailWord_4668835).sum := by decide
  have hdescent : baseEnd_4668835 < baseStart_4668835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668864 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_4668864 : Nat := 118140960795 + 4668864 * 2 ^ 59
def prefixEnd_4668864 : Nat := 4983230072969 + 3 ^ 40 * 4668864 * 2
def baseEnd_4668864 : Nat := 2397371342473326281828291

theorem tailTrace_4668864 : CollatzResearch.WordTrace tailWord_4668864 prefixEnd_4668864 2397371342473326281828291 := by
  unfold tailWord_4668864
  simp only [CollatzResearch.WordTrace]
  refine ⟨85143729878755290666882823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113524973171673720889177097 85143729878755290666882823)
  ·
    refine ⟨127715594818132936000324235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85143729878755290666882823 127715594818132936000324235)
    ·
      refine ⟨191573392227199404000486353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127715594818132936000324235 191573392227199404000486353)
      ·
        refine ⟨143680044170399553000364765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191573392227199404000486353 143680044170399553000364765)
        ·
          refine ⟨53880016563899832375136787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143680044170399553000364765 53880016563899832375136787)
          ·
            refine ⟨80820024845849748562705181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53880016563899832375136787 80820024845849748562705181)
            ·
              refine ⟨30307509317193655711014443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80820024845849748562705181 30307509317193655711014443)
              ·
                refine ⟨45461263975790483566521665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30307509317193655711014443 45461263975790483566521665)
                ·
                  refine ⟨34095947981842862674891249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45461263975790483566521665 34095947981842862674891249)
                  ·
                    refine ⟨25571960986382147006168437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34095947981842862674891249 25571960986382147006168437)
                    ·
                      refine ⟨2397371342473326281828291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25571960986382147006168437 2397371342473326281828291)
                      ·
                        rfl

theorem cell23_4668864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_4668864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668864 prefixEnd_4668864 := by exact prefixLift 4668864
  have htrace : WordTrace (prefixWord ++ tailWord_4668864) baseStart_4668864 baseEnd_4668864 := by
    simpa [prefixWord, tailWord_4668864, baseEnd_4668864] using wordTrace_append hprefix tailTrace_4668864
  have hstable : (prefixWord ++ tailWord_4668864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668864).length < 2 ^ (prefixWord ++ tailWord_4668864).sum := by decide
  have hdescent : baseEnd_4668864 < baseStart_4668864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668886 : List Nat := [5, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_4668886 : Nat := 118140960795 + 4668886 * 2 ^ 59
def prefixEnd_4668886 : Nat := 4983230072969 + 3 ^ 40 * 4668886 * 2
def baseEnd_4668886 : Nat := 2397382639047725195753191

theorem tailTrace_4668886 : CollatzResearch.WordTrace tailWord_4668886 prefixEnd_4668886 2397382639047725195753191 := by
  unfold tailWord_4668886
  simp only [CollatzResearch.WordTrace]
  refine ⟨10643016385214429943191657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113525508108953919394044341 10643016385214429943191657)
  ·
    refine ⟨7982262288910822457393743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10643016385214429943191657 7982262288910822457393743)
    ·
      refine ⟨11973393433366233686090615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7982262288910822457393743 11973393433366233686090615)
      ·
        refine ⟨17960090150049350529135923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11973393433366233686090615 17960090150049350529135923)
        ·
          refine ⟨26940135225074025793703885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17960090150049350529135923 26940135225074025793703885)
          ·
            refine ⟨10102550709402759672638957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26940135225074025793703885 10102550709402759672638957)
            ·
              refine ⟨3788456516026034877239609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10102550709402759672638957 3788456516026034877239609)
              ·
                refine ⟨2841342387019526157929707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3788456516026034877239609 2841342387019526157929707)
                ·
                  refine ⟨4262013580529289236894561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841342387019526157929707 4262013580529289236894561)
                  ·
                    refine ⟨3196510185396966927670921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4262013580529289236894561 3196510185396966927670921)
                    ·
                      refine ⟨2397382639047725195753191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196510185396966927670921 2397382639047725195753191)
                      ·
                        rfl

theorem cell23_4668886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_4668886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668886 prefixEnd_4668886 := by exact prefixLift 4668886
  have htrace : WordTrace (prefixWord ++ tailWord_4668886) baseStart_4668886 baseEnd_4668886 := by
    simpa [prefixWord, tailWord_4668886, baseEnd_4668886] using wordTrace_append hprefix tailTrace_4668886
  have hstable : (prefixWord ++ tailWord_4668886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668886).length < 2 ^ (prefixWord ++ tailWord_4668886).sum := by decide
  have hdescent : baseEnd_4668886 < baseStart_4668886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668908 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 6, 2, 2]
def baseStart_4668908 : Nat := 118140960795 + 4668908 * 2 ^ 59
def prefixEnd_4668908 : Nat := 4983230072969 + 3 ^ 40 * 4668908 * 2
def baseEnd_4668908 : Nat := 2397393935622124109678089

theorem tailTrace_4668908 : CollatzResearch.WordTrace tailWord_4668908 prefixEnd_4668908 2397393935622124109678089 := by
  unfold tailWord_4668908
  simp only [CollatzResearch.WordTrace]
  refine ⟨85144532284675588424183689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113526043046234117898911585 85144532284675588424183689)
  ·
    refine ⟨63858399213506691318137767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85144532284675588424183689 63858399213506691318137767)
    ·
      refine ⟨95787598820260036977206651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63858399213506691318137767 95787598820260036977206651)
      ·
        refine ⟨143681398230390055465809977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95787598820260036977206651 143681398230390055465809977)
        ·
          refine ⟨107761048672792541599357483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143681398230390055465809977 107761048672792541599357483)
          ·
            refine ⟨161641573009188812399036225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107761048672792541599357483 161641573009188812399036225)
            ·
              refine ⟨121231179756891609299277169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161641573009188812399036225 121231179756891609299277169)
              ·
                refine ⟨90923384817668706974457877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121231179756891609299277169 90923384817668706974457877)
                ·
                  refine ⟨4262033663328220639427713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90923384817668706974457877 4262033663328220639427713)
                  ·
                    refine ⟨3196525247496165479570785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4262033663328220639427713 3196525247496165479570785)
                    ·
                      refine ⟨2397393935622124109678089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196525247496165479570785 2397393935622124109678089)
                      ·
                        rfl

theorem cell23_4668908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 2, 2].length) (baseStart_4668908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668908 prefixEnd_4668908 := by exact prefixLift 4668908
  have htrace : WordTrace (prefixWord ++ tailWord_4668908) baseStart_4668908 baseEnd_4668908 := by
    simpa [prefixWord, tailWord_4668908, baseEnd_4668908] using wordTrace_append hprefix tailTrace_4668908
  have hstable : (prefixWord ++ tailWord_4668908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668908).length < 2 ^ (prefixWord ++ tailWord_4668908).sum := by decide
  have hdescent : baseEnd_4668908 < baseStart_4668908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4668982 : List Nat := [5, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_4668982 : Nat := 118140960795 + 4668982 * 2 ^ 59
def prefixEnd_4668982 : Nat := 4983230072969 + 3 ^ 40 * 4668982 * 2
def baseEnd_4668982 : Nat := 266381325910061868905861

theorem tailTrace_4668982 : CollatzResearch.WordTrace tailWord_4668982 prefixEnd_4668982 266381325910061868905861 := by
  unfold tailWord_4668982
  simp only [CollatzResearch.WordTrace]
  refine ⟨10643235223192692967910075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113527842380722058324374133 10643235223192692967910075)
  ·
    refine ⟨15964852834789039451865113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10643235223192692967910075 15964852834789039451865113)
    ·
      refine ⟨11973639626091779588898835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15964852834789039451865113 11973639626091779588898835)
      ·
        refine ⟨17960459439137669383348253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11973639626091779588898835 17960459439137669383348253)
        ·
          refine ⟨6735172289676626018755595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17960459439137669383348253 6735172289676626018755595)
          ·
            refine ⟨10102758434514939028133393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6735172289676626018755595 10102758434514939028133393)
            ·
              refine ⟨7577068825886204271100045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10102758434514939028133393 7577068825886204271100045)
              ·
                refine ⟨2841400809707326601662517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7577068825886204271100045 2841400809707326601662517)
                ·
                  refine ⟨266381325910061868905861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2841400809707326601662517 266381325910061868905861)
                  ·
                    rfl

theorem cell23_4668982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_4668982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4668982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4668982 prefixEnd_4668982 := by exact prefixLift 4668982
  have htrace : WordTrace (prefixWord ++ tailWord_4668982) baseStart_4668982 baseEnd_4668982 := by
    simpa [prefixWord, tailWord_4668982, baseEnd_4668982] using wordTrace_append hprefix tailTrace_4668982
  have hstable : (prefixWord ++ tailWord_4668982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4668982).length < 2 ^ (prefixWord ++ tailWord_4668982).sum := by decide
  have hdescent : baseEnd_4668982 < baseStart_4668982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4668982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669008 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 3, 4]
def baseStart_4669008 : Nat := 118140960795 + 4669008 * 2 ^ 59
def prefixEnd_4669008 : Nat := 4983230072969 + 3 ^ 40 * 4669008 * 2
def baseEnd_4669008 : Nat := 799148427895857906142543

theorem tailTrace_4669008 : CollatzResearch.WordTrace tailWord_4669008 prefixEnd_4669008 799148427895857906142543 := by
  unfold tailWord_4669008
  simp only [CollatzResearch.WordTrace]
  refine ⟨85146355934494446963503839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113528474579325929284671785 85146355934494446963503839)
  ·
    refine ⟨127719533901741670445255759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85146355934494446963503839 127719533901741670445255759)
    ·
      refine ⟨191579300852612505667883639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127719533901741670445255759 191579300852612505667883639)
      ·
        refine ⟨287368951278918758501825459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191579300852612505667883639 287368951278918758501825459)
        ·
          refine ⟨431053426918378137752738189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287368951278918758501825459 431053426918378137752738189)
          ·
            refine ⟨161645035094391801657276821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 431053426918378137752738189 161645035094391801657276821)
            ·
              refine ⟨7577111020049615702684851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 161645035094391801657276821 7577111020049615702684851)
              ·
                refine ⟨11365666530074423554027277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7577111020049615702684851 11365666530074423554027277)
                ·
                  refine ⟨4262124948777908832760229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11365666530074423554027277 4262124948777908832760229)
                  ·
                    refine ⟨799148427895857906142543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4262124948777908832760229 799148427895857906142543)
                    ·
                      rfl

theorem cell23_4669008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3, 4].length) (baseStart_4669008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669008 prefixEnd_4669008 := by exact prefixLift 4669008
  have htrace : WordTrace (prefixWord ++ tailWord_4669008) baseStart_4669008 baseEnd_4669008 := by
    simpa [prefixWord, tailWord_4669008, baseEnd_4669008] using wordTrace_append hprefix tailTrace_4669008
  have hstable : (prefixWord ++ tailWord_4669008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669008).length < 2 ^ (prefixWord ++ tailWord_4669008).sum := by decide
  have hdescent : baseEnd_4669008 < baseStart_4669008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669042 : List Nat := [3, 2, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_4669042 : Nat := 118140960795 + 4669042 * 2 ^ 59
def prefixEnd_4669042 : Nat := 4983230072969 + 3 ^ 40 * 4669042 * 2
def baseEnd_4669042 : Nat := 799154247343275528467491

theorem tailTrace_4669042 : CollatzResearch.WordTrace tailWord_4669042 prefixEnd_4669042 799154247343275528467491 := by
  unfold tailWord_4669042
  simp only [CollatzResearch.WordTrace]
  refine ⟨42573487987716429433436345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113529301300577145155830253 42573487987716429433436345)
  ·
    refine ⟨31930115990787322075077259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42573487987716429433436345 31930115990787322075077259)
    ·
      refine ⟨47895173986180983112615889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31930115990787322075077259 47895173986180983112615889)
      ·
        refine ⟨35921380489635737334461917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47895173986180983112615889 35921380489635737334461917)
        ·
          refine ⟨13470517683613401500423219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35921380489635737334461917 13470517683613401500423219)
          ·
            refine ⟨20205776525420102250634829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13470517683613401500423219 20205776525420102250634829)
            ·
              refine ⟨7577166197032538343988061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20205776525420102250634829 7577166197032538343988061)
              ·
                refine ⟨2841437323887201878995523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7577166197032538343988061 2841437323887201878995523)
                ·
                  refine ⟨4262155985830802818493285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841437323887201878995523 4262155985830802818493285)
                  ·
                    refine ⟨799154247343275528467491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4262155985830802818493285 799154247343275528467491)
                    ·
                      rfl

theorem cell23_4669042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_4669042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669042 prefixEnd_4669042 := by exact prefixLift 4669042
  have htrace : WordTrace (prefixWord ++ tailWord_4669042) baseStart_4669042 baseEnd_4669042 := by
    simpa [prefixWord, tailWord_4669042, baseEnd_4669042] using wordTrace_append hprefix tailTrace_4669042
  have hstable : (prefixWord ++ tailWord_4669042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669042).length < 2 ^ (prefixWord ++ tailWord_4669042).sum := by decide
  have hdescent : baseEnd_4669042 < baseStart_4669042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669065 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 3, 1, 3]
def baseStart_4669065 : Nat := 118140960795 + 4669065 * 2 ^ 59
def prefixEnd_4669065 : Nat := 4983230072969 + 3 ^ 40 * 4669065 * 2
def baseEnd_4669065 : Nat := 2397474552084879995414867

theorem tailTrace_4669065 : CollatzResearch.WordTrace tailWord_4669065 prefixEnd_4669065 2397474552084879995414867 := by
  unfold tailWord_4669065
  simp only [CollatzResearch.WordTrace]
  refine ⟨170294790829782392661832649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113529860553188261774555099 170294790829782392661832649)
  ·
    refine ⟨127721093122336794496374487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170294790829782392661832649 127721093122336794496374487)
    ·
      refine ⟨191581639683505191744561731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127721093122336794496374487 191581639683505191744561731)
      ·
        refine ⟨287372459525257787616842597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191581639683505191744561731 287372459525257787616842597)
        ·
          refine ⟨53882336160985835178157987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 287372459525257787616842597 53882336160985835178157987)
          ·
            refine ⟨80823504241478752767236981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53882336160985835178157987 80823504241478752767236981)
            ·
              refine ⟨7577203522638633071928467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80823504241478752767236981 7577203522638633071928467)
              ·
                refine ⟨11365805283957949607892701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7577203522638633071928467 11365805283957949607892701)
                ·
                  refine ⟨4262176981484231102959763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11365805283957949607892701 4262176981484231102959763)
                  ·
                    refine ⟨6393265472226346654439645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4262176981484231102959763 6393265472226346654439645)
                    ·
                      refine ⟨2397474552084879995414867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6393265472226346654439645 2397474552084879995414867)
                      ·
                        rfl

theorem cell23_4669065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 1, 3].length) (baseStart_4669065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669065 prefixEnd_4669065 := by exact prefixLift 4669065
  have htrace : WordTrace (prefixWord ++ tailWord_4669065) baseStart_4669065 baseEnd_4669065 := by
    simpa [prefixWord, tailWord_4669065, baseEnd_4669065] using wordTrace_append hprefix tailTrace_4669065
  have hstable : (prefixWord ++ tailWord_4669065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669065).length < 2 ^ (prefixWord ++ tailWord_4669065).sum := by decide
  have hdescent : baseEnd_4669065 < baseStart_4669065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669092 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 2, 3, 2]
def baseStart_4669092 : Nat := 118140960795 + 4669092 * 2 ^ 59
def prefixEnd_4669092 : Nat := 4983230072969 + 3 ^ 40 * 4669092 * 2
def baseEnd_4669092 : Nat := 2397488416062551389777243

theorem tailTrace_4669092 : CollatzResearch.WordTrace tailWord_4669092 prefixEnd_4669092 2397488416062551389777243 := by
  unfold tailWord_4669092
  simp only [CollatzResearch.WordTrace]
  refine ⟨85147887800342288136532765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113530517067123050848710353 85147887800342288136532765)
  ·
    refine ⟨31930457925128358051199787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85147887800342288136532765 31930457925128358051199787)
    ·
      refine ⟨47895686887692537076799681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31930457925128358051199787 47895686887692537076799681)
      ·
        refine ⟨35921765165769402807599761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47895686887692537076799681 35921765165769402807599761)
        ·
          refine ⟨26941323874327052105699821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35921765165769402807599761 26941323874327052105699821)
          ·
            refine ⟨10102996452872644539637433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26941323874327052105699821 10102996452872644539637433)
            ·
              refine ⟨7577247339654483404728075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10102996452872644539637433 7577247339654483404728075)
              ·
                refine ⟨11365871009481725107092113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7577247339654483404728075 11365871009481725107092113)
                ·
                  refine ⟨8524403257111293830319085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11365871009481725107092113 8524403257111293830319085)
                  ·
                    refine ⟨3196651221416735186369657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8524403257111293830319085 3196651221416735186369657)
                    ·
                      refine ⟨2397488416062551389777243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196651221416735186369657 2397488416062551389777243)
                      ·
                        rfl

theorem cell23_4669092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_4669092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669092 prefixEnd_4669092 := by exact prefixLift 4669092
  have htrace : WordTrace (prefixWord ++ tailWord_4669092) baseStart_4669092 baseEnd_4669092 := by
    simpa [prefixWord, tailWord_4669092, baseEnd_4669092] using wordTrace_append hprefix tailTrace_4669092
  have hstable : (prefixWord ++ tailWord_4669092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669092).length < 2 ^ (prefixWord ++ tailWord_4669092).sum := by decide
  have hdescent : baseEnd_4669092 < baseStart_4669092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669111 : List Nat := [1, 1, 3, 1, 5, 12]
def baseStart_4669111 : Nat := 118140960795 + 4669111 * 2 ^ 59
def prefixEnd_4669111 : Nat := 4983230072969 + 3 ^ 40 * 4669111 * 2
def baseEnd_4669111 : Nat := 9866247622201591833085

theorem tailTrace_4669111 : CollatzResearch.WordTrace tailWord_4669111 prefixEnd_4669111 9866247622201591833085 := by
  unfold tailWord_4669111
  simp only [CollatzResearch.WordTrace]
  refine ⟨170296468587615742518007187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113530979058410495012004791 170296468587615742518007187)
  ·
    refine ⟨255444702881423613777010781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170296468587615742518007187 255444702881423613777010781)
    ·
      refine ⟨95791763580533855166379043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255444702881423613777010781 95791763580533855166379043)
      ·
        refine ⟨143687645370800782749568565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95791763580533855166379043 143687645370800782749568565)
        ·
          refine ⟨13470716753512573382772053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143687645370800782749568565 13470716753512573382772053)
          ·
            refine ⟨9866247622201591833085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13470716753512573382772053 9866247622201591833085)
            ·
              rfl

theorem cell23_4669111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 12].length) (baseStart_4669111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669111 prefixEnd_4669111 := by exact prefixLift 4669111
  have htrace : WordTrace (prefixWord ++ tailWord_4669111) baseStart_4669111 baseEnd_4669111 := by
    simpa [prefixWord, tailWord_4669111, baseEnd_4669111] using wordTrace_append hprefix tailTrace_4669111
  have hstable : (prefixWord ++ tailWord_4669111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669111).length < 2 ^ (prefixWord ++ tailWord_4669111).sum := by decide
  have hdescent : baseEnd_4669111 < baseStart_4669111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669116 : List Nat := [2, 2, 2, 3, 1, 4, 2, 2, 1, 1, 3]
def baseStart_4669116 : Nat := 118140960795 + 4669116 * 2 ^ 59
def prefixEnd_4669116 : Nat := 4983230072969 + 3 ^ 40 * 4669116 * 2
def baseEnd_4669116 : Nat := 2397500739598259295877133

theorem tailTrace_4669116 : CollatzResearch.WordTrace tailWord_4669116 prefixEnd_4669116 2397500739598259295877133 := by
  unfold tailWord_4669116
  simp only [CollatzResearch.WordTrace]
  refine ⟨85148325476298814185969601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113531100635065085581292801 85148325476298814185969601)
  ·
    refine ⟨63861244107224110639477201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85148325476298814185969601 63861244107224110639477201)
    ·
      refine ⟨47895933080418082979607901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63861244107224110639477201 47895933080418082979607901)
      ·
        refine ⟨17960974905156781117352963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47895933080418082979607901 17960974905156781117352963)
        ·
          refine ⟨26941462357735171676029445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17960974905156781117352963 26941462357735171676029445)
          ·
            refine ⟨5051524192075344689255521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26941462357735171676029445 5051524192075344689255521)
            ·
              refine ⟨3788643144056508516941641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5051524192075344689255521 3788643144056508516941641)
              ·
                refine ⟨2841482358042381387706231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3788643144056508516941641 2841482358042381387706231)
                ·
                  refine ⟨4262223537063572081559347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841482358042381387706231 4262223537063572081559347)
                  ·
                    refine ⟨6393335305595358122339021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4262223537063572081559347 6393335305595358122339021)
                    ·
                      refine ⟨2397500739598259295877133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6393335305595358122339021 2397500739598259295877133)
                      ·
                        rfl

theorem cell23_4669116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_4669116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669116 prefixEnd_4669116 := by exact prefixLift 4669116
  have htrace : WordTrace (prefixWord ++ tailWord_4669116) baseStart_4669116 baseEnd_4669116 := by
    simpa [prefixWord, tailWord_4669116, baseEnd_4669116] using wordTrace_append hprefix tailTrace_4669116
  have hstable : (prefixWord ++ tailWord_4669116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669116).length < 2 ^ (prefixWord ++ tailWord_4669116).sum := by decide
  have hdescent : baseEnd_4669116 < baseStart_4669116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669131 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 6]
def baseStart_4669131 : Nat := 118140960795 + 4669131 * 2 ^ 59
def prefixEnd_4669131 : Nat := 4983230072969 + 3 ^ 40 * 4669131 * 2
def baseEnd_4669131 : Nat := 2397508441808076737189563

theorem tailTrace_4669131 : CollatzResearch.WordTrace tailWord_4669131 prefixEnd_4669131 2397508441808076737189563 := by
  unfold tailWord_4669131
  simp only [CollatzResearch.WordTrace]
  refine ⟨170297198047543285933735247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113531465365028857289156831 170297198047543285933735247)
  ·
    refine ⟨255445797071314928900602871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170297198047543285933735247 255445797071314928900602871)
    ·
      refine ⟨383168695606972393350904307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255445797071314928900602871 383168695606972393350904307)
      ·
        refine ⟨574753043410458590026356461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383168695606972393350904307 574753043410458590026356461)
        ·
          refine ⟨215532391278921971259883673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 574753043410458590026356461 215532391278921971259883673)
          ·
            refine ⟨161649293459191478444912755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215532391278921971259883673 161649293459191478444912755)
            ·
              refine ⟨242473940188787217667369133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161649293459191478444912755 242473940188787217667369133)
              ·
                refine ⟨90927727570795206625263425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242473940188787217667369133 90927727570795206625263425)
                ·
                  refine ⟨68195795678096404968947569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90927727570795206625263425 68195795678096404968947569)
                  ·
                    refine ⟨51146846758572303726710677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68195795678096404968947569 51146846758572303726710677)
                    ·
                      refine ⟨2397508441808076737189563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51146846758572303726710677 2397508441808076737189563)
                      ·
                        rfl

theorem cell23_4669131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_4669131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669131 prefixEnd_4669131 := by exact prefixLift 4669131
  have htrace : WordTrace (prefixWord ++ tailWord_4669131) baseStart_4669131 baseEnd_4669131 := by
    simpa [prefixWord, tailWord_4669131, baseEnd_4669131] using wordTrace_append hprefix tailTrace_4669131
  have hstable : (prefixWord ++ tailWord_4669131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669131).length < 2 ^ (prefixWord ++ tailWord_4669131).sum := by decide
  have hdescent : baseEnd_4669131 < baseStart_4669131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669159 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4669159 : Nat := 118140960795 + 4669159 * 2 ^ 59
def prefixEnd_4669159 : Nat := 4983230072969 + 3 ^ 40 * 4669159 * 2
def baseEnd_4669159 : Nat := 2397522819266402627639435

theorem tailTrace_4669159 : CollatzResearch.WordTrace tailWord_4669159 prefixEnd_4669159 2397522819266402627639435 := by
  unfold tailWord_4669159
  simp only [CollatzResearch.WordTrace]
  refine ⟨170298219291441846715754531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113532146194294564477169687 170298219291441846715754531)
  ·
    refine ⟨255447328937162770073631797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170298219291441846715754531 255447328937162770073631797)
    ·
      refine ⟨23948187087859009694402981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 255447328937162770073631797 23948187087859009694402981)
      ·
        refine ⟨4490285078973564317700559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23948187087859009694402981 4490285078973564317700559)
        ·
          refine ⟨6735427618460346476550839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4490285078973564317700559 6735427618460346476550839)
          ·
            refine ⟨10103141427690519714826259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6735427618460346476550839 10103141427690519714826259)
            ·
              refine ⟨15154712141535779572239389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10103141427690519714826259 15154712141535779572239389)
              ·
                refine ⟨5683017053075917339589771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15154712141535779572239389 5683017053075917339589771)
                ·
                  refine ⟨8524525579613876009384657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5683017053075917339589771 8524525579613876009384657)
                  ·
                    refine ⟨6393394184710407007038493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8524525579613876009384657 6393394184710407007038493)
                    ·
                      refine ⟨2397522819266402627639435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6393394184710407007038493 2397522819266402627639435)
                      ·
                        rfl

theorem cell23_4669159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4669159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669159 prefixEnd_4669159 := by exact prefixLift 4669159
  have htrace : WordTrace (prefixWord ++ tailWord_4669159) baseStart_4669159 baseEnd_4669159 := by
    simpa [prefixWord, tailWord_4669159, baseEnd_4669159] using wordTrace_append hprefix tailTrace_4669159
  have hstable : (prefixWord ++ tailWord_4669159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669159).length < 2 ^ (prefixWord ++ tailWord_4669159).sum := by decide
  have hdescent : baseEnd_4669159 < baseStart_4669159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669190 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4669190 : Nat := 118140960795 + 4669190 * 2 ^ 59
def prefixEnd_4669190 : Nat := 4983230072969 + 3 ^ 40 * 4669190 * 2
def baseEnd_4669190 : Nat := 2397538737166692006351793

theorem tailTrace_4669190 : CollatzResearch.WordTrace tailWord_4669190 prefixEnd_4669190 2397538737166692006351793 := by
  unfold tailWord_4669190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5321854686072798094066657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113532899969553026006755349 5321854686072798094066657)
  ·
    refine ⟨3991391014554598570549993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5321854686072798094066657 3991391014554598570549993)
    ·
      refine ⟨2993543260915948927912495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3991391014554598570549993 2993543260915948927912495)
      ·
        refine ⟨4490314891373923391868743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2993543260915948927912495 4490314891373923391868743)
        ·
          refine ⟨6735472337060885087803115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4490314891373923391868743 6735472337060885087803115)
          ·
            refine ⟨10103208505591327631704673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6735472337060885087803115 10103208505591327631704673)
            ·
              refine ⟨7577406379193495723778505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10103208505591327631704673 7577406379193495723778505)
              ·
                refine ⟨5683054784395121792833879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7577406379193495723778505 5683054784395121792833879)
                ·
                  refine ⟨8524582176592682689250819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5683054784395121792833879 8524582176592682689250819)
                  ·
                    refine ⟨12786873264889024033876229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8524582176592682689250819 12786873264889024033876229)
                    ·
                      refine ⟨2397538737166692006351793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12786873264889024033876229 2397538737166692006351793)
                      ·
                        rfl

theorem cell23_4669190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4669190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669190 prefixEnd_4669190 := by exact prefixLift 4669190
  have htrace : WordTrace (prefixWord ++ tailWord_4669190) baseStart_4669190 baseEnd_4669190 := by
    simpa [prefixWord, tailWord_4669190, baseEnd_4669190] using wordTrace_append hprefix tailTrace_4669190
  have hstable : (prefixWord ++ tailWord_4669190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669190).length < 2 ^ (prefixWord ++ tailWord_4669190).sum := by decide
  have hdescent : baseEnd_4669190 < baseStart_4669190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669208 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_4669208 : Nat := 118140960795 + 4669208 * 2 ^ 59
def prefixEnd_4669208 : Nat := 4983230072969 + 3 ^ 40 * 4669208 * 2
def baseEnd_4669208 : Nat := 2397547979818472935926709

theorem tailTrace_4669208 : CollatzResearch.WordTrace tailWord_4669208 prefixEnd_4669208 2397547979818472935926709 := by
  unfold tailWord_4669208
  simp only [CollatzResearch.WordTrace]
  refine ⟨85150003234132164042144139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113533337645509552056192185 85150003234132164042144139)
  ·
    refine ⟨127725004851198246063216209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85150003234132164042144139 127725004851198246063216209)
    ·
      refine ⟨95793753638398684547412157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127725004851198246063216209 95793753638398684547412157)
      ·
        refine ⟨35922657614399506705279559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95793753638398684547412157 35922657614399506705279559)
        ·
          refine ⟨53883986421599260057919339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35922657614399506705279559 53883986421599260057919339)
          ·
            refine ⟨80825979632398890086879009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53883986421599260057919339 80825979632398890086879009)
            ·
              refine ⟨60619484724299167565159257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80825979632398890086879009 60619484724299167565159257)
              ·
                refine ⟨45464613543224375673869443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60619484724299167565159257 45464613543224375673869443)
                ·
                  refine ⟨68196920314836563510804165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45464613543224375673869443 68196920314836563510804165)
                  ·
                    refine ⟨12786922559031855658275781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68196920314836563510804165 12786922559031855658275781)
                    ·
                      refine ⟨2397547979818472935926709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12786922559031855658275781 2397547979818472935926709)
                      ·
                        rfl

theorem cell23_4669208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_4669208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669208 prefixEnd_4669208 := by exact prefixLift 4669208
  have htrace : WordTrace (prefixWord ++ tailWord_4669208) baseStart_4669208 baseEnd_4669208 := by
    simpa [prefixWord, tailWord_4669208, baseEnd_4669208] using wordTrace_append hprefix tailTrace_4669208
  have hstable : (prefixWord ++ tailWord_4669208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669208).length < 2 ^ (prefixWord ++ tailWord_4669208).sum := by decide
  have hdescent : baseEnd_4669208 < baseStart_4669208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669212 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_4669212 : Nat := 118140960795 + 4669212 * 2 ^ 59
def prefixEnd_4669212 : Nat := 4983230072969 + 3 ^ 40 * 4669212 * 2
def baseEnd_4669212 : Nat := 2397550033741090920276691

theorem tailTrace_4669212 : CollatzResearch.WordTrace tailWord_4669212 prefixEnd_4669212 2397550033741090920276691 := by
  unfold tailWord_4669212
  simp only [CollatzResearch.WordTrace]
  refine ⟨85150076180124918383716945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113533434906833224511622593 85150076180124918383716945)
  ·
    refine ⟨63862557135093688787787709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85150076180124918383716945 63862557135093688787787709)
    ·
      refine ⟨23948458925660133295420391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63862557135093688787787709 23948458925660133295420391)
      ·
        refine ⟨35922688388490199943130587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23948458925660133295420391 35922688388490199943130587)
        ·
          refine ⟨53884032582735299914695881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35922688388490199943130587 53884032582735299914695881)
          ·
            refine ⟨40413024437051474936021911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53884032582735299914695881 40413024437051474936021911)
            ·
              refine ⟨60619536655577212404032867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40413024437051474936021911 60619536655577212404032867)
              ·
                refine ⟨90929304983365818606049301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60619536655577212404032867 90929304983365818606049301)
                ·
                  refine ⟨4262311171095272747158561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90929304983365818606049301 4262311171095272747158561)
                  ·
                    refine ⟨3196733378321454560368921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4262311171095272747158561 3196733378321454560368921)
                    ·
                      refine ⟨2397550033741090920276691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196733378321454560368921 2397550033741090920276691)
                      ·
                        rfl

theorem cell23_4669212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_4669212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669212 prefixEnd_4669212 := by exact prefixLift 4669212
  have htrace : WordTrace (prefixWord ++ tailWord_4669212) baseStart_4669212 baseEnd_4669212 := by
    simpa [prefixWord, tailWord_4669212, baseEnd_4669212] using wordTrace_append hprefix tailTrace_4669212
  have hstable : (prefixWord ++ tailWord_4669212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669212).length < 2 ^ (prefixWord ++ tailWord_4669212).sum := by decide
  have hdescent : baseEnd_4669212 < baseStart_4669212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669246 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_4669246 : Nat := 118140960795 + 4669246 * 2 ^ 59
def prefixEnd_4669246 : Nat := 4983230072969 + 3 ^ 40 * 4669246 * 2
def baseEnd_4669246 : Nat := 2397567492083343787251535

theorem tailTrace_4669246 : CollatzResearch.WordTrace tailWord_4669246 prefixEnd_4669246 2397567492083343787251535 := by
  unfold tailWord_4669246
  simp only [CollatzResearch.WordTrace]
  refine ⟨21287674055265832571771449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113534261628084440382781061 21287674055265832571771449)
  ·
    refine ⟨15965755541449374428828587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21287674055265832571771449 15965755541449374428828587)
    ·
      refine ⟨23948633312174061643242881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15965755541449374428828587 23948633312174061643242881)
      ·
        refine ⟨17961474984130546232432161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23948633312174061643242881 17961474984130546232432161)
        ·
          refine ⟨13471106238097909674324121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17961474984130546232432161 13471106238097909674324121)
          ·
            refine ⟨10103329678573432255743091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13471106238097909674324121 10103329678573432255743091)
            ·
              refine ⟨15154994517860148383614637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10103329678573432255743091 15154994517860148383614637)
              ·
                refine ⟨5683122944197555643855489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15154994517860148383614637 5683122944197555643855489)
                ·
                  refine ⟨4262342208148166732891617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5683122944197555643855489 4262342208148166732891617)
                  ·
                    refine ⟨3196756656111125049668713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4262342208148166732891617 3196756656111125049668713)
                    ·
                      refine ⟨2397567492083343787251535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196756656111125049668713 2397567492083343787251535)
                      ·
                        rfl

theorem cell23_4669246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_4669246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669246 prefixEnd_4669246 := by exact prefixLift 4669246
  have htrace : WordTrace (prefixWord ++ tailWord_4669246) baseStart_4669246 baseEnd_4669246 := by
    simpa [prefixWord, tailWord_4669246, baseEnd_4669246] using wordTrace_append hprefix tailTrace_4669246
  have hstable : (prefixWord ++ tailWord_4669246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669246).length < 2 ^ (prefixWord ++ tailWord_4669246).sum := by decide
  have hdescent : baseEnd_4669246 < baseStart_4669246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669258 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_4669258 : Nat := 118140960795 + 4669258 * 2 ^ 59
def prefixEnd_4669258 : Nat := 4983230072969 + 3 ^ 40 * 4669258 * 2
def baseEnd_4669258 : Nat := 2397573653851197740301479

theorem tailTrace_4669258 : CollatzResearch.WordTrace tailWord_4669258 prefixEnd_4669258 2397573653851197740301479 := by
  unfold tailWord_4669258
  simp only [CollatzResearch.WordTrace]
  refine ⟨42575457529520796655902107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113534553412055457749072285 42575457529520796655902107)
  ·
    refine ⟨63863186294281194983853161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42575457529520796655902107 63863186294281194983853161)
    ·
      refine ⟨47897389720710896237889871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63863186294281194983853161 47897389720710896237889871)
      ·
        refine ⟨71846084581066344356834807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47897389720710896237889871 71846084581066344356834807)
        ·
          refine ⟨107769126871599516535252211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71846084581066344356834807 107769126871599516535252211)
          ·
            refine ⟨161653690307399274802878317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107769126871599516535252211 161653690307399274802878317)
            ·
              refine ⟨60620133865274728051079369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161653690307399274802878317 60620133865274728051079369)
              ·
                refine ⟨45465100398956046038309527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60620133865274728051079369 45465100398956046038309527)
                ·
                  refine ⟨68197650598434069057464291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45465100398956046038309527 68197650598434069057464291)
                  ·
                    refine ⟨102296475897651103586196437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68197650598434069057464291 102296475897651103586196437)
                    ·
                      refine ⟨2397573653851197740301479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102296475897651103586196437 2397573653851197740301479)
                      ·
                        rfl

theorem cell23_4669258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_4669258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669258 prefixEnd_4669258 := by exact prefixLift 4669258
  have htrace : WordTrace (prefixWord ++ tailWord_4669258) baseStart_4669258 baseEnd_4669258 := by
    simpa [prefixWord, tailWord_4669258, baseEnd_4669258] using wordTrace_append hprefix tailTrace_4669258
  have hstable : (prefixWord ++ tailWord_4669258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669258).length < 2 ^ (prefixWord ++ tailWord_4669258).sum := by decide
  have hdescent : baseEnd_4669258 < baseStart_4669258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669265 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 2, 5]
def baseStart_4669265 : Nat := 118140960795 + 4669265 * 2 ^ 59
def prefixEnd_4669265 : Nat := 4983230072969 + 3 ^ 40 * 4669265 * 2
def baseEnd_4669265 : Nat := 799192416071926404304649

theorem tailTrace_4669265 : CollatzResearch.WordTrace tailWord_4669265 prefixEnd_4669265 799192416071926404304649 := by
  unfold tailWord_4669265
  simp only [CollatzResearch.WordTrace]
  refine ⟨170302085429057826819113249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113534723619371884546075499 170302085429057826819113249)
  ·
    refine ⟨127726564071793370114334937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170302085429057826819113249 127726564071793370114334937)
    ·
      refine ⟨95794923053845027585751203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127726564071793370114334937 95794923053845027585751203)
      ·
        refine ⟨143692384580767541378626805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95794923053845027585751203 143692384580767541378626805)
        ·
          refine ⟨13471161054446957004246263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143692384580767541378626805 13471161054446957004246263)
          ·
            refine ⟨20206741581670435506369395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13471161054446957004246263 20206741581670435506369395)
            ·
              refine ⟨30310112372505653259554093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20206741581670435506369395 30310112372505653259554093)
              ·
                refine ⟨11366292139689619972332785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30310112372505653259554093 11366292139689619972332785)
                ·
                  refine ⟨8524719104767214979249589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11366292139689619972332785 8524719104767214979249589)
                  ·
                    refine ⟨799192416071926404304649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8524719104767214979249589 799192416071926404304649)
                    ·
                      rfl

theorem cell23_4669265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_4669265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669265 prefixEnd_4669265 := by exact prefixLift 4669265
  have htrace : WordTrace (prefixWord ++ tailWord_4669265) baseStart_4669265 baseEnd_4669265 := by
    simpa [prefixWord, tailWord_4669265, baseEnd_4669265] using wordTrace_append hprefix tailTrace_4669265
  have hstable : (prefixWord ++ tailWord_4669265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669265).length < 2 ^ (prefixWord ++ tailWord_4669265).sum := by decide
  have hdescent : baseEnd_4669265 < baseStart_4669265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669282 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_4669282 : Nat := 118140960795 + 4669282 * 2 ^ 59
def prefixEnd_4669282 : Nat := 4983230072969 + 3 ^ 40 * 4669282 * 2
def baseEnd_4669282 : Nat := 799195325795635215467123

theorem tailTrace_4669282 : CollatzResearch.WordTrace tailWord_4669282 prefixEnd_4669282 799195325795635215467123 := by
  unfold tailWord_4669282
  simp only [CollatzResearch.WordTrace]
  refine ⟨42575676367499059680620525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113535136979997492481654733 42575676367499059680620525)
  ·
    refine ⟨15965878637812147380232697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42575676367499059680620525 15965878637812147380232697)
    ·
      refine ⟨11974408978359110535174523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15965878637812147380232697 11974408978359110535174523)
      ·
        refine ⟨17961613467538665802761785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11974408978359110535174523 17961613467538665802761785)
        ·
          refine ⟨13471210100653999352071339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17961613467538665802761785 13471210100653999352071339)
          ·
            refine ⟨20206815150980999028107009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13471210100653999352071339 20206815150980999028107009)
            ·
              refine ⟨15155111363235749271080257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20206815150980999028107009 15155111363235749271080257)
              ·
                refine ⟨11366333522426811953310193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15155111363235749271080257 11366333522426811953310193)
                ·
                  refine ⟨8524750141820108964982645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11366333522426811953310193 8524750141820108964982645)
                  ·
                    refine ⟨799195325795635215467123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8524750141820108964982645 799195325795635215467123)
                    ·
                      rfl

theorem cell23_4669282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_4669282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669282 prefixEnd_4669282 := by exact prefixLift 4669282
  have htrace : WordTrace (prefixWord ++ tailWord_4669282) baseStart_4669282 baseEnd_4669282 := by
    simpa [prefixWord, tailWord_4669282, baseEnd_4669282] using wordTrace_append hprefix tailTrace_4669282
  have hstable : (prefixWord ++ tailWord_4669282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669282).length < 2 ^ (prefixWord ++ tailWord_4669282).sum := by decide
  have hdescent : baseEnd_4669282 < baseStart_4669282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669305 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 1, 4, 3]
def baseStart_4669305 : Nat := 118140960795 + 4669305 * 2 ^ 59
def prefixEnd_4669305 : Nat := 4983230072969 + 3 ^ 40 * 4669305 * 2
def baseEnd_4669305 : Nat := 2397597787441959056413763

theorem tailTrace_4669305 : CollatzResearch.WordTrace tailWord_4669305 prefixEnd_4669305 2397597787441959056413763 := by
  unfold tailWord_4669305
  simp only [CollatzResearch.WordTrace]
  refine ⟨170303544348912913650569369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113535696232608609100379579 170303544348912913650569369)
  ·
    refine ⟨127727658261684685237927027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170303544348912913650569369 127727658261684685237927027)
    ·
      refine ⟨191591487392527027856890541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127727658261684685237927027 191591487392527027856890541)
      ·
        refine ⟨71846807772197635446333953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191591487392527027856890541 71846807772197635446333953)
        ·
          refine ⟨53885105829148226584750465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71846807772197635446333953 53885105829148226584750465)
          ·
            refine ⟨40413829371861169938562849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53885105829148226584750465 40413829371861169938562849)
            ·
              refine ⟨30310372028895877453922137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40413829371861169938562849 30310372028895877453922137)
              ·
                refine ⟨22732779021671908090441603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30310372028895877453922137 22732779021671908090441603)
                ·
                  refine ⟨34099168532507862135662405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22732779021671908090441603 34099168532507862135662405)
                  ·
                    refine ⟨6393594099845224150436701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34099168532507862135662405 6393594099845224150436701)
                    ·
                      refine ⟨2397597787441959056413763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6393594099845224150436701 2397597787441959056413763)
                      ·
                        rfl

theorem cell23_4669305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_4669305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669305 prefixEnd_4669305 := by exact prefixLift 4669305
  have htrace : WordTrace (prefixWord ++ tailWord_4669305) baseStart_4669305 baseEnd_4669305 := by
    simpa [prefixWord, tailWord_4669305, baseEnd_4669305] using wordTrace_append hprefix tailTrace_4669305
  have hstable : (prefixWord ++ tailWord_4669305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669305).length < 2 ^ (prefixWord ++ tailWord_4669305).sum := by decide
  have hdescent : baseEnd_4669305 < baseStart_4669305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669308 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 12]
def baseStart_4669308 : Nat := 118140960795 + 4669308 * 2 ^ 59
def prefixEnd_4669308 : Nat := 4983230072969 + 3 ^ 40 * 4669308 * 2
def baseEnd_4669308 : Nat := 266399925320435838297361

theorem tailTrace_4669308 : CollatzResearch.WordTrace tailWord_4669308 prefixEnd_4669308 266399925320435838297361 := by
  unfold tailWord_4669308
  simp only [CollatzResearch.WordTrace]
  refine ⟨85151826883951022581464289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113535769178601363441952385 85151826883951022581464289)
  ·
    refine ⟨63863870162963266936098217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85151826883951022581464289 63863870162963266936098217)
    ·
      refine ⟨47897902622222450202073663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63863870162963266936098217 47897902622222450202073663)
      ·
        refine ⟨71846853933333675303110495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47897902622222450202073663 71846853933333675303110495)
        ·
          refine ⟨107770280900000512954665743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71846853933333675303110495 107770280900000512954665743)
          ·
            refine ⟨161655421350000769431998615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107770280900000512954665743 161655421350000769431998615)
            ·
              refine ⟨242483132025001154147997923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161655421350000769431998615 242483132025001154147997923)
              ·
                refine ⟨363724698037501731221996885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242483132025001154147997923 363724698037501731221996885)
                ·
                  refine ⟨266399925320435838297361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 363724698037501731221996885 266399925320435838297361)
                  ·
                    rfl

theorem cell23_4669308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_4669308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669308 prefixEnd_4669308 := by exact prefixLift 4669308
  have htrace : WordTrace (prefixWord ++ tailWord_4669308) baseStart_4669308 baseEnd_4669308 := by
    simpa [prefixWord, tailWord_4669308, baseEnd_4669308] using wordTrace_append hprefix tailTrace_4669308
  have hstable : (prefixWord ++ tailWord_4669308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669308).length < 2 ^ (prefixWord ++ tailWord_4669308).sum := by decide
  have hdescent : baseEnd_4669308 < baseStart_4669308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669319 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_4669319 : Nat := 118140960795 + 4669319 * 2 ^ 59
def prefixEnd_4669319 : Nat := 4983230072969 + 3 ^ 40 * 4669319 * 2
def baseEnd_4669319 : Nat := 2397604976171122001638699

theorem tailTrace_4669319 : CollatzResearch.WordTrace tailWord_4669319 prefixEnd_4669319 2397604976171122001638699 := by
  unfold tailWord_4669319
  simp only [CollatzResearch.WordTrace]
  refine ⟨170304054970862194041579011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113536036647241462694386007 170304054970862194041579011)
  ·
    refine ⟨255456082456293291062368517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170304054970862194041579011 255456082456293291062368517)
    ·
      refine ⟨47898015460554992074194097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255456082456293291062368517 47898015460554992074194097)
      ·
        refine ⟨35923511595416244055645573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47898015460554992074194097 35923511595416244055645573)
        ·
          refine ⟨6735658424140545760433545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35923511595416244055645573 6735658424140545760433545)
          ·
            refine ⟨5051743818105409320325159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6735658424140545760433545 5051743818105409320325159)
            ·
              refine ⟨7577615727158113980487739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5051743818105409320325159 7577615727158113980487739)
              ·
                refine ⟨11366423590737170970731609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7577615727158113980487739 11366423590737170970731609)
                ·
                  refine ⟨8524817693052878228048707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11366423590737170970731609 8524817693052878228048707)
                  ·
                    refine ⟨12787226539579317342073061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8524817693052878228048707 12787226539579317342073061)
                    ·
                      refine ⟨2397604976171122001638699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12787226539579317342073061 2397604976171122001638699)
                      ·
                        rfl

theorem cell23_4669319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_4669319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669319 prefixEnd_4669319 := by exact prefixLift 4669319
  have htrace : WordTrace (prefixWord ++ tailWord_4669319) baseStart_4669319 baseEnd_4669319 := by
    simpa [prefixWord, tailWord_4669319, baseEnd_4669319] using wordTrace_append hprefix tailTrace_4669319
  have hstable : (prefixWord ++ tailWord_4669319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669319).length < 2 ^ (prefixWord ++ tailWord_4669319).sum := by decide
  have hdescent : baseEnd_4669319 < baseStart_4669319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669328 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_4669328 : Nat := 118140960795 + 4669328 * 2 ^ 59
def prefixEnd_4669328 : Nat := 4983230072969 + 3 ^ 40 * 4669328 * 2
def baseEnd_4669328 : Nat := 2397609597497012466426157

theorem tailTrace_4669328 : CollatzResearch.WordTrace tailWord_4669328 prefixEnd_4669328 2397609597497012466426157 := by
  unfold tailWord_4669328
  simp only [CollatzResearch.WordTrace]
  refine ⟨85152191613914794289328319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113536255485219725719104425 85152191613914794289328319)
  ·
    refine ⟨127728287420872191433992479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85152191613914794289328319 127728287420872191433992479)
    ·
      refine ⟨191592431131308287150988719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127728287420872191433992479 191592431131308287150988719)
      ·
        refine ⟨287388646696962430726483079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191592431131308287150988719 287388646696962430726483079)
        ·
          refine ⟨431082970045443646089724619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287388646696962430726483079 431082970045443646089724619)
          ·
            refine ⟨646624455068165469134586929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431082970045443646089724619 646624455068165469134586929)
            ·
              refine ⟨484968341301124101850940197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646624455068165469134586929 484968341301124101850940197)
              ·
                refine ⟨90931563993960769097051287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 484968341301124101850940197 90931563993960769097051287)
                ·
                  refine ⟨136397345990941153645576931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90931563993960769097051287 136397345990941153645576931)
                  ·
                    refine ⟨204596018986411730468365397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136397345990941153645576931 204596018986411730468365397)
                    ·
                      refine ⟨2397609597497012466426157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 204596018986411730468365397 2397609597497012466426157)
                      ·
                        rfl

theorem cell23_4669328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_4669328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669328 prefixEnd_4669328 := by exact prefixLift 4669328
  have htrace : WordTrace (prefixWord ++ tailWord_4669328) baseStart_4669328 baseEnd_4669328 := by
    simpa [prefixWord, tailWord_4669328, baseEnd_4669328] using wordTrace_append hprefix tailTrace_4669328
  have hstable : (prefixWord ++ tailWord_4669328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669328).length < 2 ^ (prefixWord ++ tailWord_4669328).sum := by decide
  have hdescent : baseEnd_4669328 < baseStart_4669328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669386 : List Nat := [3, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3]
def baseStart_4669386 : Nat := 118140960795 + 4669386 * 2 ^ 59
def prefixEnd_4669386 : Nat := 4983230072969 + 3 ^ 40 * 4669386 * 2
def baseEnd_4669386 : Nat := 2397639379374973239500891

theorem tailTrace_4669386 : CollatzResearch.WordTrace tailWord_4669386 prefixEnd_4669386 2397639379374973239500891 := by
  unfold tailWord_4669386
  simp only [CollatzResearch.WordTrace]
  refine ⟨42576624665404866121067003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113537665774412976322845341 42576624665404866121067003)
  ·
    refine ⟨63864936998107299181600505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42576624665404866121067003 63864936998107299181600505)
    ·
      refine ⟨47898702748580474386200379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63864936998107299181600505 47898702748580474386200379)
      ·
        refine ⟨71848054122870711579300569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47898702748580474386200379 71848054122870711579300569)
        ·
          refine ⟨53886040592153033684475427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71848054122870711579300569 53886040592153033684475427)
          ·
            refine ⟨80829060888229550526713141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53886040592153033684475427 80829060888229550526713141)
            ·
              refine ⟨7577724458271520361879357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80829060888229550526713141 7577724458271520361879357)
              ·
                refine ⟨2841646671851820135704759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7577724458271520361879357 2841646671851820135704759)
                ·
                  refine ⟨4262470007777730203557139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841646671851820135704759 4262470007777730203557139)
                  ·
                    refine ⟨6393705011666595305335709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4262470007777730203557139 6393705011666595305335709)
                    ·
                      refine ⟨2397639379374973239500891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6393705011666595305335709 2397639379374973239500891)
                      ·
                        rfl

theorem cell23_4669386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_4669386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669386 prefixEnd_4669386 := by exact prefixLift 4669386
  have htrace : WordTrace (prefixWord ++ tailWord_4669386) baseStart_4669386 baseEnd_4669386 := by
    simpa [prefixWord, tailWord_4669386, baseEnd_4669386] using wordTrace_append hprefix tailTrace_4669386
  have hstable : (prefixWord ++ tailWord_4669386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669386).length < 2 ^ (prefixWord ++ tailWord_4669386).sum := by decide
  have hdescent : baseEnd_4669386 < baseStart_4669386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669392 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 4]
def baseStart_4669392 : Nat := 118140960795 + 4669392 * 2 ^ 59
def prefixEnd_4669392 : Nat := 4983230072969 + 3 ^ 40 * 4669392 * 2
def baseEnd_4669392 : Nat := 2397642460258900216025863

theorem tailTrace_4669392 : CollatzResearch.WordTrace tailWord_4669392 prefixEnd_4669392 2397642460258900216025863 := by
  unfold tailWord_4669392
  simp only [CollatzResearch.WordTrace]
  refine ⟨85153358749798863754493215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113537811666398485005990953 85153358749798863754493215)
  ·
    refine ⟨127730038124698295631739823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85153358749798863754493215 127730038124698295631739823)
    ·
      refine ⟨191595057187047443447609735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127730038124698295631739823 191595057187047443447609735)
      ·
        refine ⟨287392585780571165171414603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191595057187047443447609735 287392585780571165171414603)
        ·
          refine ⟨431088878670856747757121905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287392585780571165171414603 431088878670856747757121905)
          ·
            refine ⟨323316659003142560817841429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431088878670856747757121905 323316659003142560817841429)
            ·
              refine ⟨15155468390772307538336317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 323316659003142560817841429 15155468390772307538336317)
              ·
                refine ⟨5683300646539615326876119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15155468390772307538336317 5683300646539615326876119)
                ·
                  refine ⟨8524950969809422990314179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5683300646539615326876119 8524950969809422990314179)
                  ·
                    refine ⟨12787426454714134485471269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8524950969809422990314179 12787426454714134485471269)
                    ·
                      refine ⟨2397642460258900216025863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12787426454714134485471269 2397642460258900216025863)
                      ·
                        rfl

theorem cell23_4669392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 4].length) (baseStart_4669392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669392 prefixEnd_4669392 := by exact prefixLift 4669392
  have htrace : WordTrace (prefixWord ++ tailWord_4669392) baseStart_4669392 baseEnd_4669392 := by
    simpa [prefixWord, tailWord_4669392, baseEnd_4669392] using wordTrace_append hprefix tailTrace_4669392
  have hstable : (prefixWord ++ tailWord_4669392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669392).length < 2 ^ (prefixWord ++ tailWord_4669392).sum := by decide
  have hdescent : baseEnd_4669392 < baseStart_4669392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669412 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_4669412 : Nat := 118140960795 + 4669412 * 2 ^ 59
def prefixEnd_4669412 : Nat := 4983230072969 + 3 ^ 40 * 4669412 * 2
def baseEnd_4669412 : Nat := 2397652729871990137775771

theorem tailTrace_4669412 : CollatzResearch.WordTrace tailWord_4669412 prefixEnd_4669412 2397652729871990137775771 := by
  unfold tailWord_4669412
  simp only [CollatzResearch.WordTrace]
  refine ⟨85153723479762635462357245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113538297973016847283142993 85153723479762635462357245)
  ·
    refine ⟨31932646304910988298383967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85153723479762635462357245 31932646304910988298383967)
    ·
      refine ⟨47898969457366482447575951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31932646304910988298383967 47898969457366482447575951)
      ·
        refine ⟨71848454186049723671363927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47898969457366482447575951 71848454186049723671363927)
        ·
          refine ⟨107772681279074585507045891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71848454186049723671363927 107772681279074585507045891)
          ·
            refine ⟨161659021918611878260568837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107772681279074585507045891 161659021918611878260568837)
            ·
              refine ⟨30311066609739727173856657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161659021918611878260568837 30311066609739727173856657)
              ·
                refine ⟨22733299957304795380392493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30311066609739727173856657 22733299957304795380392493)
                ·
                  refine ⟨8524987483989298267647185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22733299957304795380392493 8524987483989298267647185)
                  ·
                    refine ⟨6393740612991973700735389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8524987483989298267647185 6393740612991973700735389)
                    ·
                      refine ⟨2397652729871990137775771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6393740612991973700735389 2397652729871990137775771)
                      ·
                        rfl

theorem cell23_4669412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_4669412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669412 prefixEnd_4669412 := by exact prefixLift 4669412
  have htrace : WordTrace (prefixWord ++ tailWord_4669412) baseStart_4669412 baseEnd_4669412 := by
    simpa [prefixWord, tailWord_4669412, baseEnd_4669412] using wordTrace_append hprefix tailTrace_4669412
  have hstable : (prefixWord ++ tailWord_4669412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669412).length < 2 ^ (prefixWord ++ tailWord_4669412).sum := by decide
  have hdescent : baseEnd_4669412 < baseStart_4669412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669422 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_4669422 : Nat := 118140960795 + 4669422 * 2 ^ 59
def prefixEnd_4669422 : Nat := 4983230072969 + 3 ^ 40 * 4669422 * 2
def baseEnd_4669422 : Nat := 2397657864678535098650725

theorem tailTrace_4669422 : CollatzResearch.WordTrace tailWord_4669422 prefixEnd_4669422 2397657864678535098650725 := by
  unfold tailWord_4669422
  simp only [CollatzResearch.WordTrace]
  refine ⟨21288476461186130329072315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113538541126326028421719013 21288476461186130329072315)
  ·
    refine ⟨31932714691779195493608473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21288476461186130329072315 31932714691779195493608473)
    ·
      refine ⟨23949536018834396620206355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31932714691779195493608473 23949536018834396620206355)
      ·
        refine ⟨35924304028251594930309533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23949536018834396620206355 35924304028251594930309533)
        ·
          refine ⟨13471614010594348098866075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35924304028251594930309533 13471614010594348098866075)
          ·
            refine ⟨20207421015891522148299113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13471614010594348098866075 20207421015891522148299113)
            ·
              refine ⟨15155565761918641611224335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20207421015891522148299113 15155565761918641611224335)
              ·
                refine ⟨22733348642877962416836503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15155565761918641611224335 22733348642877962416836503)
                ·
                  refine ⟨34100022964316943625254755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22733348642877962416836503 34100022964316943625254755)
                  ·
                    refine ⟨51150034446475415437882133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34100022964316943625254755 51150034446475415437882133)
                    ·
                      refine ⟨2397657864678535098650725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51150034446475415437882133 2397657864678535098650725)
                      ·
                        rfl

theorem cell23_4669422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_4669422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669422 prefixEnd_4669422 := by exact prefixLift 4669422
  have htrace : WordTrace (prefixWord ++ tailWord_4669422) baseStart_4669422 baseEnd_4669422 := by
    simpa [prefixWord, tailWord_4669422, baseEnd_4669422] using wordTrace_append hprefix tailTrace_4669422
  have hstable : (prefixWord ++ tailWord_4669422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669422).length < 2 ^ (prefixWord ++ tailWord_4669422).sum := by decide
  have hdescent : baseEnd_4669422 < baseStart_4669422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669459 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 2, 1, 3]
def baseStart_4669459 : Nat := 118140960795 + 4669459 * 2 ^ 59
def prefixEnd_4669459 : Nat := 4983230072969 + 3 ^ 40 * 4669459 * 2
def baseEnd_4669459 : Nat := 2397676863462751453888055

theorem tailTrace_4669459 : CollatzResearch.WordTrace tailWord_4669459 prefixEnd_4669459 2397676863462751453888055 := by
  unfold tailWord_4669459
  simp only [CollatzResearch.WordTrace]
  refine ⟨170309161190354997951675431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113539440793569998634450287 170309161190354997951675431)
  ·
    refine ⟨255463741785532496927513147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170309161190354997951675431 255463741785532496927513147)
    ·
      refine ⟨383195612678298745391269721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255463741785532496927513147 383195612678298745391269721)
      ·
        refine ⟨287396709508724059043452291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383195612678298745391269721 287396709508724059043452291)
        ·
          refine ⟨431095064263086088565178437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287396709508724059043452291 431095064263086088565178437)
          ·
            refine ⟨80830324549328641605970957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 431095064263086088565178437 80830324549328641605970957)
            ·
              refine ⟨30311371705998240602239109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80830324549328641605970957 30311371705998240602239109)
              ·
                refine ⟨5683382194874670112919833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30311371705998240602239109 5683382194874670112919833)
                ·
                  refine ⟨4262536646156002584689875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5683382194874670112919833 4262536646156002584689875)
                  ·
                    refine ⟨6393804969234003877034813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4262536646156002584689875 6393804969234003877034813)
                    ·
                      refine ⟨2397676863462751453888055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6393804969234003877034813 2397676863462751453888055)
                      ·
                        rfl

theorem cell23_4669459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 1, 3].length) (baseStart_4669459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669459 prefixEnd_4669459 := by exact prefixLift 4669459
  have htrace : WordTrace (prefixWord ++ tailWord_4669459) baseStart_4669459 baseEnd_4669459 := by
    simpa [prefixWord, tailWord_4669459, baseEnd_4669459] using wordTrace_append hprefix tailTrace_4669459
  have hstable : (prefixWord ++ tailWord_4669459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669459).length < 2 ^ (prefixWord ++ tailWord_4669459).sum := by decide
  have hdescent : baseEnd_4669459 < baseStart_4669459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669476 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_4669476 : Nat := 118140960795 + 4669476 * 2 ^ 59
def prefixEnd_4669476 : Nat := 4983230072969 + 3 ^ 40 * 4669476 * 2
def baseEnd_4669476 : Nat := 2397685592633877887375477

theorem tailTrace_4669476 : CollatzResearch.WordTrace tailWord_4669476 prefixEnd_4669476 2397685592633877887375477 := by
  unfold tailWord_4669476
  simp only [CollatzResearch.WordTrace]
  refine ⟨85154890615646704927522141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113539854154195606570029521 85154890615646704927522141)
  ·
    refine ⟨31933083980867514347820803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85154890615646704927522141 31933083980867514347820803)
    ·
      refine ⟨47899625971301271521731205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31933083980867514347820803 47899625971301271521731205)
      ·
        refine ⟨8981179869618988410324601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47899625971301271521731205 8981179869618988410324601)
        ·
          refine ⟨6735884902214241307743451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8981179869618988410324601 6735884902214241307743451)
          ·
            refine ⟨10103827353321361961615177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6735884902214241307743451 10103827353321361961615177)
            ·
              refine ⟨7577870514991021471211383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10103827353321361961615177 7577870514991021471211383)
              ·
                refine ⟨11366805772486532206817075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7577870514991021471211383 11366805772486532206817075)
                ·
                  refine ⟨17050208658729798310225613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11366805772486532206817075 17050208658729798310225613)
                  ·
                    refine ⟨6393828247023674366334605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17050208658729798310225613 6393828247023674366334605)
                    ·
                      refine ⟨2397685592633877887375477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6393828247023674366334605 2397685592633877887375477)
                      ·
                        rfl

theorem cell23_4669476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_4669476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669476 prefixEnd_4669476 := by exact prefixLift 4669476
  have htrace : WordTrace (prefixWord ++ tailWord_4669476) baseStart_4669476 baseEnd_4669476 := by
    simpa [prefixWord, tailWord_4669476, baseEnd_4669476] using wordTrace_append hprefix tailTrace_4669476
  have hstable : (prefixWord ++ tailWord_4669476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669476).length < 2 ^ (prefixWord ++ tailWord_4669476).sum := by decide
  have hdescent : baseEnd_4669476 < baseStart_4669476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669486 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_4669486 : Nat := 118140960795 + 4669486 * 2 ^ 59
def prefixEnd_4669486 : Nat := 4983230072969 + 3 ^ 40 * 4669486 * 2
def baseEnd_4669486 : Nat := 2397690727440422848250431

theorem tailTrace_4669486 : CollatzResearch.WordTrace tailWord_4669486 prefixEnd_4669486 2397690727440422848250431 := by
  unfold tailWord_4669486
  simp only [CollatzResearch.WordTrace]
  refine ⟨21288768245157147695363539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113540097307504787708605541 21288768245157147695363539)
  ·
    refine ⟨31933152367735721543045309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21288768245157147695363539 31933152367735721543045309)
    ·
      refine ⟨11974932137900895578641991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31933152367735721543045309 11974932137900895578641991)
      ·
        refine ⟨17962398206851343367962987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11974932137900895578641991 17962398206851343367962987)
        ·
          refine ⟨26943597310277015051944481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17962398206851343367962987 26943597310277015051944481)
          ·
            refine ⟨20207697982707761288958361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26943597310277015051944481 20207697982707761288958361)
            ·
              refine ⟨15155773487030820966718771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20207697982707761288958361 15155773487030820966718771)
              ·
                refine ⟨22733660230546231450078157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15155773487030820966718771 22733660230546231450078157)
                ·
                  refine ⟨8525122586454836793779309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22733660230546231450078157 8525122586454836793779309)
                  ·
                    refine ⟨3196920969920563797667241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8525122586454836793779309 3196920969920563797667241)
                    ·
                      refine ⟨2397690727440422848250431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196920969920563797667241 2397690727440422848250431)
                      ·
                        rfl

theorem cell23_4669486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_4669486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669486 prefixEnd_4669486 := by exact prefixLift 4669486
  have htrace : WordTrace (prefixWord ++ tailWord_4669486) baseStart_4669486 baseEnd_4669486 := by
    simpa [prefixWord, tailWord_4669486, baseEnd_4669486] using wordTrace_append hprefix tailTrace_4669486
  have hstable : (prefixWord ++ tailWord_4669486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669486).length < 2 ^ (prefixWord ++ tailWord_4669486).sum := by decide
  have hdescent : baseEnd_4669486 < baseStart_4669486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669499 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 6, 2, 2]
def baseStart_4669499 : Nat := 118140960795 + 4669499 * 2 ^ 59
def prefixEnd_4669499 : Nat := 4983230072969 + 3 ^ 40 * 4669499 * 2
def baseEnd_4669499 : Nat := 2397697402688931297387871

theorem tailTrace_4669499 : CollatzResearch.WordTrace tailWord_4669499 prefixEnd_4669499 2397697402688931297387871 := by
  unfold tailWord_4669499
  simp only [CollatzResearch.WordTrace]
  refine ⟨170310620110210084783131551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113540413406806723188754367 170310620110210084783131551)
  ·
    refine ⟨255465930165315127174697327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170310620110210084783131551 255465930165315127174697327)
    ·
      refine ⟨383198895247972690762045991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255465930165315127174697327 383198895247972690762045991)
      ·
        refine ⟨574798342871959036143068987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383198895247972690762045991 574798342871959036143068987)
        ·
          refine ⟨862197514307938554214603481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574798342871959036143068987 862197514307938554214603481)
          ·
            refine ⟨646648135730953915660952611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862197514307938554214603481 646648135730953915660952611)
            ·
              refine ⟨969972203596430873491428917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646648135730953915660952611 969972203596430873491428917)
              ·
                refine ⟨90934894087165394389821461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 969972203596430873491428917 90934894087165394389821461)
                ·
                  refine ⟨4262573160335877862022881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90934894087165394389821461 4262573160335877862022881)
                  ·
                    refine ⟨3196929870251908396517161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4262573160335877862022881 3196929870251908396517161)
                    ·
                      refine ⟨2397697402688931297387871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196929870251908396517161 2397697402688931297387871)
                      ·
                        rfl

theorem cell23_4669499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 2, 2].length) (baseStart_4669499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669499 prefixEnd_4669499 := by exact prefixLift 4669499
  have htrace : WordTrace (prefixWord ++ tailWord_4669499) baseStart_4669499 baseEnd_4669499 := by
    simpa [prefixWord, tailWord_4669499, baseEnd_4669499] using wordTrace_append hprefix tailTrace_4669499
  have hstable : (prefixWord ++ tailWord_4669499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669499).length < 2 ^ (prefixWord ++ tailWord_4669499).sum := by decide
  have hdescent : baseEnd_4669499 < baseStart_4669499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669515 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 7]
def baseStart_4669515 : Nat := 118140960795 + 4669515 * 2 ^ 59
def prefixEnd_4669515 : Nat := 4983230072969 + 3 ^ 40 * 4669515 * 2
def baseEnd_4669515 : Nat := 2397705618379403234787797

theorem tailTrace_4669515 : CollatzResearch.WordTrace tailWord_4669515 prefixEnd_4669515 2397705618379403234787797 := by
  unfold tailWord_4669515
  simp only [CollatzResearch.WordTrace]
  refine ⟨170311203678152119515713999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113540802452101413010475999 170311203678152119515713999)
  ·
    refine ⟨255466805517228179273570999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170311203678152119515713999 255466805517228179273570999)
    ·
      refine ⟨383200208275842268910356499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255466805517228179273570999 383200208275842268910356499)
      ·
        refine ⟨574800312413763403365534749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383200208275842268910356499 574800312413763403365534749)
        ·
          refine ⟨215550117155161276262075531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 574800312413763403365534749 215550117155161276262075531)
          ·
            refine ⟨323325175732741914393113297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215550117155161276262075531 323325175732741914393113297)
            ·
              refine ⟨242493881799556435794834973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323325175732741914393113297 242493881799556435794834973)
              ·
                refine ⟨90935205674833663423063115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242493881799556435794834973 90935205674833663423063115)
                ·
                  refine ⟨136402808512250495134594673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90935205674833663423063115 136402808512250495134594673)
                  ·
                    refine ⟨102302106384187871350946005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 136402808512250495134594673 102302106384187871350946005)
                    ·
                      refine ⟨2397705618379403234787797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102302106384187871350946005 2397705618379403234787797)
                      ·
                        rfl

theorem cell23_4669515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_4669515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669515 prefixEnd_4669515 := by exact prefixLift 4669515
  have htrace : WordTrace (prefixWord ++ tailWord_4669515) baseStart_4669515 baseEnd_4669515 := by
    simpa [prefixWord, tailWord_4669515, baseEnd_4669515] using wordTrace_append hprefix tailTrace_4669515
  have hstable : (prefixWord ++ tailWord_4669515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669515).length < 2 ^ (prefixWord ++ tailWord_4669515).sum := by decide
  have hdescent : baseEnd_4669515 < baseStart_4669515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669526 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_4669526 : Nat := 118140960795 + 4669526 * 2 ^ 59
def prefixEnd_4669526 : Nat := 4983230072969 + 3 ^ 40 * 4669526 * 2
def baseEnd_4669526 : Nat := 799237088888867563916749

theorem tailTrace_4669526 : CollatzResearch.WordTrace tailWord_4669526 prefixEnd_4669526 799237088888867563916749 := by
  unfold tailWord_4669526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10644475305069516774647777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113541069920741512262909621 10644475305069516774647777)
  ·
    refine ⟨7983356478802137580985833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10644475305069516774647777 7983356478802137580985833)
    ·
      refine ⟨5987517359101603185739375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7983356478802137580985833 5987517359101603185739375)
      ·
        refine ⟨8981276038652404778609063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5987517359101603185739375 8981276038652404778609063)
        ·
          refine ⟨13471914057978607167913595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8981276038652404778609063 13471914057978607167913595)
          ·
            refine ⟨20207871086967910751870393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13471914057978607167913595 20207871086967910751870393)
            ·
              refine ⟨15155903315225933063902795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20207871086967910751870393 15155903315225933063902795)
              ·
                refine ⟨22733854972838899595854193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15155903315225933063902795 22733854972838899595854193)
                ·
                  refine ⟨17050391229629174696890645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22733854972838899595854193 17050391229629174696890645)
                  ·
                    refine ⟨799237088888867563916749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17050391229629174696890645 799237088888867563916749)
                    ·
                      rfl

theorem cell23_4669526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_4669526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669526 prefixEnd_4669526 := by exact prefixLift 4669526
  have htrace : WordTrace (prefixWord ++ tailWord_4669526) baseStart_4669526 baseEnd_4669526 := by
    simpa [prefixWord, tailWord_4669526, baseEnd_4669526] using wordTrace_append hprefix tailTrace_4669526
  have hstable : (prefixWord ++ tailWord_4669526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669526).length < 2 ^ (prefixWord ++ tailWord_4669526).sum := by decide
  have hdescent : baseEnd_4669526 < baseStart_4669526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669533 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_4669533 : Nat := 118140960795 + 4669533 * 2 ^ 59
def prefixEnd_4669533 : Nat := 4983230072969 + 3 ^ 40 * 4669533 * 2
def baseEnd_4669533 : Nat := 2397714861031184164362715

theorem tailTrace_4669533 : CollatzResearch.WordTrace tailWord_4669533 prefixEnd_4669533 2397714861031184164362715 := by
  unfold tailWord_4669533
  simp only [CollatzResearch.WordTrace]
  refine ⟨170311860192086908589869253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113541240128057939059912835 170311860192086908589869253)
  ·
    refine ⟨31933473786016295360600485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170311860192086908589869253 31933473786016295360600485)
    ·
      refine ⟨5987526334878055380112591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31933473786016295360600485 5987526334878055380112591)
      ·
        refine ⟨8981289502317083070168887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5987526334878055380112591 8981289502317083070168887)
        ·
          refine ⟨13471934253475624605253331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8981289502317083070168887 13471934253475624605253331)
          ·
            refine ⟨20207901380213436907879997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13471934253475624605253331 20207901380213436907879997)
            ·
              refine ⟨7577963017580038840454999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20207901380213436907879997 7577963017580038840454999)
              ·
                refine ⟨11366944526370058260682499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7577963017580038840454999 11366944526370058260682499)
                ·
                  refine ⟨17050416789555087391023749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11366944526370058260682499 17050416789555087391023749)
                  ·
                    refine ⟨3196953148041578885816953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17050416789555087391023749 3196953148041578885816953)
                    ·
                      refine ⟨2397714861031184164362715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196953148041578885816953 2397714861031184164362715)
                      ·
                        rfl

theorem cell23_4669533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_4669533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669533 prefixEnd_4669533 := by exact prefixLift 4669533
  have htrace : WordTrace (prefixWord ++ tailWord_4669533) baseStart_4669533 baseEnd_4669533 := by
    simpa [prefixWord, tailWord_4669533, baseEnd_4669533] using wordTrace_append hprefix tailTrace_4669533
  have hstable : (prefixWord ++ tailWord_4669533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669533).length < 2 ^ (prefixWord ++ tailWord_4669533).sum := by decide
  have hdescent : baseEnd_4669533 < baseStart_4669533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669552 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 1, 7]
def baseStart_4669552 : Nat := 118140960795 + 4669552 * 2 ^ 59
def prefixEnd_4669552 : Nat := 4983230072969 + 3 ^ 40 * 4669552 * 2
def baseEnd_4669552 : Nat := 799241539054539863341709

theorem tailTrace_4669552 : CollatzResearch.WordTrace tailWord_4669552 prefixEnd_4669552 799241539054539863341709 := by
  unfold tailWord_4669552
  simp only [CollatzResearch.WordTrace]
  refine ⟨85156276589509037417405455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113541702119345383223207273 85156276589509037417405455)
  ·
    refine ⟨127734414884263556126108183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85156276589509037417405455 127734414884263556126108183)
    ·
      refine ⟨191601622326395334189162275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127734414884263556126108183 191601622326395334189162275)
      ·
        refine ⟨287402433489593001283743413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191601622326395334189162275 287402433489593001283743413)
        ·
          refine ⟨26943978139649343870350945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 287402433489593001283743413 26943978139649343870350945)
          ·
            refine ⟨20207983604737007902763209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26943978139649343870350945 20207983604737007902763209)
            ·
              refine ⟨15155987703552755927072407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20207983604737007902763209 15155987703552755927072407)
              ·
                refine ⟨22733981555329133890608611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15155987703552755927072407 22733981555329133890608611)
                ·
                  refine ⟨34100972332993700835912917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22733981555329133890608611 34100972332993700835912917)
                  ·
                    refine ⟨799241539054539863341709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34100972332993700835912917 799241539054539863341709)
                    ·
                      rfl

theorem cell23_4669552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_4669552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669552 prefixEnd_4669552 := by exact prefixLift 4669552
  have htrace : WordTrace (prefixWord ++ tailWord_4669552) baseStart_4669552 baseEnd_4669552 := by
    simpa [prefixWord, tailWord_4669552, baseEnd_4669552] using wordTrace_append hprefix tailTrace_4669552
  have hstable : (prefixWord ++ tailWord_4669552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669552).length < 2 ^ (prefixWord ++ tailWord_4669552).sum := by decide
  have hdescent : baseEnd_4669552 < baseStart_4669552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669589 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 1, 6, 2]
def baseStart_4669589 : Nat := 118140960795 + 4669589 * 2 ^ 59
def prefixEnd_4669589 : Nat := 4983230072969 + 3 ^ 40 * 4669589 * 2
def baseEnd_4669589 : Nat := 2397743615947835945262457

theorem tailTrace_4669589 : CollatzResearch.WordTrace tailWord_4669589 prefixEnd_4669589 2397743615947835945262457 := by
  unfold tailWord_4669589
  simp only [CollatzResearch.WordTrace]
  refine ⟨170313902679884030153907821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113542601786589353435938547 170313902679884030153907821)
  ·
    refine ⟨63867713504956511307715433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170313902679884030153907821 63867713504956511307715433)
    ·
      refine ⟨47900785128717383480786575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63867713504956511307715433 47900785128717383480786575)
      ·
        refine ⟨71851177693076075221179863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47900785128717383480786575 71851177693076075221179863)
        ·
          refine ⟨107776766539614112831769795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71851177693076075221179863 107776766539614112831769795)
          ·
            refine ⟨161665149809421169247654693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107776766539614112831769795 161665149809421169247654693)
            ·
              refine ⟨30312215589266469233935255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161665149809421169247654693 30312215589266469233935255)
              ·
                refine ⟨45468323383899703850902883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30312215589266469233935255 45468323383899703850902883)
                ·
                  refine ⟨68202485075849555776354325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45468323383899703850902883 68202485075849555776354325)
                  ·
                    refine ⟨3196991487930447927016609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68202485075849555776354325 3196991487930447927016609)
                    ·
                      refine ⟨2397743615947835945262457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3196991487930447927016609 2397743615947835945262457)
                      ·
                        rfl

theorem cell23_4669589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_4669589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669589 prefixEnd_4669589 := by exact prefixLift 4669589
  have htrace : WordTrace (prefixWord ++ tailWord_4669589) baseStart_4669589 baseEnd_4669589 := by
    simpa [prefixWord, tailWord_4669589, baseEnd_4669589] using wordTrace_append hprefix tailTrace_4669589
  have hstable : (prefixWord ++ tailWord_4669589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669589).length < 2 ^ (prefixWord ++ tailWord_4669589).sum := by decide
  have hdescent : baseEnd_4669589 < baseStart_4669589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669656 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 5, 1, 3]
def baseStart_4669656 : Nat := 118140960795 + 4669656 * 2 ^ 59
def prefixEnd_4669656 : Nat := 4983230072969 + 3 ^ 40 * 4669656 * 2
def baseEnd_4669656 : Nat := 2397778019151687183124649

theorem tailTrace_4669656 : CollatzResearch.WordTrace tailWord_4669656 prefixEnd_4669656 2397778019151687183124649 := by
  unfold tailWord_4669656
  simp only [CollatzResearch.WordTrace]
  refine ⟨85158173185320650298298411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113544230913760867064397881 85158173185320650298298411)
  ·
    refine ⟨127737259777980975447447617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85158173185320650298298411 127737259777980975447447617)
    ·
      refine ⟨95802944833485731585585713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127737259777980975447447617 95802944833485731585585713)
      ·
        refine ⟨71852208625114298689189285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95802944833485731585585713 71852208625114298689189285)
        ·
          refine ⟨13472289117208931004222991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71852208625114298689189285 13472289117208931004222991)
          ·
            refine ⟨20208433675813396506334487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13472289117208931004222991 20208433675813396506334487)
            ·
              refine ⟨30312650513720094759501731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20208433675813396506334487 30312650513720094759501731)
              ·
                refine ⟨45468975770580142139252597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30312650513720094759501731 45468975770580142139252597)
                ·
                  refine ⟨4262716478491888325554931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45468975770580142139252597 4262716478491888325554931)
                  ·
                    refine ⟨6394074717737832488332397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4262716478491888325554931 6394074717737832488332397)
                    ·
                      refine ⟨2397778019151687183124649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6394074717737832488332397 2397778019151687183124649)
                      ·
                        rfl

theorem cell23_4669656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_4669656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669656 prefixEnd_4669656 := by exact prefixLift 4669656
  have htrace : WordTrace (prefixWord ++ tailWord_4669656) baseStart_4669656 baseEnd_4669656 := by
    simpa [prefixWord, tailWord_4669656, baseEnd_4669656] using wordTrace_append hprefix tailTrace_4669656
  have hstable : (prefixWord ++ tailWord_4669656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669656).length < 2 ^ (prefixWord ++ tailWord_4669656).sum := by decide
  have hdescent : baseEnd_4669656 < baseStart_4669656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669699 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 5]
def baseStart_4669699 : Nat := 118140960795 + 4669699 * 2 ^ 59
def prefixEnd_4669699 : Nat := 4983230072969 + 3 ^ 40 * 4669699 * 2
def baseEnd_4669699 : Nat := 2397800098819830514886951

theorem tailTrace_4669699 : CollatzResearch.WordTrace tailWord_4669699 prefixEnd_4669699 2397800098819830514886951 := by
  unfold tailWord_4669699
  simp only [CollatzResearch.WordTrace]
  refine ⟨170317914709485518940412151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113545276472990345960274767 170317914709485518940412151)
  ·
    refine ⟨255476872064228278410618227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170317914709485518940412151 255476872064228278410618227)
    ·
      refine ⟨383215308096342417615927341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255476872064228278410618227 383215308096342417615927341)
      ·
        refine ⟨143705740536128406605972753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383215308096342417615927341 143705740536128406605972753)
        ·
          refine ⟨107779305402096304954479565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143705740536128406605972753 107779305402096304954479565)
          ·
            refine ⟨40417239525786114357929837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107779305402096304954479565 40417239525786114357929837)
            ·
              refine ⟨15156464822169792884223689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40417239525786114357929837 15156464822169792884223689)
              ·
                refine ⟨11367348616627344663167767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15156464822169792884223689 11367348616627344663167767)
                ·
                  refine ⟨17051022924941016994751651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11367348616627344663167767 17051022924941016994751651)
                  ·
                    refine ⟨25576534387411525492127477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17051022924941016994751651 25576534387411525492127477)
                    ·
                      refine ⟨2397800098819830514886951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25576534387411525492127477 2397800098819830514886951)
                      ·
                        rfl

theorem cell23_4669699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_4669699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669699 prefixEnd_4669699 := by exact prefixLift 4669699
  have htrace : WordTrace (prefixWord ++ tailWord_4669699) baseStart_4669699 baseEnd_4669699 := by
    simpa [prefixWord, tailWord_4669699, baseEnd_4669699] using wordTrace_append hprefix tailTrace_4669699
  have hstable : (prefixWord ++ tailWord_4669699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669699).length < 2 ^ (prefixWord ++ tailWord_4669699).sum := by decide
  have hdescent : baseEnd_4669699 < baseStart_4669699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669706 : List Nat := [3, 1, 2, 2, 1, 1, 2, 5, 2, 4]
def baseStart_4669706 : Nat := 118140960795 + 4669706 * 2 ^ 59
def prefixEnd_4669706 : Nat := 4983230072969 + 3 ^ 40 * 4669706 * 2
def baseEnd_4669706 : Nat := 799267897728137329166473

theorem tailTrace_4669706 : CollatzResearch.WordTrace tailWord_4669706 prefixEnd_4669706 799267897728137329166473 := by
  unfold tailWord_4669706
  simp only [CollatzResearch.WordTrace]
  refine ⟨42579542505115039783979243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113545446680306772757277981 42579542505115039783979243)
  ·
    refine ⟨63869313757672559675968865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42579542505115039783979243 63869313757672559675968865)
    ·
      refine ⟨47901985318254419756976649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63869313757672559675968865 47901985318254419756976649)
      ·
        refine ⟨35926488988690814817732487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47901985318254419756976649 35926488988690814817732487)
        ·
          refine ⟨53889733483036222226598731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35926488988690814817732487 53889733483036222226598731)
          ·
            refine ⟨80834600224554333339898097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53889733483036222226598731 80834600224554333339898097)
            ·
              refine ⟨60625950168415750004923573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80834600224554333339898097 60625950168415750004923573)
              ·
                refine ⟨5683682828288976562961585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60625950168415750004923573 5683682828288976562961585)
                ·
                  refine ⟨4262762121216732422221189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5683682828288976562961585 4262762121216732422221189)
                  ·
                    refine ⟨799267897728137329166473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4262762121216732422221189 799267897728137329166473)
                    ·
                      rfl

theorem cell23_4669706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_4669706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669706 prefixEnd_4669706 := by exact prefixLift 4669706
  have htrace : WordTrace (prefixWord ++ tailWord_4669706) baseStart_4669706 baseEnd_4669706 := by
    simpa [prefixWord, tailWord_4669706, baseEnd_4669706] using wordTrace_append hprefix tailTrace_4669706
  have hstable : (prefixWord ++ tailWord_4669706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669706).length < 2 ^ (prefixWord ++ tailWord_4669706).sum := by decide
  have hdescent : baseEnd_4669706 < baseStart_4669706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669712 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_4669712 : Nat := 118140960795 + 4669712 * 2 ^ 59
def prefixEnd_4669712 : Nat := 4983230072969 + 3 ^ 40 * 4669712 * 2
def baseEnd_4669712 : Nat := 2397806774068338964024391

theorem tailTrace_4669712 : CollatzResearch.WordTrace tailWord_4669712 prefixEnd_4669712 2397806774068338964024391 := by
  unfold tailWord_4669712
  simp only [CollatzResearch.WordTrace]
  refine ⟨85159194429219211080317695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113545592572292281440423593 85159194429219211080317695)
  ·
    refine ⟨127738791643828816620476543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85159194429219211080317695 127738791643828816620476543)
    ·
      refine ⟨191608187465743224930714815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127738791643828816620476543 191608187465743224930714815)
      ·
        refine ⟨287412281198614837396072223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191608187465743224930714815 287412281198614837396072223)
        ·
          refine ⟨431118421797922256094108335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287412281198614837396072223 431118421797922256094108335)
          ·
            refine ⟨646677632696883384141162503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431118421797922256094108335 646677632696883384141162503)
            ·
              refine ⟨970016449045325076211743755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646677632696883384141162503 970016449045325076211743755)
              ·
                refine ⟨1455024673567987614317615633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970016449045325076211743755 1455024673567987614317615633)
                ·
                  refine ⟨1091268505175990710738211725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1455024673567987614317615633 1091268505175990710738211725)
                  ·
                    refine ⟨409225689440996516526829397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1091268505175990710738211725 409225689440996516526829397)
                    ·
                      refine ⟨2397806774068338964024391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 409225689440996516526829397 2397806774068338964024391)
                      ·
                        rfl

theorem cell23_4669712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_4669712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669712 prefixEnd_4669712 := by exact prefixLift 4669712
  have htrace : WordTrace (prefixWord ++ tailWord_4669712) baseStart_4669712 baseEnd_4669712 := by
    simpa [prefixWord, tailWord_4669712, baseEnd_4669712] using wordTrace_append hprefix tailTrace_4669712
  have hstable : (prefixWord ++ tailWord_4669712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669712).length < 2 ^ (prefixWord ++ tailWord_4669712).sum := by decide
  have hdescent : baseEnd_4669712 < baseStart_4669712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669713 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 3, 2, 2]
def baseStart_4669713 : Nat := 118140960795 + 4669713 * 2 ^ 59
def prefixEnd_4669713 : Nat := 4983230072969 + 3 ^ 40 * 4669713 * 2
def baseEnd_4669713 : Nat := 2397807287548993460111887

theorem tailTrace_4669713 : CollatzResearch.WordTrace tailWord_4669713 prefixEnd_4669713 2397807287548993460111887 := by
  unfold tailWord_4669713
  simp only [CollatzResearch.WordTrace]
  refine ⟨170318425331434799331421793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113545616887623199554281195 170318425331434799331421793)
  ·
    refine ⟨127738818998576099498566345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170318425331434799331421793 127738818998576099498566345)
    ·
      refine ⟨95804114248932074623924759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127738818998576099498566345 95804114248932074623924759)
      ·
        refine ⟨143706171373398111935887139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95804114248932074623924759 143706171373398111935887139)
        ·
          refine ⟨215559257060097167903830709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143706171373398111935887139 215559257060097167903830709)
          ·
            refine ⟨20208680349384109490984129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 215559257060097167903830709 20208680349384109490984129)
            ·
              refine ⟨15156510262038082118238097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20208680349384109490984129 15156510262038082118238097)
              ·
                refine ⟨11367382696528561588678573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15156510262038082118238097 11367382696528561588678573)
                ·
                  refine ⟨4262768511198210595754465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11367382696528561588678573 4262768511198210595754465)
                  ·
                    refine ⟨3197076383398657946815849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4262768511198210595754465 3197076383398657946815849)
                    ·
                      refine ⟨2397807287548993460111887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197076383398657946815849 2397807287548993460111887)
                      ·
                        rfl

theorem cell23_4669713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 2, 2].length) (baseStart_4669713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669713 prefixEnd_4669713 := by exact prefixLift 4669713
  have htrace : WordTrace (prefixWord ++ tailWord_4669713) baseStart_4669713 baseEnd_4669713 := by
    simpa [prefixWord, tailWord_4669713, baseEnd_4669713] using wordTrace_append hprefix tailTrace_4669713
  have hstable : (prefixWord ++ tailWord_4669713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669713).length < 2 ^ (prefixWord ++ tailWord_4669713).sum := by decide
  have hdescent : baseEnd_4669713 < baseStart_4669713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669719 : List Nat := [1, 1, 3, 4, 1, 3, 1, 9]
def baseStart_4669719 : Nat := 118140960795 + 4669719 * 2 ^ 59
def prefixEnd_4669719 : Nat := 4983230072969 + 3 ^ 40 * 4669719 * 2
def baseEnd_4669719 : Nat := 88807791423441497653217

theorem tailTrace_4669719 : CollatzResearch.WordTrace tailWord_4669719 prefixEnd_4669719 88807791423441497653217 := by
  unfold tailWord_4669719
  simp only [CollatzResearch.WordTrace]
  refine ⟨170318644169413062356140211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113545762779608708237426807 170318644169413062356140211)
  ·
    refine ⟨255477966254119593534210317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170318644169413062356140211 255477966254119593534210317)
    ·
      refine ⟨95804237345294847575328869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255477966254119593534210317 95804237345294847575328869)
      ·
        refine ⟨17963294502242783920374163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95804237345294847575328869 17963294502242783920374163)
        ·
          refine ⟨26944941753364175880561245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17963294502242783920374163 26944941753364175880561245)
          ·
            refine ⟨10104353157511565955210467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26944941753364175880561245 10104353157511565955210467)
            ·
              refine ⟨15156529736267348932815701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10104353157511565955210467 15156529736267348932815701)
              ·
                refine ⟨88807791423441497653217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15156529736267348932815701 88807791423441497653217)
                ·
                  rfl

theorem cell23_4669719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 9].length) (baseStart_4669719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669719 prefixEnd_4669719 := by exact prefixLift 4669719
  have htrace : WordTrace (prefixWord ++ tailWord_4669719) baseStart_4669719 baseEnd_4669719 := by
    simpa [prefixWord, tailWord_4669719, baseEnd_4669719] using wordTrace_append hprefix tailTrace_4669719
  have hstable : (prefixWord ++ tailWord_4669719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669719).length < 2 ^ (prefixWord ++ tailWord_4669719).sum := by decide
  have hdescent : baseEnd_4669719 < baseStart_4669719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669736 : List Nat := [2, 1, 5, 1, 3, 2, 9]
def baseStart_4669736 : Nat := 118140960795 + 4669736 * 2 ^ 59
def prefixEnd_4669736 : Nat := 4983230072969 + 3 ^ 40 * 4669736 * 2
def baseEnd_4669736 : Nat := 29602704908691936668201

theorem tailTrace_4669736 : CollatzResearch.WordTrace tailWord_4669736 prefixEnd_4669736 29602704908691936668201 := by
  unfold tailWord_4669736
  simp only [CollatzResearch.WordTrace]
  refine ⟨85159632105175737129754531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113546176140234316173006041 85159632105175737129754531)
  ·
    refine ⟨127739448157763605694631797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85159632105175737129754531 127739448157763605694631797)
    ·
      refine ⟨11975573264790338033871731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127739448157763605694631797 11975573264790338033871731)
      ·
        refine ⟨17963359897185507050807597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11975573264790338033871731 17963359897185507050807597)
        ·
          refine ⟨6736259961444565144052849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17963359897185507050807597 6736259961444565144052849)
          ·
            refine ⟨5052194971083423858039637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6736259961444565144052849 5052194971083423858039637)
            ·
              refine ⟨29602704908691936668201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5052194971083423858039637 29602704908691936668201)
              ·
                rfl

theorem cell23_4669736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 9].length) (baseStart_4669736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669736 prefixEnd_4669736 := by exact prefixLift 4669736
  have htrace : WordTrace (prefixWord ++ tailWord_4669736) baseStart_4669736 baseEnd_4669736 := by
    simpa [prefixWord, tailWord_4669736, baseEnd_4669736] using wordTrace_append hprefix tailTrace_4669736
  have hstable : (prefixWord ++ tailWord_4669736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669736).length < 2 ^ (prefixWord ++ tailWord_4669736).sum := by decide
  have hdescent : baseEnd_4669736 < baseStart_4669736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669747 : List Nat := [1, 1, 1, 2, 5, 1, 5, 2, 1, 2, 2]
def baseStart_4669747 : Nat := 118140960795 + 4669747 * 2 ^ 59
def prefixEnd_4669747 : Nat := 4983230072969 + 3 ^ 40 * 4669747 * 2
def baseEnd_4669747 : Nat := 2397824745891246327086731

theorem tailTrace_4669747 : CollatzResearch.WordTrace tailWord_4669747 prefixEnd_4669747 2397824745891246327086731 := by
  unfold tailWord_4669747
  simp only [CollatzResearch.WordTrace]
  refine ⟨170319665413311623138159495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113546443608874415425439663 170319665413311623138159495)
  ·
    refine ⟨255479498119967434707239243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170319665413311623138159495 255479498119967434707239243)
    ·
      refine ⟨383219247179951152060858865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255479498119967434707239243 383219247179951152060858865)
      ·
        refine ⟨287414435384963364045644149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383219247179951152060858865 287414435384963364045644149)
        ·
          refine ⟨26945103317340315379279139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 287414435384963364045644149 26945103317340315379279139)
          ·
            refine ⟨40417654976010473068918709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26945103317340315379279139 40417654976010473068918709)
            ·
              refine ⟨3789155154000981850211129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40417654976010473068918709 3789155154000981850211129)
              ·
                refine ⟨2841866365500736387658347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3789155154000981850211129 2841866365500736387658347)
                ·
                  refine ⟨4262799548251104581487521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841866365500736387658347 4262799548251104581487521)
                  ·
                    refine ⟨3197099661188328436115641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4262799548251104581487521 3197099661188328436115641)
                    ·
                      refine ⟨2397824745891246327086731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197099661188328436115641 2397824745891246327086731)
                      ·
                        rfl

theorem cell23_4669747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 1, 2, 2].length) (baseStart_4669747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669747 prefixEnd_4669747 := by exact prefixLift 4669747
  have htrace : WordTrace (prefixWord ++ tailWord_4669747) baseStart_4669747 baseEnd_4669747 := by
    simpa [prefixWord, tailWord_4669747, baseEnd_4669747] using wordTrace_append hprefix tailTrace_4669747
  have hstable : (prefixWord ++ tailWord_4669747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669747).length < 2 ^ (prefixWord ++ tailWord_4669747).sum := by decide
  have hdescent : baseEnd_4669747 < baseStart_4669747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669749 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_4669749 : Nat := 118140960795 + 4669749 * 2 ^ 59
def prefixEnd_4669749 : Nat := 4983230072969 + 3 ^ 40 * 4669749 * 2
def baseEnd_4669749 : Nat := 799275257617518439753907

theorem tailTrace_4669749 : CollatzResearch.WordTrace tailWord_4669749 prefixEnd_4669749 799275257617518439753907 := by
  unfold tailWord_4669749
  simp only [CollatzResearch.WordTrace]
  refine ⟨170319738359304377479732301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113546492239536251653154867 170319738359304377479732301)
  ·
    refine ⟨63869901884739141554899613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170319738359304377479732301 63869901884739141554899613)
    ·
      refine ⟨23951213206777178083087355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63869901884739141554899613 23951213206777178083087355)
      ·
        refine ⟨35926819810165767124631033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23951213206777178083087355 35926819810165767124631033)
        ·
          refine ⟨26945114857624325343473275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35926819810165767124631033 26945114857624325343473275)
          ·
            refine ⟨40417672286436488015209913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26945114857624325343473275 40417672286436488015209913)
            ·
              refine ⟨30313254214827366011407435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40417672286436488015209913 30313254214827366011407435)
              ·
                refine ⟨45469881322241049017111153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30313254214827366011407435 45469881322241049017111153)
                ·
                  refine ⟨34102410991680786762833365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45469881322241049017111153 34102410991680786762833365)
                  ·
                    refine ⟨799275257617518439753907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34102410991680786762833365 799275257617518439753907)
                    ·
                      rfl

theorem cell23_4669749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_4669749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669749 prefixEnd_4669749 := by exact prefixLift 4669749
  have htrace : WordTrace (prefixWord ++ tailWord_4669749) baseStart_4669749 baseEnd_4669749 := by
    simpa [prefixWord, tailWord_4669749, baseEnd_4669749] using wordTrace_append hprefix tailTrace_4669749
  have hstable : (prefixWord ++ tailWord_4669749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669749).length < 2 ^ (prefixWord ++ tailWord_4669749).sum := by decide
  have hdescent : baseEnd_4669749 < baseStart_4669749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669809 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 7]
def baseStart_4669809 : Nat := 118140960795 + 4669809 * 2 ^ 59
def prefixEnd_4669809 : Nat := 4983230072969 + 3 ^ 40 * 4669809 * 2
def baseEnd_4669809 : Nat := 266428509076869453834605

theorem tailTrace_4669809 : CollatzResearch.WordTrace tailWord_4669809 prefixEnd_4669809 266428509076869453834605 := by
  unfold tailWord_4669809
  simp only [CollatzResearch.WordTrace]
  refine ⟨170321926739087007726916481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113547951159391338484610987 170321926739087007726916481)
  ·
    refine ⟨127741445054315255795187361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170321926739087007726916481 127741445054315255795187361)
    ·
      refine ⟨95806083790736441846390521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127741445054315255795187361 95806083790736441846390521)
      ·
        refine ⟨71854562843052331384792891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95806083790736441846390521 71854562843052331384792891)
        ·
          refine ⟨107781844264578497077189337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71854562843052331384792891 107781844264578497077189337)
          ·
            refine ⟨80836383198433872807892003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107781844264578497077189337 80836383198433872807892003)
            ·
              refine ⟨121254574797650809211838005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80836383198433872807892003 121254574797650809211838005)
              ·
                refine ⟨11367616387279763363609813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121254574797650809211838005 11367616387279763363609813)
                ·
                  refine ⟨266428509076869453834605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11367616387279763363609813 266428509076869453834605)
                  ·
                    rfl

theorem cell23_4669809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 7].length) (baseStart_4669809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669809 prefixEnd_4669809 := by exact prefixLift 4669809
  have htrace : WordTrace (prefixWord ++ tailWord_4669809) baseStart_4669809 baseEnd_4669809 := by
    simpa [prefixWord, tailWord_4669809, baseEnd_4669809] using wordTrace_append hprefix tailTrace_4669809
  have hstable : (prefixWord ++ tailWord_4669809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669809).length < 2 ^ (prefixWord ++ tailWord_4669809).sum := by decide
  have hdescent : baseEnd_4669809 < baseStart_4669809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669854 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_4669854 : Nat := 118140960795 + 4669854 * 2 ^ 59
def prefixEnd_4669854 : Nat := 4983230072969 + 3 ^ 40 * 4669854 * 2
def baseEnd_4669854 : Nat := 2397879688321277408448739

theorem tailTrace_4669854 : CollatzResearch.WordTrace tailWord_4669854 prefixEnd_4669854 2397879688321277408448739 := by
  unfold tailWord_4669854
  simp only [CollatzResearch.WordTrace]
  refine ⟨21290446002990497551538077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113549045349282653608203077 21290446002990497551538077)
  ·
    refine ⟨7983917251121436581826779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21290446002990497551538077 7983917251121436581826779)
    ·
      refine ⟨11975875876682154872740169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7983917251121436581826779 11975875876682154872740169)
      ·
        refine ⟨8981906907511616154555127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11975875876682154872740169 8981906907511616154555127)
        ·
          refine ⟨13472860361267424231832691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8981906907511616154555127 13472860361267424231832691)
          ·
            refine ⟨20209290541901136347749037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13472860361267424231832691 20209290541901136347749037)
            ·
              refine ⟨7578483953212926130405889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20209290541901136347749037 7578483953212926130405889)
              ·
                refine ⟨5683862964909694597804417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7578483953212926130405889 5683862964909694597804417)
                ·
                  refine ⟨4262897223682270948353313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5683862964909694597804417 4262897223682270948353313)
                  ·
                    refine ⟨3197172917761703211264985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4262897223682270948353313 3197172917761703211264985)
                    ·
                      refine ⟨2397879688321277408448739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197172917761703211264985 2397879688321277408448739)
                      ·
                        rfl

theorem cell23_4669854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_4669854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669854 prefixEnd_4669854 := by exact prefixLift 4669854
  have htrace : WordTrace (prefixWord ++ tailWord_4669854) baseStart_4669854 baseEnd_4669854 := by
    simpa [prefixWord, tailWord_4669854, baseEnd_4669854] using wordTrace_append hprefix tailTrace_4669854
  have hstable : (prefixWord ++ tailWord_4669854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669854).length < 2 ^ (prefixWord ++ tailWord_4669854).sum := by decide
  have hdescent : baseEnd_4669854 < baseStart_4669854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669910 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_4669910 : Nat := 118140960795 + 4669910 * 2 ^ 59
def prefixEnd_4669910 : Nat := 4983230072969 + 3 ^ 40 * 4669910 * 2
def baseEnd_4669910 : Nat := 2397908443237929189348481

theorem tailTrace_4669910 : CollatzResearch.WordTrace tailWord_4669910 prefixEnd_4669910 2397908443237929189348481 := by
  unfold tailWord_4669910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10645350656982568873521449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113550407007814067984228789 10645350656982568873521449)
  ·
    refine ⟨7984012992736926655141087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10645350656982568873521449 7984012992736926655141087)
    ·
      refine ⟨11976019489105389982711631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7984012992736926655141087 11976019489105389982711631)
      ·
        refine ⟨17964029233658084974067447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11976019489105389982711631 17964029233658084974067447)
        ·
          refine ⟨26946043850487127461101171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17964029233658084974067447 26946043850487127461101171)
          ·
            refine ⟨40419065775730691191651757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26946043850487127461101171 40419065775730691191651757)
            ·
              refine ⟨15157149665899009196869409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40419065775730691191651757 15157149665899009196869409)
              ·
                refine ⟨11367862249424256897652057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15157149665899009196869409 11367862249424256897652057)
                ·
                  refine ⟨8525896687068192673239043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11367862249424256897652057 8525896687068192673239043)
                  ·
                    refine ⟨12788845030602289009858565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8525896687068192673239043 12788845030602289009858565)
                    ·
                      refine ⟨2397908443237929189348481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12788845030602289009858565 2397908443237929189348481)
                      ·
                        rfl

theorem cell23_4669910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_4669910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669910 prefixEnd_4669910 := by exact prefixLift 4669910
  have htrace : WordTrace (prefixWord ++ tailWord_4669910) baseStart_4669910 baseEnd_4669910 := by
    simpa [prefixWord, tailWord_4669910, baseEnd_4669910] using wordTrace_append hprefix tailTrace_4669910
  have hstable : (prefixWord ++ tailWord_4669910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669910).length < 2 ^ (prefixWord ++ tailWord_4669910).sum := by decide
  have hdescent : baseEnd_4669910 < baseStart_4669910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669913 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 2, 2, 3]
def baseStart_4669913 : Nat := 118140960795 + 4669913 * 2 ^ 59
def prefixEnd_4669913 : Nat := 4983230072969 + 3 ^ 40 * 4669913 * 2
def baseEnd_4669913 : Nat := 2397909983679892677610967

theorem tailTrace_4669913 : CollatzResearch.WordTrace tailWord_4669913 prefixEnd_4669913 2397909983679892677610967 := by
  unfold tailWord_4669913
  simp only [CollatzResearch.WordTrace]
  refine ⟨170325719930710233488702393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113550479953806822325801595 170325719930710233488702393)
  ·
    refine ⟨127744289948032675116526795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170325719930710233488702393 127744289948032675116526795)
    ·
      refine ⟨191616434922049012674790193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127744289948032675116526795 191616434922049012674790193)
      ·
        refine ⟨143712326191536759506092645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191616434922049012674790193 143712326191536759506092645)
        ·
          refine ⟨26946061160913142407392371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143712326191536759506092645 26946061160913142407392371)
          ·
            refine ⟨40419091741369713611088557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26946061160913142407392371 40419091741369713611088557)
            ·
              refine ⟨15157159403013642604158209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40419091741369713611088557 15157159403013642604158209)
              ·
                refine ⟨11367869552260231953118657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15157159403013642604158209 11367869552260231953118657)
                ·
                  refine ⟨8525902164195173964838993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11367869552260231953118657 8525902164195173964838993)
                  ·
                    refine ⟨6394426623146380473629245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8525902164195173964838993 6394426623146380473629245)
                    ·
                      refine ⟨2397909983679892677610967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6394426623146380473629245 2397909983679892677610967)
                      ·
                        rfl

theorem cell23_4669913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_4669913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669913 prefixEnd_4669913 := by exact prefixLift 4669913
  have htrace : WordTrace (prefixWord ++ tailWord_4669913) baseStart_4669913 baseEnd_4669913 := by
    simpa [prefixWord, tailWord_4669913, baseEnd_4669913] using wordTrace_append hprefix tailTrace_4669913
  have hstable : (prefixWord ++ tailWord_4669913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669913).length < 2 ^ (prefixWord ++ tailWord_4669913).sum := by decide
  have hdescent : baseEnd_4669913 < baseStart_4669913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669983 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 2, 6, 2]
def baseStart_4669983 : Nat := 118140960795 + 4669983 * 2 ^ 59
def prefixEnd_4669983 : Nat := 4983230072969 + 3 ^ 40 * 4669983 * 2
def baseEnd_4669983 : Nat := 2397945927325707403735645

theorem tailTrace_4669983 : CollatzResearch.WordTrace tailWord_4669983 prefixEnd_4669983 2397945927325707403735645 := by
  unfold tailWord_4669983
  simp only [CollatzResearch.WordTrace]
  refine ⟨170328273040456635443750603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113552182026971090295833735 170328273040456635443750603)
  ·
    refine ⟨255492409560684953165625905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170328273040456635443750603 255492409560684953165625905)
    ·
      refine ⟨191619307170513714874219429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255492409560684953165625905 191619307170513714874219429)
      ·
        refine ⟨35928620094471321538916143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191619307170513714874219429 35928620094471321538916143)
        ·
          refine ⟨53892930141706982308374215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35928620094471321538916143 53892930141706982308374215)
          ·
            refine ⟨80839395212560473462561323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53892930141706982308374215 80839395212560473462561323)
            ·
              refine ⟨121259092818840710193841985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80839395212560473462561323 121259092818840710193841985)
              ·
                refine ⟨90944319614130532645381489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121259092818840710193841985 90944319614130532645381489)
                ·
                  refine ⟨68208239710597899484036117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90944319614130532645381489 68208239710597899484036117)
                  ·
                    refine ⟨3197261236434276538314193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68208239710597899484036117 3197261236434276538314193)
                    ·
                      refine ⟨2397945927325707403735645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197261236434276538314193 2397945927325707403735645)
                      ·
                        rfl

theorem cell23_4669983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_4669983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669983 prefixEnd_4669983 := by exact prefixLift 4669983
  have htrace : WordTrace (prefixWord ++ tailWord_4669983) baseStart_4669983 baseEnd_4669983 := by
    simpa [prefixWord, tailWord_4669983, baseEnd_4669983] using wordTrace_append hprefix tailTrace_4669983
  have hstable : (prefixWord ++ tailWord_4669983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669983).length < 2 ^ (prefixWord ++ tailWord_4669983).sum := by decide
  have hdescent : baseEnd_4669983 < baseStart_4669983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4669996 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_4669996 : Nat := 118140960795 + 4669996 * 2 ^ 59
def prefixEnd_4669996 : Nat := 4983230072969 + 3 ^ 40 * 4669996 * 2
def baseEnd_4669996 : Nat := 2397952602574215852873085

theorem tailTrace_4669996 : CollatzResearch.WordTrace tailWord_4669996 prefixEnd_4669996 2397952602574215852873085 := by
  unfold tailWord_4669996
  simp only [CollatzResearch.WordTrace]
  refine ⟨85164373594704769331986921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113552498126273025775982561 85164373594704769331986921)
  ·
    refine ⟨63873280196028576998990191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85164373594704769331986921 63873280196028576998990191)
    ·
      refine ⟨95809920294042865498485287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63873280196028576998990191 95809920294042865498485287)
      ·
        refine ⟨143714880441064298247727931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95809920294042865498485287 143714880441064298247727931)
        ·
          refine ⟨215572320661596447371591897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143714880441064298247727931 215572320661596447371591897)
          ·
            refine ⟨161679240496197335528693923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215572320661596447371591897 161679240496197335528693923)
            ·
              refine ⟨242518860744296003293040885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161679240496197335528693923 242518860744296003293040885)
              ·
                refine ⟨22736143194777750308722583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 242518860744296003293040885 22736143194777750308722583)
                ·
                  refine ⟨34104214792166625463083875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22736143194777750308722583 34104214792166625463083875)
                  ·
                    refine ⟨51156322188249938194625813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34104214792166625463083875 51156322188249938194625813)
                    ·
                      refine ⟨2397952602574215852873085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51156322188249938194625813 2397952602574215852873085)
                      ·
                        rfl

theorem cell23_4669996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_4669996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4669996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4669996 prefixEnd_4669996 := by exact prefixLift 4669996
  have htrace : WordTrace (prefixWord ++ tailWord_4669996) baseStart_4669996 baseEnd_4669996 := by
    simpa [prefixWord, tailWord_4669996, baseEnd_4669996] using wordTrace_append hprefix tailTrace_4669996
  have hstable : (prefixWord ++ tailWord_4669996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4669996).length < 2 ^ (prefixWord ++ tailWord_4669996).sum := by decide
  have hdescent : baseEnd_4669996 < baseStart_4669996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4669996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670000 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 5, 2, 2]
def baseStart_4670000 : Nat := 118140960795 + 4670000 * 2 ^ 59
def prefixEnd_4670000 : Nat := 4983230072969 + 3 ^ 40 * 4670000 * 2
def baseEnd_4670000 : Nat := 2397954656496833837223067

theorem tailTrace_4670000 : CollatzResearch.WordTrace tailWord_4670000 prefixEnd_4670000 2397954656496833837223067 := by
  unfold tailWord_4670000
  simp only [CollatzResearch.WordTrace]
  refine ⟨85164446540697523673559727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113552595387596698231412969 85164446540697523673559727)
  ·
    refine ⟨127746669811046285510339591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85164446540697523673559727 127746669811046285510339591)
    ·
      refine ⟨191620004716569428265509387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127746669811046285510339591 191620004716569428265509387)
      ·
        refine ⟨287430007074854142398264081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191620004716569428265509387 287430007074854142398264081)
        ·
          refine ⟨215572505306140606798698061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287430007074854142398264081 215572505306140606798698061)
          ·
            refine ⟨80839689489802727549511773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215572505306140606798698061 80839689489802727549511773)
            ·
              refine ⟨30314883558676022831066915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80839689489802727549511773 30314883558676022831066915)
              ·
                refine ⟨45472325338014034246600373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30314883558676022831066915 45472325338014034246600373)
                ·
                  refine ⟨4263030500438815710618785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45472325338014034246600373 4263030500438815710618785)
                  ·
                    refine ⟨3197272875329111782964089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4263030500438815710618785 3197272875329111782964089)
                    ·
                      refine ⟨2397954656496833837223067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197272875329111782964089 2397954656496833837223067)
                      ·
                        rfl

theorem cell23_4670000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5, 2, 2].length) (baseStart_4670000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670000 prefixEnd_4670000 := by exact prefixLift 4670000
  have htrace : WordTrace (prefixWord ++ tailWord_4670000) baseStart_4670000 baseEnd_4670000 := by
    simpa [prefixWord, tailWord_4670000, baseEnd_4670000] using wordTrace_append hprefix tailTrace_4670000
  have hstable : (prefixWord ++ tailWord_4670000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670000).length < 2 ^ (prefixWord ++ tailWord_4670000).sum := by decide
  have hdescent : baseEnd_4670000 < baseStart_4670000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670003 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 3]
def baseStart_4670003 : Nat := 118140960795 + 4670003 * 2 ^ 59
def prefixEnd_4670003 : Nat := 4983230072969 + 3 ^ 40 * 4670003 * 2
def baseEnd_4670003 : Nat := 2397956196938797325485553

theorem tailTrace_4670003 : CollatzResearch.WordTrace tailWord_4670003 prefixEnd_4670003 2397956196938797325485553 := by
  unfold tailWord_4670003
  simp only [CollatzResearch.WordTrace]
  refine ⟨170329002500384178859478663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113552668333589452572985775 170329002500384178859478663)
  ·
    refine ⟨255493503750576268289217995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170329002500384178859478663 255493503750576268289217995)
    ·
      refine ⟨383240255625864402433826993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255493503750576268289217995 383240255625864402433826993)
      ·
        refine ⟨287430191719398301825370245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383240255625864402433826993 287430191719398301825370245)
        ·
          refine ⟨53893160947387181592256921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 287430191719398301825370245 53893160947387181592256921)
          ·
            refine ⟨40419870710540386194192691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53893160947387181592256921 40419870710540386194192691)
            ·
              refine ⟨60629806065810579291289037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40419870710540386194192691 60629806065810579291289037)
              ·
                refine ⟨22736177274678967234233389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60629806065810579291289037 22736177274678967234233389)
                ·
                  refine ⟨8526066478004612712837521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22736177274678967234233389 8526066478004612712837521)
                  ·
                    refine ⟨6394549858503459534628141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8526066478004612712837521 6394549858503459534628141)
                    ·
                      refine ⟨2397956196938797325485553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6394549858503459534628141 2397956196938797325485553)
                      ·
                        rfl

theorem cell23_4670003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 3].length) (baseStart_4670003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670003 prefixEnd_4670003 := by exact prefixLift 4670003
  have htrace : WordTrace (prefixWord ++ tailWord_4670003) baseStart_4670003 baseEnd_4670003 := by
    simpa [prefixWord, tailWord_4670003, baseEnd_4670003] using wordTrace_append hprefix tailTrace_4670003
  have hstable : (prefixWord ++ tailWord_4670003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670003).length < 2 ^ (prefixWord ++ tailWord_4670003).sum := by decide
  have hdescent : baseEnd_4670003 < baseStart_4670003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670004 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_4670004 : Nat := 118140960795 + 4670004 * 2 ^ 59
def prefixEnd_4670004 : Nat := 4983230072969 + 3 ^ 40 * 4670004 * 2
def baseEnd_4670004 : Nat := 2397956710419451821573049

theorem tailTrace_4670004 : CollatzResearch.WordTrace tailWord_4670004 prefixEnd_4670004 2397956710419451821573049 := by
  unfold tailWord_4670004
  simp only [CollatzResearch.WordTrace]
  refine ⟨85164519486690278015132533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113552692648920370686843377 85164519486690278015132533)
  ·
    refine ⟨7984173701877213563918675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85164519486690278015132533 7984173701877213563918675)
    ·
      refine ⟨11976260552815820345878013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7984173701877213563918675 11976260552815820345878013)
      ·
        refine ⟨4491097707305932629704255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11976260552815820345878013 4491097707305932629704255)
        ·
          refine ⟨6736646560958898944556383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4491097707305932629704255 6736646560958898944556383)
          ·
            refine ⟨10104969841438348416834575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736646560958898944556383 10104969841438348416834575)
            ·
              refine ⟨15157454762157522625251863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10104969841438348416834575 15157454762157522625251863)
              ·
                refine ⟨22736182143236283937877795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15157454762157522625251863 22736182143236283937877795)
                ·
                  refine ⟨34104273214854425906816693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22736182143236283937877795 34104273214854425906816693)
                  ·
                    refine ⟨3197275613892602428764065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34104273214854425906816693 3197275613892602428764065)
                    ·
                      refine ⟨2397956710419451821573049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197275613892602428764065 2397956710419451821573049)
                      ·
                        rfl

theorem cell23_4670004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_4670004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670004 prefixEnd_4670004 := by exact prefixLift 4670004
  have htrace : WordTrace (prefixWord ++ tailWord_4670004) baseStart_4670004 baseEnd_4670004 := by
    simpa [prefixWord, tailWord_4670004, baseEnd_4670004] using wordTrace_append hprefix tailTrace_4670004
  have hstable : (prefixWord ++ tailWord_4670004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670004).length < 2 ^ (prefixWord ++ tailWord_4670004).sum := by decide
  have hdescent : baseEnd_4670004 < baseStart_4670004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670017 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_4670017 : Nat := 118140960795 + 4670017 * 2 ^ 59
def prefixEnd_4670017 : Nat := 4983230072969 + 3 ^ 40 * 4670017 * 2
def baseEnd_4670017 : Nat := 2397963385667960270710489

theorem tailTrace_4670017 : CollatzResearch.WordTrace tailWord_4670017 prefixEnd_4670017 2397963385667960270710489 := by
  unfold tailWord_4670017
  simp only [CollatzResearch.WordTrace]
  refine ⟨170329513122333459250488305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113553008748222306166992203 170329513122333459250488305)
  ·
    refine ⟨127747134841750094437866229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170329513122333459250488305 127747134841750094437866229)
    ·
      refine ⟨11976293891414071353549959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127747134841750094437866229 11976293891414071353549959)
      ·
        refine ⟨17964440837121107030324939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11976293891414071353549959 17964440837121107030324939)
        ·
          refine ⟨26946661255681660545487409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17964440837121107030324939 26946661255681660545487409)
          ·
            refine ⟨20209995941761245409115557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26946661255681660545487409 20209995941761245409115557)
            ·
              refine ⟨3789374239080233514209167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20209995941761245409115557 3789374239080233514209167)
              ·
                refine ⟨5684061358620350271313751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3789374239080233514209167 5684061358620350271313751)
                ·
                  refine ⟨8526092037930525406970627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5684061358620350271313751 8526092037930525406970627)
                  ·
                    refine ⟨12789138056895788110455941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8526092037930525406970627 12789138056895788110455941)
                    ·
                      refine ⟨2397963385667960270710489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12789138056895788110455941 2397963385667960270710489)
                      ·
                        rfl

theorem cell23_4670017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_4670017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670017 prefixEnd_4670017 := by exact prefixLift 4670017
  have htrace : WordTrace (prefixWord ++ tailWord_4670017) baseStart_4670017 baseEnd_4670017 := by
    simpa [prefixWord, tailWord_4670017, baseEnd_4670017] using wordTrace_append hprefix tailTrace_4670017
  have hstable : (prefixWord ++ tailWord_4670017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670017).length < 2 ^ (prefixWord ++ tailWord_4670017).sum := by decide
  have hdescent : baseEnd_4670017 < baseStart_4670017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670034 : List Nat := [3, 2, 2, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_4670034 : Nat := 118140960795 + 4670034 * 2 ^ 59
def prefixEnd_4670034 : Nat := 4983230072969 + 3 ^ 40 * 4670034 * 2
def baseEnd_4670034 : Nat := 2397972114839086704197911

theorem tailTrace_4670034 : CollatzResearch.WordTrace tailWord_4670034 prefixEnd_4670034 2397972114839086704197911 := by
  unfold tailWord_4670034
  simp only [CollatzResearch.WordTrace]
  refine ⟨42582533290817967788464289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113553422108847914102571437 42582533290817967788464289)
  ·
    refine ⟨31936899968113475841348217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42582533290817967788464289 31936899968113475841348217)
    ·
      refine ⟨23952674976085106881011163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31936899968113475841348217 23952674976085106881011163)
      ·
        refine ⟨35929012464127660321516745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23952674976085106881011163 35929012464127660321516745)
        ·
          refine ⟨26946759348095745241137559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35929012464127660321516745 26946759348095745241137559)
          ·
            refine ⟨40420139022143617861706339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26946759348095745241137559 40420139022143617861706339)
            ·
              refine ⟨60630208533215426792559509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40420139022143617861706339 60630208533215426792559509)
              ·
                refine ⟨2842041024994473130901227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60630208533215426792559509 2842041024994473130901227)
                ·
                  refine ⟨4263061537491709696351841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842041024994473130901227 4263061537491709696351841)
                  ·
                    refine ⟨3197296153118782272263881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4263061537491709696351841 3197296153118782272263881)
                    ·
                      refine ⟨2397972114839086704197911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197296153118782272263881 2397972114839086704197911)
                      ·
                        rfl

theorem cell23_4670034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_4670034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670034 prefixEnd_4670034 := by exact prefixLift 4670034
  have htrace : WordTrace (prefixWord ++ tailWord_4670034) baseStart_4670034 baseEnd_4670034 := by
    simpa [prefixWord, tailWord_4670034, baseEnd_4670034] using wordTrace_append hprefix tailTrace_4670034
  have hstable : (prefixWord ++ tailWord_4670034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670034).length < 2 ^ (prefixWord ++ tailWord_4670034).sum := by decide
  have hdescent : baseEnd_4670034 < baseStart_4670034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670044 : List Nat := [2, 2, 4, 1, 3, 1, 3, 1, 2, 4]
def baseStart_4670044 : Nat := 118140960795 + 4670044 * 2 ^ 59
def prefixEnd_4670044 : Nat := 4983230072969 + 3 ^ 40 * 4670044 * 2
def baseEnd_4670044 : Nat := 799325749881877221690955

theorem tailTrace_4670044 : CollatzResearch.WordTrace tailWord_4670044 prefixEnd_4670044 799325749881877221690955 := by
  unfold tailWord_4670044
  simp only [CollatzResearch.WordTrace]
  refine ⟨85165248946617821430860593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113553665262157095241147457 85165248946617821430860593)
  ·
    refine ⟨63873936709963366073145445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85165248946617821430860593 63873936709963366073145445)
    ·
      refine ⟨11976363133118131138714771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63873936709963366073145445 11976363133118131138714771)
      ·
        refine ⟨17964544699677196708072157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11976363133118131138714771 17964544699677196708072157)
        ·
          refine ⟨6736704262378948765527059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17964544699677196708072157 6736704262378948765527059)
          ·
            refine ⟨10105056393568423148290589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736704262378948765527059 10105056393568423148290589)
            ·
              refine ⟨3789396147588158680608971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10105056393568423148290589 3789396147588158680608971)
              ·
                refine ⟨5684094221382238020913457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3789396147588158680608971 5684094221382238020913457)
                ·
                  refine ⟨4263070666036678515685093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5684094221382238020913457 4263070666036678515685093)
                  ·
                    refine ⟨799325749881877221690955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4263070666036678515685093 799325749881877221690955)
                    ·
                      rfl

theorem cell23_4670044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_4670044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670044 prefixEnd_4670044 := by exact prefixLift 4670044
  have htrace : WordTrace (prefixWord ++ tailWord_4670044) baseStart_4670044 baseEnd_4670044 := by
    simpa [prefixWord, tailWord_4670044, baseEnd_4670044] using wordTrace_append hprefix tailTrace_4670044
  have hstable : (prefixWord ++ tailWord_4670044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670044).length < 2 ^ (prefixWord ++ tailWord_4670044).sum := by decide
  have hdescent : baseEnd_4670044 < baseStart_4670044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670060 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 3, 3, 2]
def baseStart_4670060 : Nat := 118140960795 + 4670060 * 2 ^ 59
def prefixEnd_4670060 : Nat := 4983230072969 + 3 ^ 40 * 4670060 * 2
def baseEnd_4670060 : Nat := 2397985465336103602472791

theorem tailTrace_4670060 : CollatzResearch.WordTrace tailWord_4670060 prefixEnd_4670060 2397985465336103602472791 := by
  unfold tailWord_4670060
  simp only [CollatzResearch.WordTrace]
  refine ⟨85165540730588838797151817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113554054307451785062869089 85165540730588838797151817)
  ·
    refine ⟨63874155547941629097863863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85165540730588838797151817 63874155547941629097863863)
    ·
      refine ⟨95811233321912443646795795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63874155547941629097863863 95811233321912443646795795)
      ·
        refine ⟨143716849982868665470193693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95811233321912443646795795 143716849982868665470193693)
        ·
          refine ⟨53893818743575749551322635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143716849982868665470193693 53893818743575749551322635)
          ·
            refine ⟨80840728115363624326983953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53893818743575749551322635 80840728115363624326983953)
            ·
              refine ⟨60630546086522718245237965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80840728115363624326983953 60630546086522718245237965)
              ·
                refine ⟨22736454782446019341964237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60630546086522718245237965 22736454782446019341964237)
                ·
                  refine ⟨8526170543417257253236589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22736454782446019341964237 8526170543417257253236589)
                  ·
                    refine ⟨3197313953781471469963721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8526170543417257253236589 3197313953781471469963721)
                    ·
                      refine ⟨2397985465336103602472791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197313953781471469963721 2397985465336103602472791)
                      ·
                        rfl

theorem cell23_4670060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 3, 2].length) (baseStart_4670060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670060 prefixEnd_4670060 := by exact prefixLift 4670060
  have htrace : WordTrace (prefixWord ++ tailWord_4670060) baseStart_4670060 baseEnd_4670060 := by
    simpa [prefixWord, tailWord_4670060, baseEnd_4670060] using wordTrace_append hprefix tailTrace_4670060
  have hstable : (prefixWord ++ tailWord_4670060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670060).length < 2 ^ (prefixWord ++ tailWord_4670060).sum := by decide
  have hdescent : baseEnd_4670060 < baseStart_4670060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670103 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_4670103 : Nat := 118140960795 + 4670103 * 2 ^ 59
def prefixEnd_4670103 : Nat := 4983230072969 + 3 ^ 40 * 4670103 * 2
def baseEnd_4670103 : Nat := 2398007545004246934235093

theorem tailTrace_4670103 : CollatzResearch.WordTrace tailWord_4670103 prefixEnd_4670103 2398007545004246934235093 := by
  unfold tailWord_4670103
  simp only [CollatzResearch.WordTrace]
  refine ⟨170332649800021895938118963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113555099866681263958745975 170332649800021895938118963)
  ·
    refine ⟨255498974700032843907178445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170332649800021895938118963 255498974700032843907178445)
    ·
      refine ⟨95812115512512316465191917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255498974700032843907178445 95812115512512316465191917)
      ·
        refine ⟨35929543317192118674446969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95812115512512316465191917 35929543317192118674446969)
        ·
          refine ⟨26947157487894089005835227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35929543317192118674446969 26947157487894089005835227)
          ·
            refine ⟨40420736231841133508752841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26947157487894089005835227 40420736231841133508752841)
            ·
              refine ⟨30315552173880850131564631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40420736231841133508752841 30315552173880850131564631)
              ·
                refine ⟨45473328260821275197346947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30315552173880850131564631 45473328260821275197346947)
                ·
                  refine ⟨68209992391231912796020421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45473328260821275197346947 68209992391231912796020421)
                  ·
                    refine ⟨12789373573355983649253829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68209992391231912796020421 12789373573355983649253829)
                    ·
                      refine ⟨2398007545004246934235093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12789373573355983649253829 2398007545004246934235093)
                      ·
                        rfl

theorem cell23_4670103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_4670103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670103 prefixEnd_4670103 := by exact prefixLift 4670103
  have htrace : WordTrace (prefixWord ++ tailWord_4670103) baseStart_4670103 baseEnd_4670103 := by
    simpa [prefixWord, tailWord_4670103, baseEnd_4670103] using wordTrace_append hprefix tailTrace_4670103
  have hstable : (prefixWord ++ tailWord_4670103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670103).length < 2 ^ (prefixWord ++ tailWord_4670103).sum := by decide
  have hdescent : baseEnd_4670103 < baseStart_4670103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670110 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4670110 : Nat := 118140960795 + 4670110 * 2 ^ 59
def prefixEnd_4670110 : Nat := 4983230072969 + 3 ^ 40 * 4670110 * 2
def baseEnd_4670110 : Nat := 2398011139368828406847561

theorem tailTrace_4670110 : CollatzResearch.WordTrace tailWord_4670110 prefixEnd_4670110 2398011139368828406847561 := by
  unfold tailWord_4670110
  simp only [CollatzResearch.WordTrace]
  refine ⟨21291613138874567016702973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113555270073997690755749189 21291613138874567016702973)
  ·
    refine ⟨7984354927077962631263615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21291613138874567016702973 7984354927077962631263615)
    ·
      refine ⟨11976532390616943946895423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7984354927077962631263615 11976532390616943946895423)
      ·
        refine ⟨17964798585925415920343135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11976532390616943946895423 17964798585925415920343135)
        ·
          refine ⟨26947197878888123880514703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17964798585925415920343135 26947197878888123880514703)
          ·
            refine ⟨40420796818332185820772055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26947197878888123880514703 40420796818332185820772055)
            ·
              refine ⟨60631195227498278731158083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40420796818332185820772055 60631195227498278731158083)
              ·
                refine ⟨90946792841247418096737125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60631195227498278731158083 90946792841247418096737125)
                ·
                  refine ⟨17052523657733890893138211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90946792841247418096737125 17052523657733890893138211)
                  ·
                    refine ⟨25578785486600836339707317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17052523657733890893138211 25578785486600836339707317)
                    ·
                      refine ⟨2398011139368828406847561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25578785486600836339707317 2398011139368828406847561)
                      ·
                        rfl

theorem cell23_4670110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4670110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670110 prefixEnd_4670110 := by exact prefixLift 4670110
  have htrace : WordTrace (prefixWord ++ tailWord_4670110) baseStart_4670110 baseEnd_4670110 := by
    simpa [prefixWord, tailWord_4670110, baseEnd_4670110] using wordTrace_append hprefix tailTrace_4670110
  have hstable : (prefixWord ++ tailWord_4670110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670110).length < 2 ^ (prefixWord ++ tailWord_4670110).sum := by decide
  have hdescent : baseEnd_4670110 < baseStart_4670110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670130 : List Nat := [3, 2, 1, 1, 1, 2, 1, 7, 5]
def baseStart_4670130 : Nat := 118140960795 + 4670130 * 2 ^ 59
def prefixEnd_4670130 : Nat := 4983230072969 + 3 ^ 40 * 4670130 * 2
def baseEnd_4670130 : Nat := 266446823220213147621941

theorem tailTrace_4670130 : CollatzResearch.WordTrace tailWord_4670130 prefixEnd_4670130 266446823220213147621941 := by
  unfold tailWord_4670130
  simp only [CollatzResearch.WordTrace]
  refine ⟨42583408642731019887337961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113555756380616053032901229 42583408642731019887337961)
  ·
    refine ⟨31937556482048264915503471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42583408642731019887337961 31937556482048264915503471)
    ·
      refine ⟨47906334723072397373255207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31937556482048264915503471 47906334723072397373255207)
      ·
        refine ⟨71859502084608596059882811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47906334723072397373255207 71859502084608596059882811)
        ·
          refine ⟨107789253126912894089824217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71859502084608596059882811 107789253126912894089824217)
          ·
            refine ⟨80841939845184670567368163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107789253126912894089824217 80841939845184670567368163)
            ·
              refine ⟨121262909767777005851052245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80841939845184670567368163 121262909767777005851052245)
              ·
                refine ⟨2842099447682273574634037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 121262909767777005851052245 2842099447682273574634037)
                ·
                  refine ⟨266446823220213147621941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2842099447682273574634037 266446823220213147621941)
                  ·
                    rfl

theorem cell23_4670130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_4670130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670130 prefixEnd_4670130 := by exact prefixLift 4670130
  have htrace : WordTrace (prefixWord ++ tailWord_4670130) baseStart_4670130 baseEnd_4670130 := by
    simpa [prefixWord, tailWord_4670130, baseEnd_4670130] using wordTrace_append hprefix tailTrace_4670130
  have hstable : (prefixWord ++ tailWord_4670130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670130).length < 2 ^ (prefixWord ++ tailWord_4670130).sum := by decide
  have hdescent : baseEnd_4670130 < baseStart_4670130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670140 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_4670140 : Nat := 118140960795 + 4670140 * 2 ^ 59
def prefixEnd_4670140 : Nat := 4983230072969 + 3 ^ 40 * 4670140 * 2
def baseEnd_4670140 : Nat := 2398026543788463289472423

theorem tailTrace_4670140 : CollatzResearch.WordTrace tailWord_4670140 prefixEnd_4670140 2398026543788463289472423 := by
  unfold tailWord_4670140
  simp only [CollatzResearch.WordTrace]
  refine ⟨85166999650443925628607937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113555999533925234171477249 85166999650443925628607937)
  ·
    refine ⟨63875249737832944221455953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85166999650443925628607937 63875249737832944221455953)
    ·
      refine ⟨47906437303374708166091965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63875249737832944221455953 47906437303374708166091965)
      ·
        refine ⟨17964913988765515562284487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47906437303374708166091965 17964913988765515562284487)
        ·
          refine ⟨26947370983148273343426731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17964913988765515562284487 26947370983148273343426731)
          ·
            refine ⟨40421056474722410015140097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26947370983148273343426731 40421056474722410015140097)
            ·
              refine ⟨30315792356041807511355073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40421056474722410015140097 30315792356041807511355073)
              ·
                refine ⟨22736844267031355633516305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30315792356041807511355073 22736844267031355633516305)
                ·
                  refine ⟨17052633200273516725137229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22736844267031355633516305 17052633200273516725137229)
                  ·
                    refine ⟨6394737450102568771926461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17052633200273516725137229 6394737450102568771926461)
                    ·
                      refine ⟨2398026543788463289472423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6394737450102568771926461 2398026543788463289472423)
                      ·
                        rfl

theorem cell23_4670140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_4670140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670140 prefixEnd_4670140 := by exact prefixLift 4670140
  have htrace : WordTrace (prefixWord ++ tailWord_4670140) baseStart_4670140 baseEnd_4670140 := by
    simpa [prefixWord, tailWord_4670140, baseEnd_4670140] using wordTrace_append hprefix tailTrace_4670140
  have hstable : (prefixWord ++ tailWord_4670140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670140).length < 2 ^ (prefixWord ++ tailWord_4670140).sum := by decide
  have hdescent : baseEnd_4670140 < baseStart_4670140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670177 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 2, 5]
def baseStart_4670177 : Nat := 118140960795 + 4670177 * 2 ^ 59
def prefixEnd_4670177 : Nat := 4983230072969 + 3 ^ 40 * 4670177 * 2
def baseEnd_4670177 : Nat := 799348514190893214903251

theorem tailTrace_4670177 : CollatzResearch.WordTrace tailWord_4670177 prefixEnd_4670177 799348514190893214903251 := by
  unfold tailWord_4670177
  simp only [CollatzResearch.WordTrace]
  refine ⟨170335348801753806576312785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113556899201169204384208523 170335348801753806576312785)
  ·
    refine ⟨127751511601315354932234589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170335348801753806576312785 127751511601315354932234589)
    ·
      refine ⟨47906816850493258099587971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127751511601315354932234589 47906816850493258099587971)
      ·
        refine ⟨71860225275739887149381957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47906816850493258099587971 71860225275739887149381957)
        ·
          refine ⟨13473792239201228840509117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71860225275739887149381957 13473792239201228840509117)
          ·
            refine ⟨5052672089700460815190919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13473792239201228840509117 5052672089700460815190919)
            ·
              refine ⟨7579008134550691222786379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5052672089700460815190919 7579008134550691222786379)
              ·
                refine ⟨11368512201826036834179569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7579008134550691222786379 11368512201826036834179569)
                ·
                  refine ⟨8526384151369527625634677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11368512201826036834179569 8526384151369527625634677)
                  ·
                    refine ⟨799348514190893214903251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8526384151369527625634677 799348514190893214903251)
                    ·
                      rfl

theorem cell23_4670177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_4670177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670177 prefixEnd_4670177 := by exact prefixLift 4670177
  have htrace : WordTrace (prefixWord ++ tailWord_4670177) baseStart_4670177 baseEnd_4670177 := by
    simpa [prefixWord, tailWord_4670177, baseEnd_4670177] using wordTrace_append hprefix tailTrace_4670177
  have hstable : (prefixWord ++ tailWord_4670177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670177).length < 2 ^ (prefixWord ++ tailWord_4670177).sum := by decide
  have hdescent : baseEnd_4670177 < baseStart_4670177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670180 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_4670180 : Nat := 118140960795 + 4670180 * 2 ^ 59
def prefixEnd_4670180 : Nat := 4983230072969 + 3 ^ 40 * 4670180 * 2
def baseEnd_4670180 : Nat := 2398047083014643132972239

theorem tailTrace_4670180 : CollatzResearch.WordTrace tailWord_4670180 prefixEnd_4670180 2398047083014643132972239 := by
  unfold tailWord_4670180
  simp only [CollatzResearch.WordTrace]
  refine ⟨85167729110371469044335997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113556972147161958725781329 85167729110371469044335997)
  ·
    refine ⟨31937898416389300891625999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85167729110371469044335997 31937898416389300891625999)
    ·
      refine ⟨47906847624583951337438999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31937898416389300891625999 47906847624583951337438999)
      ·
        refine ⟨71860271436875927006158499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47906847624583951337438999 71860271436875927006158499)
        ·
          refine ⟨107790407155313890509237749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71860271436875927006158499 107790407155313890509237749)
          ·
            refine ⟨10105350670810677235241039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107790407155313890509237749 10105350670810677235241039)
            ·
              refine ⟨15158026006216015852861559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10105350670810677235241039 15158026006216015852861559)
              ·
                refine ⟨22737039009324023779292339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15158026006216015852861559 22737039009324023779292339)
                ·
                  refine ⟨34105558513986035668938509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22737039009324023779292339 34105558513986035668938509)
                  ·
                    refine ⟨12789584442744763375851941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34105558513986035668938509 12789584442744763375851941)
                    ·
                      refine ⟨2398047083014643132972239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12789584442744763375851941 2398047083014643132972239)
                      ·
                        rfl

theorem cell23_4670180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_4670180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670180 prefixEnd_4670180 := by exact prefixLift 4670180
  have htrace : WordTrace (prefixWord ++ tailWord_4670180) baseStart_4670180 baseEnd_4670180 := by
    simpa [prefixWord, tailWord_4670180, baseEnd_4670180] using wordTrace_append hprefix tailTrace_4670180
  have hstable : (prefixWord ++ tailWord_4670180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670180).length < 2 ^ (prefixWord ++ tailWord_4670180).sum := by decide
  have hdescent : baseEnd_4670180 < baseStart_4670180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670193 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_4670193 : Nat := 118140960795 + 4670193 * 2 ^ 59
def prefixEnd_4670193 : Nat := 4983230072969 + 3 ^ 40 * 4670193 * 2
def baseEnd_4670193 : Nat := 2398053758263151582109679

theorem tailTrace_4670193 : CollatzResearch.WordTrace tailWord_4670193 prefixEnd_4670193 2398053758263151582109679 := by
  unfold tailWord_4670193
  simp only [CollatzResearch.WordTrace]
  refine ⟨170335932369695841308895233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113557288246463894205930155 170335932369695841308895233)
  ·
    refine ⟨127751949277271880981671425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170335932369695841308895233 127751949277271880981671425)
    ·
      refine ⟨95813961957953910736253569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127751949277271880981671425 95813961957953910736253569)
      ·
        refine ⟨71860471468465433052190177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95813961957953910736253569 71860471468465433052190177)
        ·
          refine ⟨53895353601349074789142633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71860471468465433052190177 53895353601349074789142633)
          ·
            refine ⟨40421515201011806091856975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53895353601349074789142633 40421515201011806091856975)
            ·
              refine ⟨60632272801517709137785463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40421515201011806091856975 60632272801517709137785463)
              ·
                refine ⟨90948409202276563706678195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60632272801517709137785463 90948409202276563706678195)
                ·
                  refine ⟨136422613803414845560017293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90948409202276563706678195 136422613803414845560017293)
                  ·
                    refine ⟨51158480176280567085006485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 136422613803414845560017293 51158480176280567085006485)
                    ·
                      refine ⟨2398053758263151582109679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51158480176280567085006485 2398053758263151582109679)
                      ·
                        rfl

theorem cell23_4670193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_4670193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670193 prefixEnd_4670193 := by exact prefixLift 4670193
  have htrace : WordTrace (prefixWord ++ tailWord_4670193) baseStart_4670193 baseEnd_4670193 := by
    simpa [prefixWord, tailWord_4670193, baseEnd_4670193] using wordTrace_append hprefix tailTrace_4670193
  have hstable : (prefixWord ++ tailWord_4670193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670193).length < 2 ^ (prefixWord ++ tailWord_4670193).sum := by decide
  have hdescent : baseEnd_4670193 < baseStart_4670193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670200 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 4, 2, 3]
def baseStart_4670200 : Nat := 118140960795 + 4670200 * 2 ^ 59
def prefixEnd_4670200 : Nat := 4983230072969 + 3 ^ 40 * 4670200 * 2
def baseEnd_4670200 : Nat := 2398057352627733054722147

theorem tailTrace_4670200 : CollatzResearch.WordTrace tailWord_4670200 prefixEnd_4670200 2398057352627733054722147 := by
  unfold tailWord_4670200
  simp only [CollatzResearch.WordTrace]
  refine ⟨85168093840335240752200027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113557458453780321002933369 85168093840335240752200027)
  ·
    refine ⟨127752140760502861128300041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85168093840335240752200027 127752140760502861128300041)
    ·
      refine ⟨95814105570377145846225031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127752140760502861128300041 95814105570377145846225031)
      ·
        refine ⟨143721158355565718769337547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95814105570377145846225031 143721158355565718769337547)
        ·
          refine ⟨215581737533348578154006321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143721158355565718769337547 215581737533348578154006321)
          ·
            refine ⟨161686303150011433615504741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215581737533348578154006321 161686303150011433615504741)
            ·
              refine ⟨30316181840627143802907139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161686303150011433615504741 30316181840627143802907139)
              ·
                refine ⟨45474272760940715704360709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30316181840627143802907139 45474272760940715704360709)
                ·
                  refine ⟨8526426142676384194567633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45474272760940715704360709 8526426142676384194567633)
                  ·
                    refine ⟨6394819607007288145925725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8526426142676384194567633 6394819607007288145925725)
                    ·
                      refine ⟨2398057352627733054722147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6394819607007288145925725 2398057352627733054722147)
                      ·
                        rfl

theorem cell23_4670200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_4670200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670200 prefixEnd_4670200 := by exact prefixLift 4670200
  have htrace : WordTrace (prefixWord ++ tailWord_4670200) baseStart_4670200 baseEnd_4670200 := by
    simpa [prefixWord, tailWord_4670200, baseEnd_4670200] using wordTrace_append hprefix tailTrace_4670200
  have hstable : (prefixWord ++ tailWord_4670200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670200).length < 2 ^ (prefixWord ++ tailWord_4670200).sum := by decide
  have hdescent : baseEnd_4670200 < baseStart_4670200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670223 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 6]
def baseStart_4670223 : Nat := 118140960795 + 4670223 * 2 ^ 59
def prefixEnd_4670223 : Nat := 4983230072969 + 3 ^ 40 * 4670223 * 2
def baseEnd_4670223 : Nat := 2398069162682786464734541

theorem tailTrace_4670223 : CollatzResearch.WordTrace tailWord_4670223 prefixEnd_4670223 2398069162682786464734541 := by
  unfold tailWord_4670223
  simp only [CollatzResearch.WordTrace]
  refine ⟨170337026559587156432487323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113558017706391437621658215 170337026559587156432487323)
  ·
    refine ⟨255505539839380734648730985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170337026559587156432487323 255505539839380734648730985)
    ·
      refine ⟨191629154879535550986548239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255505539839380734648730985 191629154879535550986548239)
      ·
        refine ⟨287443732319303326479822359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191629154879535550986548239 287443732319303326479822359)
        ·
          refine ⟨431165598478954989719733539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287443732319303326479822359 431165598478954989719733539)
          ·
            refine ⟨646748397718432484579600309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431165598478954989719733539 646748397718432484579600309)
            ·
              refine ⟨60632662286103045429337529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 646748397718432484579600309 60632662286103045429337529)
              ·
                refine ⟨45474496714577284072003147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60632662286103045429337529 45474496714577284072003147)
                ·
                  refine ⟨68211745071865926108004721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45474496714577284072003147 68211745071865926108004721)
                  ·
                    refine ⟨51158808803899444581003541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68211745071865926108004721 51158808803899444581003541)
                    ·
                      refine ⟨2398069162682786464734541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51158808803899444581003541 2398069162682786464734541)
                      ·
                        rfl

theorem cell23_4670223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_4670223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670223 prefixEnd_4670223 := by exact prefixLift 4670223
  have htrace : WordTrace (prefixWord ++ tailWord_4670223) baseStart_4670223 baseEnd_4670223 := by
    simpa [prefixWord, tailWord_4670223, baseEnd_4670223] using wordTrace_append hprefix tailTrace_4670223
  have hstable : (prefixWord ++ tailWord_4670223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670223).length < 2 ^ (prefixWord ++ tailWord_4670223).sum := by decide
  have hdescent : baseEnd_4670223 < baseStart_4670223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670280 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 1, 6]
def baseStart_4670280 : Nat := 118140960795 + 4670280 * 2 ^ 59
def prefixEnd_4670280 : Nat := 4983230072969 + 3 ^ 40 * 4670280 * 2
def baseEnd_4670280 : Nat := 799366143693364247240593

theorem tailTrace_4670280 : CollatzResearch.WordTrace tailWord_4670280 prefixEnd_4670280 799366143693364247240593 := by
  unfold tailWord_4670280
  simp only [CollatzResearch.WordTrace]
  refine ⟨85169552760190327583656147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113559403680253770111541529 85169552760190327583656147)
  ·
    refine ⟨127754329140285491375484221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85169552760190327583656147 127754329140285491375484221)
    ·
      refine ⟨47907873427607059265806583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127754329140285491375484221 47907873427607059265806583)
      ·
        refine ⟨71861810141410588898709875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47907873427607059265806583 71861810141410588898709875)
        ·
          refine ⟨107792715212115883348064813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71861810141410588898709875 107792715212115883348064813)
          ·
            refine ⟨40422268204543456255524305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107792715212115883348064813 40422268204543456255524305)
            ·
              refine ⟨30316701153407592191643229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40422268204543456255524305 30316701153407592191643229)
              ·
                refine ⟨11368762932527847071866211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30316701153407592191643229 11368762932527847071866211)
                ·
                  refine ⟨17053144398791770607799317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11368762932527847071866211 17053144398791770607799317)
                  ·
                    refine ⟨799366143693364247240593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17053144398791770607799317 799366143693364247240593)
                    ·
                      rfl

theorem cell23_4670280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_4670280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670280 prefixEnd_4670280 := by exact prefixLift 4670280
  have htrace : WordTrace (prefixWord ++ tailWord_4670280) baseStart_4670280 baseEnd_4670280 := by
    simpa [prefixWord, tailWord_4670280, baseEnd_4670280] using wordTrace_append hprefix tailTrace_4670280
  have hstable : (prefixWord ++ tailWord_4670280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670280).length < 2 ^ (prefixWord ++ tailWord_4670280).sum := by decide
  have hdescent : baseEnd_4670280 < baseStart_4670280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670284 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 1, 5]
def baseStart_4670284 : Nat := 118140960795 + 4670284 * 2 ^ 59
def prefixEnd_4670284 : Nat := 4983230072969 + 3 ^ 40 * 4670284 * 2
def baseEnd_4670284 : Nat := 799366828334236908690587

theorem tailTrace_4670284 : CollatzResearch.WordTrace tailWord_4670284 prefixEnd_4670284 799366828334236908690587 := by
  unfold tailWord_4670284
  simp only [CollatzResearch.WordTrace]
  refine ⟨85169625706183081925228953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113559500941577442566971937 85169625706183081925228953)
  ·
    refine ⟨63877219279637311443921715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85169625706183081925228953 63877219279637311443921715)
    ·
      refine ⟨95815828919455967165882573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63877219279637311443921715 95815828919455967165882573)
      ·
        refine ⟨35930935844795987687205965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95815828919455967165882573 35930935844795987687205965)
        ·
          refine ⟨13474100941798495382702237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35930935844795987687205965 13474100941798495382702237)
          ·
            refine ⟨5052787853174435768513339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13474100941798495382702237 5052787853174435768513339)
            ·
              refine ⟨7579181779761653652770009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5052787853174435768513339 7579181779761653652770009)
              ·
                refine ⟨5684386334821240239577507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7579181779761653652770009 5684386334821240239577507)
                ·
                  refine ⟨8526579502231860359366261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5684386334821240239577507 8526579502231860359366261)
                  ·
                    refine ⟨799366828334236908690587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8526579502231860359366261 799366828334236908690587)
                    ·
                      rfl

theorem cell23_4670284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_4670284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670284 prefixEnd_4670284 := by exact prefixLift 4670284
  have htrace : WordTrace (prefixWord ++ tailWord_4670284) baseStart_4670284 baseEnd_4670284 := by
    simpa [prefixWord, tailWord_4670284, baseEnd_4670284] using wordTrace_append hprefix tailTrace_4670284
  have hstable : (prefixWord ++ tailWord_4670284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670284).length < 2 ^ (prefixWord ++ tailWord_4670284).sum := by decide
  have hdescent : baseEnd_4670284 < baseStart_4670284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670304 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 1, 1, 4]
def baseStart_4670304 : Nat := 118140960795 + 4670304 * 2 ^ 59
def prefixEnd_4670304 : Nat := 4983230072969 + 3 ^ 40 * 4670304 * 2
def baseEnd_4670304 : Nat := 2398110754615800647821669

theorem tailTrace_4670304 : CollatzResearch.WordTrace tailWord_4670304 prefixEnd_4670304 2398110754615800647821669 := by
  unfold tailWord_4670304
  simp only [CollatzResearch.WordTrace]
  refine ⟨85169990436146853633092983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113559987248195804844123977 85169990436146853633092983)
  ·
    refine ⟨127754985654220280449639475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85169990436146853633092983 127754985654220280449639475)
    ·
      refine ⟨191632478481330420674459213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127754985654220280449639475 191632478481330420674459213)
      ·
        refine ⟨71862179430498907752922205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191632478481330420674459213 71862179430498907752922205)
        ·
          refine ⟨26948317286437090407345827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71862179430498907752922205 26948317286437090407345827)
          ·
            refine ⟨40422475929655635611018741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26948317286437090407345827 40422475929655635611018741)
            ·
              refine ⟨3789607118405215838533007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40422475929655635611018741 3789607118405215838533007)
              ·
                refine ⟨5684410677607823757799511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3789607118405215838533007 5684410677607823757799511)
                ·
                  refine ⟨8526616016411735636699267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5684410677607823757799511 8526616016411735636699267)
                  ·
                    refine ⟨12789924024617603455048901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8526616016411735636699267 12789924024617603455048901)
                    ·
                      refine ⟨2398110754615800647821669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12789924024617603455048901 2398110754615800647821669)
                      ·
                        rfl

theorem cell23_4670304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_4670304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670304 prefixEnd_4670304 := by exact prefixLift 4670304
  have htrace : WordTrace (prefixWord ++ tailWord_4670304) baseStart_4670304 baseEnd_4670304 := by
    simpa [prefixWord, tailWord_4670304, baseEnd_4670304] using wordTrace_append hprefix tailTrace_4670304
  have hstable : (prefixWord ++ tailWord_4670304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670304).length < 2 ^ (prefixWord ++ tailWord_4670304).sum := by decide
  have hdescent : baseEnd_4670304 < baseStart_4670304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670307 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 5]
def baseStart_4670307 : Nat := 118140960795 + 4670307 * 2 ^ 59
def prefixEnd_4670307 : Nat := 4983230072969 + 3 ^ 40 * 4670307 * 2
def baseEnd_4670307 : Nat := 2398112295057764136084155

theorem tailTrace_4670307 : CollatzResearch.WordTrace tailWord_4670307 prefixEnd_4670307 2398112295057764136084155 := by
  unfold tailWord_4670307
  simp only [CollatzResearch.WordTrace]
  refine ⟨170340090291282838778545175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113560060194188559185696783 170340090291282838778545175)
  ·
    refine ⟨255510135436924258167817763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170340090291282838778545175 255510135436924258167817763)
    ·
      refine ⟨383265203155386387251726645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255510135436924258167817763 383265203155386387251726645)
      ·
        refine ⟨35931112795817473804849373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 383265203155386387251726645 35931112795817473804849373)
        ·
          refine ⟨13474167298431552676818515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35931112795817473804849373 13474167298431552676818515)
          ·
            refine ⟨20211250947647329015227773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13474167298431552676818515 20211250947647329015227773)
            ·
              refine ⟨7579219105367748380710415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20211250947647329015227773 7579219105367748380710415)
              ·
                refine ⟨11368828658051622571065623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7579219105367748380710415 11368828658051622571065623)
                ·
                  refine ⟨17053242987077433856598435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11368828658051622571065623 17053242987077433856598435)
                  ·
                    refine ⟨25579864480616150784897653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17053242987077433856598435 25579864480616150784897653)
                    ·
                      refine ⟨2398112295057764136084155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25579864480616150784897653 2398112295057764136084155)
                      ·
                        rfl

theorem cell23_4670307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_4670307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670307 prefixEnd_4670307 := by exact prefixLift 4670307
  have htrace : WordTrace (prefixWord ++ tailWord_4670307) baseStart_4670307 baseEnd_4670307 := by
    simpa [prefixWord, tailWord_4670307, baseEnd_4670307] using wordTrace_append hprefix tailTrace_4670307
  have hstable : (prefixWord ++ tailWord_4670307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670307).length < 2 ^ (prefixWord ++ tailWord_4670307).sum := by decide
  have hdescent : baseEnd_4670307 < baseStart_4670307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670340 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_4670340 : Nat := 118140960795 + 4670340 * 2 ^ 59
def prefixEnd_4670340 : Nat := 4983230072969 + 3 ^ 40 * 4670340 * 2
def baseEnd_4670340 : Nat := 799376413306454168990501

theorem tailTrace_4670340 : CollatzResearch.WordTrace tailWord_4670340 prefixEnd_4670340 799376413306454168990501 := by
  unfold tailWord_4670340
  simp only [CollatzResearch.WordTrace]
  refine ⟨85170646950081642707248237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113560862600108856942997649 85170646950081642707248237)
  ·
    refine ⟨31938992606280616015218089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85170646950081642707248237 31938992606280616015218089)
    ·
      refine ⟨23954244454710462011413567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31938992606280616015218089 23954244454710462011413567)
      ·
        refine ⟨35931366682065693017120351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23954244454710462011413567 35931366682065693017120351)
        ·
          refine ⟨53897050023098539525680527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35931366682065693017120351 53897050023098539525680527)
          ·
            refine ⟨80845575034647809288520791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53897050023098539525680527 80845575034647809288520791)
            ·
              refine ⟨121268362551971713932781187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80845575034647809288520791 121268362551971713932781187)
              ·
                refine ⟨181902543827957570899171781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121268362551971713932781187 181902543827957570899171781)
                ·
                  refine ⟨34106726967742044543594709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181902543827957570899171781 34106726967742044543594709)
                  ·
                    refine ⟨799376413306454168990501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34106726967742044543594709 799376413306454168990501)
                    ·
                      rfl

theorem cell23_4670340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_4670340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670340 prefixEnd_4670340 := by exact prefixLift 4670340
  have htrace : WordTrace (prefixWord ++ tailWord_4670340) baseStart_4670340 baseEnd_4670340 := by
    simpa [prefixWord, tailWord_4670340, baseEnd_4670340] using wordTrace_append hprefix tailTrace_4670340
  have hstable : (prefixWord ++ tailWord_4670340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670340).length < 2 ^ (prefixWord ++ tailWord_4670340).sum := by decide
  have hdescent : baseEnd_4670340 < baseStart_4670340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670380 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_4670380 : Nat := 118140960795 + 4670380 * 2 ^ 59
def prefixEnd_4670380 : Nat := 4983230072969 + 3 ^ 40 * 4670380 * 2
def baseEnd_4670380 : Nat := 2398149779145542350471319

theorem tailTrace_4670380 : CollatzResearch.WordTrace tailWord_4670380 prefixEnd_4670380 2398149779145542350471319 := by
  unfold tailWord_4670380
  simp only [CollatzResearch.WordTrace]
  refine ⟨85171376410009186122976297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113561835213345581497301729 85171376410009186122976297)
  ·
    refine ⟨63878532307506889592232223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85171376410009186122976297 63878532307506889592232223)
    ·
      refine ⟨95817798461260334388348335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63878532307506889592232223 95817798461260334388348335)
      ·
        refine ⟨143726697691890501582522503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95817798461260334388348335 143726697691890501582522503)
        ·
          refine ⟨215590046537835752373783755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143726697691890501582522503 215590046537835752373783755)
          ·
            refine ⟨323385069806753628560675633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215590046537835752373783755 323385069806753628560675633)
            ·
              refine ⟨242538802355065221420506725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323385069806753628560675633 242538802355065221420506725)
              ·
                refine ⟨45476025441574729016345011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 242538802355065221420506725 45476025441574729016345011)
                ·
                  refine ⟨68214038162362093524517517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45476025441574729016345011 68214038162362093524517517)
                  ·
                    refine ⟨25580264310885785071694069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68214038162362093524517517 25580264310885785071694069)
                    ·
                      refine ⟨2398149779145542350471319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25580264310885785071694069 2398149779145542350471319)
                      ·
                        rfl

theorem cell23_4670380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_4670380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670380 prefixEnd_4670380 := by exact prefixLift 4670380
  have htrace : WordTrace (prefixWord ++ tailWord_4670380) baseStart_4670380 baseEnd_4670380 := by
    simpa [prefixWord, tailWord_4670380, baseEnd_4670380] using wordTrace_append hprefix tailTrace_4670380
  have hstable : (prefixWord ++ tailWord_4670380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670380).length < 2 ^ (prefixWord ++ tailWord_4670380).sum := by decide
  have hdescent : baseEnd_4670380 < baseStart_4670380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670388 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_4670388 : Nat := 118140960795 + 4670388 * 2 ^ 59
def prefixEnd_4670388 : Nat := 4983230072969 + 3 ^ 40 * 4670388 * 2
def baseEnd_4670388 : Nat := 2398153886990778319171283

theorem tailTrace_4670388 : CollatzResearch.WordTrace tailWord_4670388 prefixEnd_4670388 2398153886990778319171283 := by
  unfold tailWord_4670388
  simp only [CollatzResearch.WordTrace]
  refine ⟨85171522301994694806121909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113562029735992926408162545 85171522301994694806121909)
  ·
    refine ⟨7984830215812002638073929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85171522301994694806121909 7984830215812002638073929)
    ·
      refine ⟨5988622661859001978555447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7984830215812002638073929 5988622661859001978555447)
      ·
        refine ⟨8982933992788502967833171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5988622661859001978555447 8982933992788502967833171)
        ·
          refine ⟨13474400989182754451749757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8982933992788502967833171 13474400989182754451749757)
          ·
            refine ⟨5052900370943532919406159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13474400989182754451749757 5052900370943532919406159)
            ·
              refine ⟨7579350556415299379109239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5052900370943532919406159 7579350556415299379109239)
              ·
                refine ⟨11369025834622949068663859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7579350556415299379109239 11369025834622949068663859)
                ·
                  refine ⟨17053538751934423602995789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11369025834622949068663859 17053538751934423602995789)
                  ·
                    refine ⟨6395077031975408851123421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17053538751934423602995789 6395077031975408851123421)
                    ·
                      refine ⟨2398153886990778319171283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6395077031975408851123421 2398153886990778319171283)
                      ·
                        rfl

theorem cell23_4670388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_4670388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670388 prefixEnd_4670388 := by exact prefixLift 4670388
  have htrace : WordTrace (prefixWord ++ tailWord_4670388) baseStart_4670388 baseEnd_4670388 := by
    simpa [prefixWord, tailWord_4670388, baseEnd_4670388] using wordTrace_append hprefix tailTrace_4670388
  have hstable : (prefixWord ++ tailWord_4670388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670388).length < 2 ^ (prefixWord ++ tailWord_4670388).sum := by decide
  have hdescent : baseEnd_4670388 < baseStart_4670388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670507 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 6]
def baseStart_4670507 : Nat := 118140960795 + 4670507 * 2 ^ 59
def prefixEnd_4670507 : Nat := 4983230072969 + 3 ^ 40 * 4670507 * 2
def baseEnd_4670507 : Nat := 266468332354295928175915

theorem tailTrace_4670507 : CollatzResearch.WordTrace tailWord_4670507 prefixEnd_4670507 266468332354295928175915 := by
  unfold tailWord_4670507
  simp only [CollatzResearch.WordTrace]
  refine ⟨170347384890558272935825775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113564923260372181957217183 170347384890558272935825775)
  ·
    refine ⟨255521077335837409403738663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170347384890558272935825775 255521077335837409403738663)
    ·
      refine ⟨383281616003756114105607995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255521077335837409403738663 383281616003756114105607995)
      ·
        refine ⟨574922424005634171158411993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383281616003756114105607995 574922424005634171158411993)
        ·
          refine ⟨431191818004225628368808995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 574922424005634171158411993 431191818004225628368808995)
          ·
            refine ⟨646787727006338442553213493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431191818004225628368808995 646787727006338442553213493)
            ·
              refine ⟨60636349406844228989363765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 646787727006338442553213493 60636349406844228989363765)
              ·
                refine ⟨5684657756891646467752853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60636349406844228989363765 5684657756891646467752853)
                ·
                  refine ⟨266468332354295928175915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5684657756891646467752853 266468332354295928175915)
                  ·
                    rfl

theorem cell23_4670507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 6].length) (baseStart_4670507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670507 prefixEnd_4670507 := by exact prefixLift 4670507
  have htrace : WordTrace (prefixWord ++ tailWord_4670507) baseStart_4670507 baseEnd_4670507 := by
    simpa [prefixWord, tailWord_4670507, baseEnd_4670507] using wordTrace_append hprefix tailTrace_4670507
  have hstable : (prefixWord ++ tailWord_4670507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670507).length < 2 ^ (prefixWord ++ tailWord_4670507).sum := by decide
  have hdescent : baseEnd_4670507 < baseStart_4670507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670518 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_4670518 : Nat := 118140960795 + 4670518 * 2 ^ 59
def prefixEnd_4670518 : Nat := 4983230072969 + 3 ^ 40 * 4670518 * 2
def baseEnd_4670518 : Nat := 2398220639475862810545685

theorem tailTrace_4670518 : CollatzResearch.WordTrace tailWord_4670518 prefixEnd_4670518 2398220639475862810545685 := by
  unfold tailWord_4670518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10646736630844901363404763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113565190729012281209650805 10646736630844901363404763)
  ·
    refine ⟨15970104946267352045107145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10646736630844901363404763 15970104946267352045107145)
    ·
      refine ⟨11977578709700514033830359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15970104946267352045107145 11977578709700514033830359)
      ·
        refine ⟨17966368064550771050745539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11977578709700514033830359 17966368064550771050745539)
        ·
          refine ⟨26949552096826156576118309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17966368064550771050745539 26949552096826156576118309)
          ·
            refine ⟨5053041018154904358022183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26949552096826156576118309 5053041018154904358022183)
            ·
              refine ⟨7579561527232356537033275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5053041018154904358022183 7579561527232356537033275)
              ·
                refine ⟨11369342290848534805549913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7579561527232356537033275 11369342290848534805549913)
                ·
                  refine ⟨8527006718136401104162435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11369342290848534805549913 8527006718136401104162435)
                  ·
                    refine ⟨12790510077204601656243653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8527006718136401104162435 12790510077204601656243653)
                    ·
                      refine ⟨2398220639475862810545685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12790510077204601656243653 2398220639475862810545685)
                      ·
                        rfl

theorem cell23_4670518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_4670518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670518 prefixEnd_4670518 := by exact prefixLift 4670518
  have htrace : WordTrace (prefixWord ++ tailWord_4670518) baseStart_4670518 baseEnd_4670518 := by
    simpa [prefixWord, tailWord_4670518, baseEnd_4670518] using wordTrace_append hprefix tailTrace_4670518
  have hstable : (prefixWord ++ tailWord_4670518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670518).length < 2 ^ (prefixWord ++ tailWord_4670518).sum := by decide
  have hdescent : baseEnd_4670518 < baseStart_4670518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670521 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 2, 2, 3]
def baseStart_4670521 : Nat := 118140960795 + 4670521 * 2 ^ 59
def prefixEnd_4670521 : Nat := 4983230072969 + 3 ^ 40 * 4670521 * 2
def baseEnd_4670521 : Nat := 2398222179917826298808171

theorem tailTrace_4670521 : CollatzResearch.WordTrace tailWord_4670521 prefixEnd_4670521 2398222179917826298808171 := by
  unfold tailWord_4670521
  simp only [CollatzResearch.WordTrace]
  refine ⟨170347895512507553326835417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113565263675005035551223611 170347895512507553326835417)
  ·
    refine ⟨127760921634380664995126563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170347895512507553326835417 127760921634380664995126563)
    ·
      refine ⟨191641382451570997492689845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127760921634380664995126563 191641382451570997492689845)
      ·
        refine ⟨17966379604834781014939673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191641382451570997492689845 17966379604834781014939673)
        ·
          refine ⟨13474784703626085761204755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17966379604834781014939673 13474784703626085761204755)
          ·
            refine ⟨20212177055439128641807133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13474784703626085761204755 20212177055439128641807133)
            ·
              refine ⟨7579566395789673240677675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20212177055439128641807133 7579566395789673240677675)
              ·
                refine ⟨11369349593684509861016513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7579566395789673240677675 11369349593684509861016513)
                ·
                  refine ⟨8527012195263382395762385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11369349593684509861016513 8527012195263382395762385)
                  ·
                    refine ⟨6395259146447536796821789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8527012195263382395762385 6395259146447536796821789)
                    ·
                      refine ⟨2398222179917826298808171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6395259146447536796821789 2398222179917826298808171)
                      ·
                        rfl

theorem cell23_4670521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_4670521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670521 prefixEnd_4670521 := by exact prefixLift 4670521
  have htrace : WordTrace (prefixWord ++ tailWord_4670521) baseStart_4670521 baseEnd_4670521 := by
    simpa [prefixWord, tailWord_4670521, baseEnd_4670521] using wordTrace_append hprefix tailTrace_4670521
  have hstable : (prefixWord ++ tailWord_4670521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670521).length < 2 ^ (prefixWord ++ tailWord_4670521).sum := by decide
  have hdescent : baseEnd_4670521 < baseStart_4670521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670537 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 5, 5]
def baseStart_4670537 : Nat := 118140960795 + 4670537 * 2 ^ 59
def prefixEnd_4670537 : Nat := 4983230072969 + 3 ^ 40 * 4670537 * 2
def baseEnd_4670537 : Nat := 799410131869432745402699

theorem tailTrace_4670537 : CollatzResearch.WordTrace tailWord_4670537 prefixEnd_4670537 799410131869432745402699 := by
  unfold tailWord_4670537
  simp only [CollatzResearch.WordTrace]
  refine ⟨170348479080449588059417865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113565652720299725372945243 170348479080449588059417865)
  ·
    refine ⟨127761359310337191044563399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170348479080449588059417865 127761359310337191044563399)
    ·
      refine ⟨191642038965505786566845099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127761359310337191044563399 191642038965505786566845099)
      ·
        refine ⟨287463058448258679850267649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191642038965505786566845099 287463058448258679850267649)
        ·
          refine ⟨215597293836194009887700737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287463058448258679850267649 215597293836194009887700737)
          ·
            refine ⟨161697970377145507415775553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215597293836194009887700737 161697970377145507415775553)
            ·
              refine ⟨121273477782859130561831665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161697970377145507415775553 121273477782859130561831665)
              ·
                refine ⟨90955108337144347921373749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121273477782859130561831665 90955108337144347921373749)
                ·
                  refine ⟨8527041406607282617628789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90955108337144347921373749 8527041406607282617628789)
                  ·
                    refine ⟨799410131869432745402699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8527041406607282617628789 799410131869432745402699)
                    ·
                      rfl

theorem cell23_4670537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_4670537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670537 prefixEnd_4670537 := by exact prefixLift 4670537
  have htrace : WordTrace (prefixWord ++ tailWord_4670537) baseStart_4670537 baseEnd_4670537 := by
    simpa [prefixWord, tailWord_4670537, baseEnd_4670537] using wordTrace_append hprefix tailTrace_4670537
  have hstable : (prefixWord ++ tailWord_4670537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670537).length < 2 ^ (prefixWord ++ tailWord_4670537).sum := by decide
  have hdescent : baseEnd_4670537 < baseStart_4670537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670541 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 6]
def baseStart_4670541 : Nat := 118140960795 + 4670541 * 2 ^ 59
def prefixEnd_4670541 : Nat := 4983230072969 + 3 ^ 40 * 4670541 * 2
def baseEnd_4670541 : Nat := 266470272170101802284231

theorem tailTrace_4670541 : CollatzResearch.WordTrace tailWord_4670541 prefixEnd_4670541 266470272170101802284231 := by
  unfold tailWord_4670541
  simp only [CollatzResearch.WordTrace]
  refine ⟨170348624972435096742563477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113565749981623397828375651 170348624972435096742563477)
  ·
    refine ⟨7985091795582895159807663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 170348624972435096742563477 7985091795582895159807663)
    ·
      refine ⟨11977637693374342739711495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7985091795582895159807663 11977637693374342739711495)
      ·
        refine ⟨17966456540061514109567243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11977637693374342739711495 17966456540061514109567243)
        ·
          refine ⟨26949684810092271164350865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17966456540061514109567243 26949684810092271164350865)
          ·
            refine ⟨20212263607569203373263149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26949684810092271164350865 20212263607569203373263149)
            ·
              refine ⟨7579598852838451264973681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20212263607569203373263149 7579598852838451264973681)
              ·
                refine ⟨5684699139628838448730261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7579598852838451264973681 5684699139628838448730261)
                ·
                  refine ⟨266470272170101802284231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5684699139628838448730261 266470272170101802284231)
                  ·
                    rfl

theorem cell23_4670541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_4670541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670541 prefixEnd_4670541 := by exact prefixLift 4670541
  have htrace : WordTrace (prefixWord ++ tailWord_4670541) baseStart_4670541 baseEnd_4670541 := by
    simpa [prefixWord, tailWord_4670541, baseEnd_4670541] using wordTrace_append hprefix tailTrace_4670541
  have hstable : (prefixWord ++ tailWord_4670541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670541).length < 2 ^ (prefixWord ++ tailWord_4670541).sum := by decide
  have hdescent : baseEnd_4670541 < baseStart_4670541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670584 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 4, 4]
def baseStart_4670584 : Nat := 118140960795 + 4670584 * 2 ^ 59
def prefixEnd_4670584 : Nat := 4983230072969 + 3 ^ 40 * 4670584 * 2
def baseEnd_4670584 : Nat := 799418176399686517440127

theorem tailTrace_4670584 : CollatzResearch.WordTrace tailWord_4670584 prefixEnd_4670584 799418176399686517440127 := by
  unfold tailWord_4670584
  simp only [CollatzResearch.WordTrace]
  refine ⟨85175096655639657543189403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113566795540852876724252537 85175096655639657543189403)
  ·
    refine ⟨127762644983459486314784105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85175096655639657543189403 127762644983459486314784105)
    ·
      refine ⟨95821983737594614736088079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127762644983459486314784105 95821983737594614736088079)
      ·
        refine ⟨143732975606391922104132119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95821983737594614736088079 143732975606391922104132119)
        ·
          refine ⟨215599463409587883156198179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143732975606391922104132119 215599463409587883156198179)
          ·
            refine ⟨323399195114381824734297269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215599463409587883156198179 323399195114381824734297269)
            ·
              refine ⟨30318674541973296068840369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 323399195114381824734297269 30318674541973296068840369)
              ·
                refine ⟨22739005906479972051630277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30318674541973296068840369 22739005906479972051630277)
                ·
                  refine ⟨4263563607464994759680677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22739005906479972051630277 4263563607464994759680677)
                  ·
                    refine ⟨799418176399686517440127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4263563607464994759680677 799418176399686517440127)
                    ·
                      rfl

theorem cell23_4670584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_4670584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670584 prefixEnd_4670584 := by exact prefixLift 4670584
  have htrace : WordTrace (prefixWord ++ tailWord_4670584) baseStart_4670584 baseEnd_4670584 := by
    simpa [prefixWord, tailWord_4670584, baseEnd_4670584] using wordTrace_append hprefix tailTrace_4670584
  have hstable : (prefixWord ++ tailWord_4670584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670584).length < 2 ^ (prefixWord ++ tailWord_4670584).sum := by decide
  have hdescent : baseEnd_4670584 < baseStart_4670584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670618 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 2, 4]
def baseStart_4670618 : Nat := 118140960795 + 4670618 * 2 ^ 59
def prefixEnd_4670618 : Nat := 4983230072969 + 3 ^ 40 * 4670618 * 2
def baseEnd_4670618 : Nat := 799423995847104139765075

theorem tailTrace_4670618 : CollatzResearch.WordTrace tailWord_4670618 prefixEnd_4670618 799423995847104139765075 := by
  unfold tailWord_4670618
  simp only [CollatzResearch.WordTrace]
  refine ⟨42587858348289034723279127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113567622262104092595411005 42587858348289034723279127)
  ·
    refine ⟨63881787522433552084918691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42587858348289034723279127 63881787522433552084918691)
    ·
      refine ⟨95822681283650328127378037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63881787522433552084918691 95822681283650328127378037)
      ·
        refine ⟨8983376370342218261941691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95822681283650328127378037 8983376370342218261941691)
        ·
          refine ⟨13475064555513327392912537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8983376370342218261941691 13475064555513327392912537)
          ·
            refine ⟨10106298416634995544684403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13475064555513327392912537 10106298416634995544684403)
            ·
              refine ⟨15159447624952493317026605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10106298416634995544684403 15159447624952493317026605)
              ·
                refine ⟨5684792859357184993884977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15159447624952493317026605 5684792859357184993884977)
                ·
                  refine ⟨4263594644517888745413733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5684792859357184993884977 4263594644517888745413733)
                  ·
                    refine ⟨799423995847104139765075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4263594644517888745413733 799423995847104139765075)
                    ·
                      rfl

theorem cell23_4670618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_4670618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670618 prefixEnd_4670618 := by exact prefixLift 4670618
  have htrace : WordTrace (prefixWord ++ tailWord_4670618) baseStart_4670618 baseEnd_4670618 := by
    simpa [prefixWord, tailWord_4670618, baseEnd_4670618] using wordTrace_append hprefix tailTrace_4670618
  have hstable : (prefixWord ++ tailWord_4670618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670618).length < 2 ^ (prefixWord ++ tailWord_4670618).sum := by decide
  have hdescent : baseEnd_4670618 < baseStart_4670618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670628 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_4670628 : Nat := 118140960795 + 4670628 * 2 ^ 59
def prefixEnd_4670628 : Nat := 4983230072969 + 3 ^ 40 * 4670628 * 2
def baseEnd_4670628 : Nat := 2398277122347857380170179

theorem tailTrace_4670628 : CollatzResearch.WordTrace tailWord_4670628 prefixEnd_4670628 2398277122347857380170179 := by
  unfold tailWord_4670628
  simp only [CollatzResearch.WordTrace]
  refine ⟨85175899061559955300490269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113567865415413273733987025 85175899061559955300490269)
  ·
    refine ⟨31940962148084983237683851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85175899061559955300490269 31940962148084983237683851)
    ·
      refine ⟨47911443222127474856525777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31940962148084983237683851 47911443222127474856525777)
      ·
        refine ⟨35933582416595606142394333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47911443222127474856525777 35933582416595606142394333)
        ·
          refine ⟨13475093406223352303397875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35933582416595606142394333 13475093406223352303397875)
          ·
            refine ⟨20212640109335028455096813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13475093406223352303397875 20212640109335028455096813)
            ·
              refine ⟨7579740041000635670661305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20212640109335028455096813 7579740041000635670661305)
              ·
                refine ⟨5684805030750476752995979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7579740041000635670661305 5684805030750476752995979)
                ·
                  refine ⟨8527207546125715129493969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5684805030750476752995979 8527207546125715129493969)
                  ·
                    refine ⟨6395405659594286347120477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8527207546125715129493969 6395405659594286347120477)
                    ·
                      refine ⟨2398277122347857380170179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6395405659594286347120477 2398277122347857380170179)
                      ·
                        rfl

theorem cell23_4670628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_4670628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670628 prefixEnd_4670628 := by exact prefixLift 4670628
  have htrace : WordTrace (prefixWord ++ tailWord_4670628) baseStart_4670628 baseEnd_4670628 := by
    simpa [prefixWord, tailWord_4670628, baseEnd_4670628] using wordTrace_append hprefix tailTrace_4670628
  have hstable : (prefixWord ++ tailWord_4670628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670628).length < 2 ^ (prefixWord ++ tailWord_4670628).sum := by decide
  have hdescent : baseEnd_4670628 < baseStart_4670628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670641 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 3, 3, 3]
def baseStart_4670641 : Nat := 118140960795 + 4670641 * 2 ^ 59
def prefixEnd_4670641 : Nat := 4983230072969 + 3 ^ 40 * 4670641 * 2
def baseEnd_4670641 : Nat := 2398283797596365829307619

theorem tailTrace_4670641 : CollatzResearch.WordTrace tailWord_4670641 prefixEnd_4670641 2398283797596365829307619 := by
  unfold tailWord_4670641
  simp only [CollatzResearch.WordTrace]
  refine ⟨170352272272072813821203777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113568181514715209214135851 170352272272072813821203777)
  ·
    refine ⟨127764204204054610365902833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170352272272072813821203777 127764204204054610365902833)
    ·
      refine ⟨95823153153040957774427125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127764204204054610365902833 95823153153040957774427125)
      ·
        refine ⟨8983420608097589791352543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95823153153040957774427125 8983420608097589791352543)
        ·
          refine ⟨13475130912146384687028815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8983420608097589791352543 13475130912146384687028815)
          ·
            refine ⟨20212696368219577030543223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13475130912146384687028815 20212696368219577030543223)
            ·
              refine ⟨30319044552329365545814835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20212696368219577030543223 30319044552329365545814835)
              ·
                refine ⟨45478566828494048318722253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30319044552329365545814835 45478566828494048318722253)
                ·
                  refine ⟨17054462560685268119520845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45478566828494048318722253 17054462560685268119520845)
                  ·
                    refine ⟨6395423460256975544820317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17054462560685268119520845 6395423460256975544820317)
                    ·
                      refine ⟨2398283797596365829307619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6395423460256975544820317 2398283797596365829307619)
                      ·
                        rfl

theorem cell23_4670641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_4670641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670641 prefixEnd_4670641 := by exact prefixLift 4670641
  have htrace : WordTrace (prefixWord ++ tailWord_4670641) baseStart_4670641 baseEnd_4670641 := by
    simpa [prefixWord, tailWord_4670641, baseEnd_4670641] using wordTrace_append hprefix tailTrace_4670641
  have hstable : (prefixWord ++ tailWord_4670641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670641).length < 2 ^ (prefixWord ++ tailWord_4670641).sum := by decide
  have hdescent : baseEnd_4670641 < baseStart_4670641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670664 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_4670664 : Nat := 118140960795 + 4670664 * 2 ^ 59
def prefixEnd_4670664 : Nat := 4983230072969 + 3 ^ 40 * 4670664 * 2
def baseEnd_4670664 : Nat := 2398295607651419239320013

theorem tailTrace_4670664 : CollatzResearch.WordTrace tailWord_4670664 prefixEnd_4670664 2398295607651419239320013 := by
  unfold tailWord_4670664
  simp only [CollatzResearch.WordTrace]
  refine ⟨85176555575494744374645523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113568740767326325832860697 85176555575494744374645523)
  ·
    refine ⟨127764833363242116561968285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85176555575494744374645523 127764833363242116561968285)
    ·
      refine ⟨47911812511215793710738107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127764833363242116561968285 47911812511215793710738107)
      ·
        refine ⟨71867718766823690566107161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47911812511215793710738107 71867718766823690566107161)
        ·
          refine ⟨53900789075117767924580371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71867718766823690566107161 53900789075117767924580371)
          ·
            refine ⟨80851183612676651886870557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53900789075117767924580371 80851183612676651886870557)
            ·
              refine ⟨30319193854753744457576459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80851183612676651886870557 30319193854753744457576459)
              ·
                refine ⟨45478790782130616686364689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30319193854753744457576459 45478790782130616686364689)
                ·
                  refine ⟨34109093086597962514773517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45478790782130616686364689 34109093086597962514773517)
                  ·
                    refine ⟨12790909907474235943040069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34109093086597962514773517 12790909907474235943040069)
                    ·
                      refine ⟨2398295607651419239320013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12790909907474235943040069 2398295607651419239320013)
                      ·
                        rfl

theorem cell23_4670664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_4670664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670664 prefixEnd_4670664 := by exact prefixLift 4670664
  have htrace : WordTrace (prefixWord ++ tailWord_4670664) baseStart_4670664 baseEnd_4670664 := by
    simpa [prefixWord, tailWord_4670664, baseEnd_4670664] using wordTrace_append hprefix tailTrace_4670664
  have hstable : (prefixWord ++ tailWord_4670664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670664).length < 2 ^ (prefixWord ++ tailWord_4670664).sum := by decide
  have hdescent : baseEnd_4670664 < baseStart_4670664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670698 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_4670698 : Nat := 118140960795 + 4670698 * 2 ^ 59
def prefixEnd_4670698 : Nat := 4983230072969 + 3 ^ 40 * 4670698 * 2
def baseEnd_4670698 : Nat := 2398313065993672106294857

theorem tailTrace_4670698 : CollatzResearch.WordTrace tailWord_4670698 prefixEnd_4670698 2398313065993672106294857 := by
  unfold tailWord_4670698
  simp only [CollatzResearch.WordTrace]
  refine ⟨42588587808216578139007187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113569567488577541704019165 42588587808216578139007187)
  ·
    refine ⟨63882881712324867208510781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42588587808216578139007187 63882881712324867208510781)
    ·
      refine ⟨23956080642121825203191543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63882881712324867208510781 23956080642121825203191543)
      ·
        refine ⟨35934120963182737804787315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23956080642121825203191543 35934120963182737804787315)
        ·
          refine ⟨53901181444774106707180973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35934120963182737804787315 53901181444774106707180973)
          ·
            refine ⟨20212943041790290015192865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53901181444774106707180973 20212943041790290015192865)
            ·
              refine ⟨15159707281342717511394649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20212943041790290015192865 15159707281342717511394649)
              ·
                refine ⟨11369780461007038133545987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15159707281342717511394649 11369780461007038133545987)
                ·
                  refine ⟨17054670691510557200318981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11369780461007038133545987 17054670691510557200318981)
                  ·
                    refine ⟨3197750754658229475059809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17054670691510557200318981 3197750754658229475059809)
                    ·
                      refine ⟨2398313065993672106294857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197750754658229475059809 2398313065993672106294857)
                      ·
                        rfl

theorem cell23_4670698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_4670698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670698 prefixEnd_4670698 := by exact prefixLift 4670698
  have htrace : WordTrace (prefixWord ++ tailWord_4670698) baseStart_4670698 baseEnd_4670698 := by
    simpa [prefixWord, tailWord_4670698, baseEnd_4670698] using wordTrace_append hprefix tailTrace_4670698
  have hstable : (prefixWord ++ tailWord_4670698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670698).length < 2 ^ (prefixWord ++ tailWord_4670698).sum := by decide
  have hdescent : baseEnd_4670698 < baseStart_4670698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670721 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 7]
def baseStart_4670721 : Nat := 118140960795 + 4670721 * 2 ^ 59
def prefixEnd_4670721 : Nat := 4983230072969 + 3 ^ 40 * 4670721 * 2
def baseEnd_4670721 : Nat := 266480541783191724034139

theorem tailTrace_4670721 : CollatzResearch.WordTrace tailWord_4670721 prefixEnd_4670721 266480541783191724034139 := by
  unfold tailWord_4670721
  simp only [CollatzResearch.WordTrace]
  refine ⟨170355190111782987484116017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113570126741188658322744011 170355190111782987484116017)
  ·
    refine ⟨127766392583837240613087013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170355190111782987484116017 127766392583837240613087013)
    ·
      refine ⟨23956198609469482614953815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127766392583837240613087013 23956198609469482614953815)
      ·
        refine ⟨35934297914204223922430723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23956198609469482614953815 35934297914204223922430723)
        ·
          refine ⟨53901446871306335883646085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35934297914204223922430723 53901446871306335883646085)
          ·
            refine ⟨10106521288369937978183641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53901446871306335883646085 10106521288369937978183641)
            ·
              refine ⟨7579890966277453483637731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10106521288369937978183641 7579890966277453483637731)
              ·
                refine ⟨11369836449416180225456597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7579890966277453483637731 11369836449416180225456597)
                ·
                  refine ⟨266480541783191724034139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11369836449416180225456597 266480541783191724034139)
                  ·
                    rfl

theorem cell23_4670721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 7].length) (baseStart_4670721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670721 prefixEnd_4670721 := by exact prefixLift 4670721
  have htrace : WordTrace (prefixWord ++ tailWord_4670721) baseStart_4670721 baseEnd_4670721 := by
    simpa [prefixWord, tailWord_4670721, baseEnd_4670721] using wordTrace_append hprefix tailTrace_4670721
  have hstable : (prefixWord ++ tailWord_4670721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670721).length < 2 ^ (prefixWord ++ tailWord_4670721).sum := by decide
  have hdescent : baseEnd_4670721 < baseStart_4670721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670731 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 3]
def baseStart_4670731 : Nat := 118140960795 + 4670731 * 2 ^ 59
def prefixEnd_4670731 : Nat := 4983230072969 + 3 ^ 40 * 4670731 * 2
def baseEnd_4670731 : Nat := 2398330010855270477182205

theorem tailTrace_4670731 : CollatzResearch.WordTrace tailWord_4670731 prefixEnd_4670731 2398330010855270477182205 := by
  unfold tailWord_4670731
  simp only [CollatzResearch.WordTrace]
  refine ⟨170355554841746759191980047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113570369894497839461320031 170355554841746759191980047)
  ·
    refine ⟨255533332262620138787970071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170355554841746759191980047 255533332262620138787970071)
    ·
      refine ⟨383299998393930208181955107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255533332262620138787970071 383299998393930208181955107)
      ·
        refine ⟨574949997590895312272932661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383299998393930208181955107 574949997590895312272932661)
        ·
          refine ⟨53901562274146435525587437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 574949997590895312272932661 53901562274146435525587437)
          ·
            refine ⟨20213085852804913322095289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53901562274146435525587437 20213085852804913322095289)
            ·
              refine ⟨15159814389603684991571467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20213085852804913322095289 15159814389603684991571467)
              ·
                refine ⟨22739721584405527487357201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15159814389603684991571467 22739721584405527487357201)
                ·
                  refine ⟨17054791188304145615517901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22739721584405527487357201 17054791188304145615517901)
                  ·
                    refine ⟨6395546695614054605819213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17054791188304145615517901 6395546695614054605819213)
                    ·
                      refine ⟨2398330010855270477182205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6395546695614054605819213 2398330010855270477182205)
                      ·
                        rfl

theorem cell23_4670731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 3].length) (baseStart_4670731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670731 prefixEnd_4670731 := by exact prefixLift 4670731
  have htrace : WordTrace (prefixWord ++ tailWord_4670731) baseStart_4670731 baseEnd_4670731 := by
    simpa [prefixWord, tailWord_4670731, baseEnd_4670731] using wordTrace_append hprefix tailTrace_4670731
  have hstable : (prefixWord ++ tailWord_4670731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670731).length < 2 ^ (prefixWord ++ tailWord_4670731).sum := by decide
  have hdescent : baseEnd_4670731 < baseStart_4670731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670732 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 2, 2, 2]
def baseStart_4670732 : Nat := 118140960795 + 4670732 * 2 ^ 59
def prefixEnd_4670732 : Nat := 4983230072969 + 3 ^ 40 * 4670732 * 2
def baseEnd_4670732 : Nat := 2398330524335924973269701

theorem tailTrace_4670732 : CollatzResearch.WordTrace tailWord_4670732 prefixEnd_4670732 2398330524335924973269701 := by
  unfold tailWord_4670732
  simp only [CollatzResearch.WordTrace]
  refine ⟨85177795657371568181383225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113570394209828757575177633 85177795657371568181383225)
  ·
    refine ⟨63883346743028676136037419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85177795657371568181383225 63883346743028676136037419)
    ·
      refine ⟨95825020114543014204056129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63883346743028676136037419 95825020114543014204056129)
      ·
        refine ⟨71868765085907260653042097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95825020114543014204056129 71868765085907260653042097)
        ·
          refine ⟨53901573814430445489781573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71868765085907260653042097 53901573814430445489781573)
          ·
            refine ⟨10106545090205708529334045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53901573814430445489781573 10106545090205708529334045)
            ·
              refine ⟨3789954408827140698500267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10106545090205708529334045 3789954408827140698500267)
              ·
                refine ⟨5684931613240711047750401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3789954408827140698500267 5684931613240711047750401)
                ·
                  refine ⟨4263698709930533285812801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5684931613240711047750401 4263698709930533285812801)
                  ·
                    refine ⟨3197774032447899964359601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4263698709930533285812801 3197774032447899964359601)
                    ·
                      refine ⟨2398330524335924973269701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197774032447899964359601 2398330524335924973269701)
                      ·
                        rfl

theorem cell23_4670732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_4670732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670732 prefixEnd_4670732 := by exact prefixLift 4670732
  have htrace : WordTrace (prefixWord ++ tailWord_4670732) baseStart_4670732 baseEnd_4670732 := by
    simpa [prefixWord, tailWord_4670732, baseEnd_4670732] using wordTrace_append hprefix tailTrace_4670732
  have hstable : (prefixWord ++ tailWord_4670732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670732).length < 2 ^ (prefixWord ++ tailWord_4670732).sum := by decide
  have hdescent : baseEnd_4670732 < baseStart_4670732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670771 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 4]
def baseStart_4670771 : Nat := 118140960795 + 4670771 * 2 ^ 59
def prefixEnd_4670771 : Nat := 4983230072969 + 3 ^ 40 * 4670771 * 2
def baseEnd_4670771 : Nat := 2398350550081450320682021

theorem tailTrace_4670771 : CollatzResearch.WordTrace tailWord_4670771 prefixEnd_4670771 2398350550081450320682021 := by
  unfold tailWord_4670771
  simp only [CollatzResearch.WordTrace]
  refine ⟨170357013761601846023436167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113571342507734564015624111 170357013761601846023436167)
  ·
    refine ⟨255535520642402769035154251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170357013761601846023436167 255535520642402769035154251)
    ·
      refine ⟨383303280963604153552731377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255535520642402769035154251 383303280963604153552731377)
      ·
        refine ⟨287477460722703115164548533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383303280963604153552731377 287477460722703115164548533)
        ·
          refine ⟨26951011942753417046676425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 287477460722703115164548533 26951011942753417046676425)
          ·
            refine ⟨20213258957065062785007319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26951011942753417046676425 20213258957065062785007319)
            ·
              refine ⟨30319888435597594177510979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20213258957065062785007319 30319888435597594177510979)
              ·
                refine ⟨45479832653396391266266469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30319888435597594177510979 45479832653396391266266469)
                ·
                  refine ⟨8527468622511823362424963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45479832653396391266266469 8527468622511823362424963)
                  ·
                    refine ⟨12791202933767735043637445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8527468622511823362424963 12791202933767735043637445)
                    ·
                      refine ⟨2398350550081450320682021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12791202933767735043637445 2398350550081450320682021)
                      ·
                        rfl

theorem cell23_4670771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_4670771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670771 prefixEnd_4670771 := by exact prefixLift 4670771
  have htrace : WordTrace (prefixWord ++ tailWord_4670771) baseStart_4670771 baseEnd_4670771 := by
    simpa [prefixWord, tailWord_4670771, baseEnd_4670771] using wordTrace_append hprefix tailTrace_4670771
  have hstable : (prefixWord ++ tailWord_4670771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670771).length < 2 ^ (prefixWord ++ tailWord_4670771).sum := by decide
  have hdescent : baseEnd_4670771 < baseStart_4670771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670808 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 2, 2, 3]
def baseStart_4670808 : Nat := 118140960795 + 4670808 * 2 ^ 59
def prefixEnd_4670808 : Nat := 4983230072969 + 3 ^ 40 * 4670808 * 2
def baseEnd_4670808 : Nat := 2398369548865666675919351

theorem tailTrace_4670808 : CollatzResearch.WordTrace tailWord_4670808 prefixEnd_4670808 2398369548865666675919351 := by
  unfold tailWord_4670808
  simp only [CollatzResearch.WordTrace]
  refine ⟨85179181631233900671266539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113572242174978534228355385 85179181631233900671266539)
  ·
    refine ⟨127768772446850851006899809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85179181631233900671266539 127768772446850851006899809)
    ·
      refine ⟨95826579335138138255174857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127768772446850851006899809 95826579335138138255174857)
      ·
        refine ⟨71869934501353603691381143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95826579335138138255174857 71869934501353603691381143)
        ·
          refine ⟨107804901752030405537071715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71869934501353603691381143 107804901752030405537071715)
          ·
            refine ⟨161707352628045608305607573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107804901752030405537071715 161707352628045608305607573)
            ·
              refine ⟨7580032154439637889325355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 161707352628045608305607573 7580032154439637889325355)
              ·
                refine ⟨11370048231659456833988033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7580032154439637889325355 11370048231659456833988033)
                ·
                  refine ⟨8527536173744592625491025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11370048231659456833988033 8527536173744592625491025)
                  ·
                    refine ⟨6395652130308444469118269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8527536173744592625491025 6395652130308444469118269)
                    ·
                      refine ⟨2398369548865666675919351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6395652130308444469118269 2398369548865666675919351)
                      ·
                        rfl

theorem cell23_4670808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_4670808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670808 prefixEnd_4670808 := by exact prefixLift 4670808
  have htrace : WordTrace (prefixWord ++ tailWord_4670808) baseStart_4670808 baseEnd_4670808 := by
    simpa [prefixWord, tailWord_4670808, baseEnd_4670808] using wordTrace_append hprefix tailTrace_4670808
  have hstable : (prefixWord ++ tailWord_4670808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670808).length < 2 ^ (prefixWord ++ tailWord_4670808).sum := by decide
  have hdescent : baseEnd_4670808 < baseStart_4670808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670828 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 6]
def baseStart_4670828 : Nat := 118140960795 + 4670828 * 2 ^ 59
def prefixEnd_4670828 : Nat := 4983230072969 + 3 ^ 40 * 4670828 * 2
def baseEnd_4670828 : Nat := 266486646497639621963251

theorem tailTrace_4670828 : CollatzResearch.WordTrace tailWord_4670828 prefixEnd_4670828 266486646497639621963251 := by
  unfold tailWord_4670828
  simp only [CollatzResearch.WordTrace]
  refine ⟨85179546361197672379130569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113572728481596896505507425 85179546361197672379130569)
  ·
    refine ⟨63884659770898254284347927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85179546361197672379130569 63884659770898254284347927)
    ·
      refine ⟨95826989656347381426521891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63884659770898254284347927 95826989656347381426521891)
      ·
        refine ⟨143740484484521072139782837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95826989656347381426521891 143740484484521072139782837)
        ·
          refine ⟨13475670420423850513104641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143740484484521072139782837 13475670420423850513104641)
          ·
            refine ⟨10106752815317887884828481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13475670420423850513104641 10106752815317887884828481)
            ·
              refine ⟨7580064611488415913621361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10106752815317887884828481 7580064611488415913621361)
              ·
                refine ⟨5685048458616311935216021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7580064611488415913621361 5685048458616311935216021)
                ·
                  refine ⟨266486646497639621963251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5685048458616311935216021 266486646497639621963251)
                  ·
                    rfl

theorem cell23_4670828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_4670828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670828 prefixEnd_4670828 := by exact prefixLift 4670828
  have htrace : WordTrace (prefixWord ++ tailWord_4670828) baseStart_4670828 baseEnd_4670828 := by
    simpa [prefixWord, tailWord_4670828, baseEnd_4670828] using wordTrace_append hprefix tailTrace_4670828
  have hstable : (prefixWord ++ tailWord_4670828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670828).length < 2 ^ (prefixWord ++ tailWord_4670828).sum := by decide
  have hdescent : baseEnd_4670828 < baseStart_4670828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670841 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 3, 5]
def baseStart_4670841 : Nat := 118140960795 + 4670841 * 2 ^ 59
def prefixEnd_4670841 : Nat := 4983230072969 + 3 ^ 40 * 4670841 * 2
def baseEnd_4670841 : Nat := 799462164575755015602233

theorem tailTrace_4670841 : CollatzResearch.WordTrace tailWord_4670841 prefixEnd_4670841 799462164575755015602233 := by
  unfold tailWord_4670841
  simp only [CollatzResearch.WordTrace]
  refine ⟨170359566871348247978484377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113573044580898831985656251 170359566871348247978484377)
  ·
    refine ⟨127769675153511185983863283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170359566871348247978484377 127769675153511185983863283)
    ·
      refine ⟨191654512730266778975794925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127769675153511185983863283 191654512730266778975794925)
      ·
        refine ⟨71870442273850042115923097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191654512730266778975794925 71870442273850042115923097)
        ·
          refine ⟨53902831705387531586942323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71870442273850042115923097 53902831705387531586942323)
          ·
            refine ⟨80854247558081297380413485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53902831705387531586942323 80854247558081297380413485)
            ·
              refine ⟨30320342834280486517655057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80854247558081297380413485 30320342834280486517655057)
              ·
                refine ⟨22740257125710364888241293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30320342834280486517655057 22740257125710364888241293)
                ·
                  refine ⟨8527596422141386833090485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22740257125710364888241293 8527596422141386833090485)
                  ·
                    refine ⟨799462164575755015602233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8527596422141386833090485 799462164575755015602233)
                    ·
                      rfl

theorem cell23_4670841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_4670841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670841 prefixEnd_4670841 := by exact prefixLift 4670841
  have htrace : WordTrace (prefixWord ++ tailWord_4670841) baseStart_4670841 baseEnd_4670841 := by
    simpa [prefixWord, tailWord_4670841, baseEnd_4670841] using wordTrace_append hprefix tailTrace_4670841
  have hstable : (prefixWord ++ tailWord_4670841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670841).length < 2 ^ (prefixWord ++ tailWord_4670841).sum := by decide
  have hdescent : baseEnd_4670841 < baseStart_4670841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670848 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 4, 3, 2]
def baseStart_4670848 : Nat := 118140960795 + 4670848 * 2 ^ 59
def prefixEnd_4670848 : Nat := 4983230072969 + 3 ^ 40 * 4670848 * 2
def baseEnd_4670848 : Nat := 2398390088091846519419167

theorem tailTrace_4670848 : CollatzResearch.WordTrace tailWord_4670848 prefixEnd_4670848 2398390088091846519419167 := by
  unfold tailWord_4670848
  simp only [CollatzResearch.WordTrace]
  refine ⟨85179911091161444086994599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113573214788215258782659465 85179911091161444086994599)
  ·
    refine ⟨127769866636742166130491899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85179911091161444086994599 127769866636742166130491899)
    ·
      refine ⟨191654799955113249195737849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127769866636742166130491899 191654799955113249195737849)
      ·
        refine ⟨143741099966334936896803387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191654799955113249195737849 143741099966334936896803387)
        ·
          refine ⟨215611649949502405345205081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143741099966334936896803387 215611649949502405345205081)
          ·
            refine ⟨161708737462126804008903811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215611649949502405345205081 161708737462126804008903811)
            ·
              refine ⟨242563106193190206013355717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161708737462126804008903811 242563106193190206013355717)
              ·
                refine ⟨45480582411223163627504197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 242563106193190206013355717 45480582411223163627504197)
                ·
                  refine ⟨8527609202104343180157037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45480582411223163627504197 8527609202104343180157037)
                  ·
                    refine ⟨3197853450789128692558889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8527609202104343180157037 3197853450789128692558889)
                    ·
                      refine ⟨2398390088091846519419167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197853450789128692558889 2398390088091846519419167)
                      ·
                        rfl

theorem cell23_4670848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 3, 2].length) (baseStart_4670848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670848 prefixEnd_4670848 := by exact prefixLift 4670848
  have htrace : WordTrace (prefixWord ++ tailWord_4670848) baseStart_4670848 baseEnd_4670848 := by
    simpa [prefixWord, tailWord_4670848, baseEnd_4670848] using wordTrace_append hprefix tailTrace_4670848
  have hstable : (prefixWord ++ tailWord_4670848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670848).length < 2 ^ (prefixWord ++ tailWord_4670848).sum := by decide
  have hdescent : baseEnd_4670848 < baseStart_4670848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670855 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_4670855 : Nat := 118140960795 + 4670855 * 2 ^ 59
def prefixEnd_4670855 : Nat := 4983230072969 + 3 ^ 40 * 4670855 * 2
def baseEnd_4670855 : Nat := 2398393682456427992031635

theorem tailTrace_4670855 : CollatzResearch.WordTrace tailWord_4670855 prefixEnd_4670855 2398393682456427992031635 := by
  unfold tailWord_4670855
  simp only [CollatzResearch.WordTrace]
  refine ⟨170360077493297528369494019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113573384995531685579662679 170360077493297528369494019)
  ·
    refine ⟨255540116239946292554241029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170360077493297528369494019 255540116239946292554241029)
    ·
      refine ⟨47913771794989929853920193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255540116239946292554241029 47913771794989929853920193)
      ·
        refine ⟨35935328846242447390440145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47913771794989929853920193 35935328846242447390440145)
        ·
          refine ⟨26951496634681835542830109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35935328846242447390440145 26951496634681835542830109)
          ·
            refine ⟨10106811238005688328561291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26951496634681835542830109 10106811238005688328561291)
            ·
              refine ⟨15160216857008532492841937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10106811238005688328561291 15160216857008532492841937)
              ·
                refine ⟨11370162642756399369631453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15160216857008532492841937 11370162642756399369631453)
                ·
                  refine ⟨4263810991033649763611795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11370162642756399369631453 4263810991033649763611795)
                  ·
                    refine ⟨6395716486550474645417693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4263810991033649763611795 6395716486550474645417693)
                    ·
                      refine ⟨2398393682456427992031635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6395716486550474645417693 2398393682456427992031635)
                      ·
                        rfl

theorem cell23_4670855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_4670855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670855 prefixEnd_4670855 := by exact prefixLift 4670855
  have htrace : WordTrace (prefixWord ++ tailWord_4670855) baseStart_4670855 baseEnd_4670855 := by
    simpa [prefixWord, tailWord_4670855, baseEnd_4670855] using wordTrace_append hprefix tailTrace_4670855
  have hstable : (prefixWord ++ tailWord_4670855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670855).length < 2 ^ (prefixWord ++ tailWord_4670855).sum := by decide
  have hdescent : baseEnd_4670855 < baseStart_4670855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670898 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_4670898 : Nat := 118140960795 + 4670898 * 2 ^ 59
def prefixEnd_4670898 : Nat := 4983230072969 + 3 ^ 40 * 4670898 * 2
def baseEnd_4670898 : Nat := 2398415762124571323793937

theorem tailTrace_4670898 : CollatzResearch.WordTrace tailWord_4670898 prefixEnd_4670898 2398415762124571323793937 := by
  unfold tailWord_4670898
  simp only [CollatzResearch.WordTrace]
  refine ⟨42590411458035436678327337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113574430554761164475539565 42590411458035436678327337)
  ·
    refine ⟨31942808593526577508745503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42590411458035436678327337 31942808593526577508745503)
    ·
      refine ⟨47914212890289866263118255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31942808593526577508745503 47914212890289866263118255)
      ·
        refine ⟨71871319335434799394677383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47914212890289866263118255 71871319335434799394677383)
        ·
          refine ⟨107806979003152199092016075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71871319335434799394677383 107806979003152199092016075)
          ·
            refine ⟨161710468504728298638024113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107806979003152199092016075 161710468504728298638024113)
            ·
              refine ⟨121282851378546223978518085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161710468504728298638024113 121282851378546223978518085)
              ·
                refine ⟨22740534633477416995972141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121282851378546223978518085 22740534633477416995972141)
                ·
                  refine ⟨8527700487554031373489553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22740534633477416995972141 8527700487554031373489553)
                  ·
                    refine ⟨6395775365665523530117165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8527700487554031373489553 6395775365665523530117165)
                    ·
                      refine ⟨2398415762124571323793937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6395775365665523530117165 2398415762124571323793937)
                      ·
                        rfl

theorem cell23_4670898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_4670898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670898 prefixEnd_4670898 := by exact prefixLift 4670898
  have htrace : WordTrace (prefixWord ++ tailWord_4670898) baseStart_4670898 baseEnd_4670898 := by
    simpa [prefixWord, tailWord_4670898, baseEnd_4670898] using wordTrace_append hprefix tailTrace_4670898
  have hstable : (prefixWord ++ tailWord_4670898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670898).length < 2 ^ (prefixWord ++ tailWord_4670898).sum := by decide
  have hdescent : baseEnd_4670898 < baseStart_4670898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670905 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 1, 6]
def baseStart_4670905 : Nat := 118140960795 + 4670905 * 2 ^ 59
def prefixEnd_4670905 : Nat := 4983230072969 + 3 ^ 40 * 4670905 * 2
def baseEnd_4670905 : Nat := 799473118829717598802135

theorem tailTrace_4670905 : CollatzResearch.WordTrace tailWord_4670905 prefixEnd_4670905 799473118829717598802135 := by
  unfold tailWord_4670905
  simp only [CollatzResearch.WordTrace]
  refine ⟨170361901143116386908814169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113574600762077591272542779 170361901143116386908814169)
  ·
    refine ⟨127771425857337290181610627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170361901143116386908814169 127771425857337290181610627)
    ·
      refine ⟨191657138786005935272415941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127771425857337290181610627 191657138786005935272415941)
      ·
        refine ⟨35935713522376112863577989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191657138786005935272415941 35935713522376112863577989)
        ·
          refine ⟨6737946285445521161920873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35935713522376112863577989 6737946285445521161920873)
          ·
            refine ⟨5053459714084140871440655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6737946285445521161920873 5053459714084140871440655)
            ·
              refine ⟨7580189571126211307160983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5053459714084140871440655 7580189571126211307160983)
              ·
                refine ⟨11370284356689316960741475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7580189571126211307160983 11370284356689316960741475)
                ·
                  refine ⟨17055426535033975441112213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11370284356689316960741475 17055426535033975441112213)
                  ·
                    refine ⟨799473118829717598802135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17055426535033975441112213 799473118829717598802135)
                    ·
                      rfl

theorem cell23_4670905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 6].length) (baseStart_4670905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670905 prefixEnd_4670905 := by exact prefixLift 4670905
  have htrace : WordTrace (prefixWord ++ tailWord_4670905) baseStart_4670905 baseEnd_4670905 := by
    simpa [prefixWord, tailWord_4670905, baseEnd_4670905] using wordTrace_append hprefix tailTrace_4670905
  have hstable : (prefixWord ++ tailWord_4670905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670905).length < 2 ^ (prefixWord ++ tailWord_4670905).sum := by decide
  have hdescent : baseEnd_4670905 < baseStart_4670905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670945 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_4670945 : Nat := 118140960795 + 4670945 * 2 ^ 59
def prefixEnd_4670945 : Nat := 4983230072969 + 3 ^ 40 * 4670945 * 2
def baseEnd_4670945 : Nat := 2398439895715332639906221

theorem tailTrace_4670945 : CollatzResearch.WordTrace tailWord_4670945 prefixEnd_4670945 2398439895715332639906221 := by
  unfold tailWord_4670945
  simp only [CollatzResearch.WordTrace]
  refine ⟨170363360062971473740270289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113575573375314315826846859 170363360062971473740270289)
  ·
    refine ⟨127772520047228605305202717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170363360062971473740270289 127772520047228605305202717)
    ·
      refine ⟨47914695017710726989451019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127772520047228605305202717 47914695017710726989451019)
      ·
        refine ⟨71872042526566090484176529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47914695017710726989451019 71872042526566090484176529)
        ·
          refine ⟨53904031894924567863132397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71872042526566090484176529 53904031894924567863132397)
          ·
            refine ⟨20214011960596712948674649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53904031894924567863132397 20214011960596712948674649)
            ·
              refine ⟨15160508970447534711505987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20214011960596712948674649 15160508970447534711505987)
              ·
                refine ⟨22740763455671302067258981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15160508970447534711505987 22740763455671302067258981)
                ·
                  refine ⟨4263893147938369137611059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22740763455671302067258981 4263893147938369137611059)
                  ·
                    refine ⟨6395839721907553706416589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4263893147938369137611059 6395839721907553706416589)
                    ·
                      refine ⟨2398439895715332639906221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6395839721907553706416589 2398439895715332639906221)
                      ·
                        rfl

theorem cell23_4670945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_4670945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670945 prefixEnd_4670945 := by exact prefixLift 4670945
  have htrace : WordTrace (prefixWord ++ tailWord_4670945) baseStart_4670945 baseEnd_4670945 := by
    simpa [prefixWord, tailWord_4670945, baseEnd_4670945] using wordTrace_append hprefix tailTrace_4670945
  have hstable : (prefixWord ++ tailWord_4670945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670945).length < 2 ^ (prefixWord ++ tailWord_4670945).sum := by decide
  have hdescent : baseEnd_4670945 < baseStart_4670945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670971 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 5]
def baseStart_4670971 : Nat := 118140960795 + 4670971 * 2 ^ 59
def prefixEnd_4670971 : Nat := 4983230072969 + 3 ^ 40 * 4670971 * 2
def baseEnd_4670971 : Nat := 2398453246212349538181101

theorem tailTrace_4670971 : CollatzResearch.WordTrace tailWord_4670971 prefixEnd_4670971 2398453246212349538181101 := by
  unfold tailWord_4670971
  simp only [CollatzResearch.WordTrace]
  refine ⟨170364308360877280180716767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113576205573918186787144511 170364308360877280180716767)
  ·
    refine ⟨255546462541315920271075151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170364308360877280180716767 255546462541315920271075151)
    ·
      refine ⟨383319693811973880406612727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255546462541315920271075151 383319693811973880406612727)
      ·
        refine ⟨574979540717960820609919091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383319693811973880406612727 574979540717960820609919091)
        ·
          refine ⟨862469311076941230914878637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574979540717960820609919091 862469311076941230914878637)
          ·
            refine ⟨323425991653852961593079489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 862469311076941230914878637 323425991653852961593079489)
            ·
              refine ⟨242569493740389721194809617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323425991653852961593079489 242569493740389721194809617)
              ·
                refine ⟨181927120305292290896107213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242569493740389721194809617 181927120305292290896107213)
                ·
                  refine ⟨68222670114484609086040205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181927120305292290896107213 68222670114484609086040205)
                  ·
                    refine ⟨25583501292931728407265077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68222670114484609086040205 25583501292931728407265077)
                    ·
                      refine ⟨2398453246212349538181101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25583501292931728407265077 2398453246212349538181101)
                      ·
                        rfl

theorem cell23_4670971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_4670971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670971 prefixEnd_4670971 := by exact prefixLift 4670971
  have htrace : WordTrace (prefixWord ++ tailWord_4670971) baseStart_4670971 baseEnd_4670971 := by
    simpa [prefixWord, tailWord_4670971, baseEnd_4670971] using wordTrace_append hprefix tailTrace_4670971
  have hstable : (prefixWord ++ tailWord_4670971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670971).length < 2 ^ (prefixWord ++ tailWord_4670971).sum := by decide
  have hdescent : baseEnd_4670971 < baseStart_4670971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670972 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 1, 3, 2]
def baseStart_4670972 : Nat := 118140960795 + 4670972 * 2 ^ 59
def prefixEnd_4670972 : Nat := 4983230072969 + 3 ^ 40 * 4670972 * 2
def baseEnd_4670972 : Nat := 2398453759693004034268597

theorem tailTrace_4670972 : CollatzResearch.WordTrace tailWord_4670972 prefixEnd_4670972 2398453759693004034268597 := by
  unfold tailWord_4670972
  simp only [CollatzResearch.WordTrace]
  refine ⟨85182172416936828675751585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113576229889249104901002113 85182172416936828675751585)
  ·
    refine ⟨63886629312702621506813689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85182172416936828675751585 63886629312702621506813689)
    ·
      refine ⟨47914971984526966130110267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63886629312702621506813689 47914971984526966130110267)
      ·
        refine ⟨71872457976790449195165401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47914971984526966130110267 71872457976790449195165401)
        ·
          refine ⟨53904343482592836896374051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71872457976790449195165401 53904343482592836896374051)
          ·
            refine ⟨80856515223889255344561077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53904343482592836896374051 80856515223889255344561077)
            ·
              refine ⟨7580298302239617688552601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80856515223889255344561077 7580298302239617688552601)
              ·
                refine ⟨5685223726679713266414451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7580298302239617688552601 5685223726679713266414451)
                ·
                  refine ⟨8527835590019569899621677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5685223726679713266414451 8527835590019569899621677)
                  ·
                    refine ⟨3197938346257338712358129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8527835590019569899621677 3197938346257338712358129)
                    ·
                      refine ⟨2398453759693004034268597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197938346257338712358129 2398453759693004034268597)
                      ·
                        rfl

theorem cell23_4670972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_4670972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670972 prefixEnd_4670972 := by exact prefixLift 4670972
  have htrace : WordTrace (prefixWord ++ tailWord_4670972) baseStart_4670972 baseEnd_4670972 := by
    simpa [prefixWord, tailWord_4670972, baseEnd_4670972] using wordTrace_append hprefix tailTrace_4670972
  have hstable : (prefixWord ++ tailWord_4670972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670972).length < 2 ^ (prefixWord ++ tailWord_4670972).sum := by decide
  have hdescent : baseEnd_4670972 < baseStart_4670972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670985 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 1, 4, 2]
def baseStart_4670985 : Nat := 118140960795 + 4670985 * 2 ^ 59
def prefixEnd_4670985 : Nat := 4983230072969 + 3 ^ 40 * 4670985 * 2
def baseEnd_4670985 : Nat := 2398460434941512483406037

theorem tailTrace_4670985 : CollatzResearch.WordTrace tailWord_4670985 prefixEnd_4670985 2398460434941512483406037 := by
  unfold tailWord_4670985
  simp only [CollatzResearch.WordTrace]
  refine ⟨170364818982826560571726409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113576545988551040381150939 170364818982826560571726409)
  ·
    refine ⟨127773614237119920428794807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170364818982826560571726409 127773614237119920428794807)
    ·
      refine ⟨191660421355679880643192211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127773614237119920428794807 191660421355679880643192211)
      ·
        refine ⟨287490632033519820964788317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191660421355679880643192211 287490632033519820964788317)
        ·
          refine ⟨107808987012569932861795619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287490632033519820964788317 107808987012569932861795619)
          ·
            refine ⟨161713480518854899292693429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107808987012569932861795619 161713480518854899292693429)
            ·
              refine ⟨15160638798642646808690009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 161713480518854899292693429 15160638798642646808690009)
              ·
                refine ⟨11370479098981985106517507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15160638798642646808690009 11370479098981985106517507)
                ·
                  refine ⟨17055718648472977659776261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11370479098981985106517507 17055718648472977659776261)
                  ·
                    refine ⟨3197947246588683311208049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17055718648472977659776261 3197947246588683311208049)
                    ·
                      refine ⟨2398460434941512483406037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197947246588683311208049 2398460434941512483406037)
                      ·
                        rfl

theorem cell23_4670985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 4, 2].length) (baseStart_4670985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670985 prefixEnd_4670985 := by exact prefixLift 4670985
  have htrace : WordTrace (prefixWord ++ tailWord_4670985) baseStart_4670985 baseEnd_4670985 := by
    simpa [prefixWord, tailWord_4670985, baseEnd_4670985] using wordTrace_append hprefix tailTrace_4670985
  have hstable : (prefixWord ++ tailWord_4670985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670985).length < 2 ^ (prefixWord ++ tailWord_4670985).sum := by decide
  have hdescent : baseEnd_4670985 < baseStart_4670985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4670996 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_4670996 : Nat := 118140960795 + 4670996 * 2 ^ 59
def prefixEnd_4670996 : Nat := 4983230072969 + 3 ^ 40 * 4670996 * 2
def baseEnd_4670996 : Nat := 2398466083228711940368487

theorem tailTrace_4670996 : CollatzResearch.WordTrace tailWord_4670996 prefixEnd_4670996 2398466083228711940368487 := by
  unfold tailWord_4670996
  simp only [CollatzResearch.WordTrace]
  refine ⟨85182610092893354725188421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113576813457191139633584561 85182610092893354725188421)
  ·
    refine ⟨15971739392417504010972829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85182610092893354725188421 15971739392417504010972829)
    ·
      refine ⟨5989402272156564004114811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15971739392417504010972829 5989402272156564004114811)
      ·
        refine ⟨8984103408234846006172217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5989402272156564004114811 8984103408234846006172217)
        ·
          refine ⟨6738077556176134504629163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8984103408234846006172217 6738077556176134504629163)
          ·
            refine ⟨10107116334264201756943745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6738077556176134504629163 10107116334264201756943745)
            ·
              refine ⟨7580337250698151317707809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10107116334264201756943745 7580337250698151317707809)
              ·
                refine ⟨5685252938023613488280857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7580337250698151317707809 5685252938023613488280857)
                ·
                  refine ⟨4263939703517710116210643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5685252938023613488280857 4263939703517710116210643)
                  ·
                    refine ⟨6395909555276565174315965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4263939703517710116210643 6395909555276565174315965)
                    ·
                      refine ⟨2398466083228711940368487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6395909555276565174315965 2398466083228711940368487)
                      ·
                        rfl

theorem cell23_4670996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_4670996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4670996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4670996 prefixEnd_4670996 := by exact prefixLift 4670996
  have htrace : WordTrace (prefixWord ++ tailWord_4670996) baseStart_4670996 baseEnd_4670996 := by
    simpa [prefixWord, tailWord_4670996, baseEnd_4670996] using wordTrace_append hprefix tailTrace_4670996
  have hstable : (prefixWord ++ tailWord_4670996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4670996).length < 2 ^ (prefixWord ++ tailWord_4670996).sum := by decide
  have hdescent : baseEnd_4670996 < baseStart_4670996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4670996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671053 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_4671053 : Nat := 118140960795 + 4671053 * 2 ^ 59
def prefixEnd_4671053 : Nat := 4983230072969 + 3 ^ 40 * 4671053 * 2
def baseEnd_4671053 : Nat := 2398495351626018217355725

theorem tailTrace_4671053 : CollatzResearch.WordTrace tailWord_4671053 prefixEnd_4671053 2398495351626018217355725 := by
  unfold tailWord_4671053
  simp only [CollatzResearch.WordTrace]
  refine ⟨170367299146580208185201813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113578199431053472123467875 170367299146580208185201813)
  ·
    refine ⟨7985967147495947258681335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 170367299146580208185201813 7985967147495947258681335)
    ·
      refine ⟨11978950721243920888022003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7985967147495947258681335 11978950721243920888022003)
      ·
        refine ⟨17968426081865881332033005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11978950721243920888022003 17968426081865881332033005)
        ·
          refine ⟨6738159780699705499512377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17968426081865881332033005 6738159780699705499512377)
          ·
            refine ⟨5053619835524779124634283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6738159780699705499512377 5053619835524779124634283)
            ·
              refine ⟨7580429753287168686951425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5053619835524779124634283 7580429753287168686951425)
              ·
                refine ⟨5685322314965376515213569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7580429753287168686951425 5685322314965376515213569)
                ·
                  refine ⟨4263991736224032386410177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5685322314965376515213569 4263991736224032386410177)
                  ·
                    refine ⟨3197993802168024289807633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4263991736224032386410177 3197993802168024289807633)
                    ·
                      refine ⟨2398495351626018217355725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3197993802168024289807633 2398495351626018217355725)
                      ·
                        rfl

theorem cell23_4671053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_4671053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671053 prefixEnd_4671053 := by exact prefixLift 4671053
  have htrace : WordTrace (prefixWord ++ tailWord_4671053) baseStart_4671053 baseEnd_4671053 := by
    simpa [prefixWord, tailWord_4671053, baseEnd_4671053] using wordTrace_append hprefix tailTrace_4671053
  have hstable : (prefixWord ++ tailWord_4671053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671053).length < 2 ^ (prefixWord ++ tailWord_4671053).sum := by decide
  have hdescent : baseEnd_4671053 < baseStart_4671053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671095 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 3]
def baseStart_4671095 : Nat := 118140960795 + 4671095 * 2 ^ 59
def prefixEnd_4671095 : Nat := 4983230072969 + 3 ^ 40 * 4671095 * 2
def baseEnd_4671095 : Nat := 2398516917813507053030531

theorem tailTrace_4671095 : CollatzResearch.WordTrace tailWord_4671095 prefixEnd_4671095 2398516917813507053030531 := by
  unfold tailWord_4671095
  simp only [CollatzResearch.WordTrace]
  refine ⟨170368831012428049358230739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113579220674952032905487159 170368831012428049358230739)
  ·
    refine ⟨255553246518642074037346109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170368831012428049358230739 255553246518642074037346109)
    ·
      refine ⟨95832467444490777764004791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255553246518642074037346109 95832467444490777764004791)
      ·
        refine ⟨143748701166736166646007187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95832467444490777764004791 143748701166736166646007187)
        ·
          refine ⟨215623051750104249969010781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143748701166736166646007187 215623051750104249969010781)
          ·
            refine ⟨80858644406289093738379043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215623051750104249969010781 80858644406289093738379043)
            ·
              refine ⟨121287966609433640607568565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80858644406289093738379043 121287966609433640607568565)
              ·
                refine ⟨11370746869634403806959553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121287966609433640607568565 11370746869634403806959553)
                ·
                  refine ⟨8528060152225802855219665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11370746869634403806959553 8528060152225802855219665)
                  ·
                    refine ⟨6396045114169352141414749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8528060152225802855219665 6396045114169352141414749)
                    ·
                      refine ⟨2398516917813507053030531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6396045114169352141414749 2398516917813507053030531)
                      ·
                        rfl

theorem cell23_4671095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_4671095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671095 prefixEnd_4671095 := by exact prefixLift 4671095
  have htrace : WordTrace (prefixWord ++ tailWord_4671095) baseStart_4671095 baseEnd_4671095 := by
    simpa [prefixWord, tailWord_4671095, baseEnd_4671095] using wordTrace_append hprefix tailTrace_4671095
  have hstable : (prefixWord ++ tailWord_4671095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671095).length < 2 ^ (prefixWord ++ tailWord_4671095).sum := by decide
  have hdescent : baseEnd_4671095 < baseStart_4671095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671132 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 6]
def baseStart_4671132 : Nat := 118140960795 + 4671132 * 2 ^ 59
def prefixEnd_4671132 : Nat := 4983230072969 + 3 ^ 40 * 4671132 * 2
def baseEnd_4671132 : Nat := 266503990733080378696429

theorem tailTrace_4671132 : CollatzResearch.WordTrace tailWord_4671132 prefixEnd_4671132 266503990733080378696429 := by
  unfold tailWord_4671132
  simp only [CollatzResearch.WordTrace]
  refine ⟨85185090256647002338663825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113580120342196003118218433 85185090256647002338663825)
  ·
    refine ⟨63888817692485251753997869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85185090256647002338663825 63888817692485251753997869)
    ·
      refine ⟨23958306634681969407749201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63888817692485251753997869 23958306634681969407749201)
      ·
        refine ⟨17968729976011477055811901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23958306634681969407749201 17968729976011477055811901)
        ·
          refine ⟨6738273741004303895929463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17968729976011477055811901 6738273741004303895929463)
          ·
            refine ⟨10107410611506455843894195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6738273741004303895929463 10107410611506455843894195)
            ·
              refine ⟨15161115917259683765841293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10107410611506455843894195 15161115917259683765841293)
              ·
                refine ⟨5685418468972381412190485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15161115917259683765841293 5685418468972381412190485)
                ·
                  refine ⟨266503990733080378696429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5685418468972381412190485 266503990733080378696429)
                  ·
                    rfl

theorem cell23_4671132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_4671132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671132 prefixEnd_4671132 := by exact prefixLift 4671132
  have htrace : WordTrace (prefixWord ++ tailWord_4671132) baseStart_4671132 baseEnd_4671132 := by
    simpa [prefixWord, tailWord_4671132, baseEnd_4671132] using wordTrace_append hprefix tailTrace_4671132
  have hstable : (prefixWord ++ tailWord_4671132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671132).length < 2 ^ (prefixWord ++ tailWord_4671132).sum := by decide
  have hdescent : baseEnd_4671132 < baseStart_4671132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671152 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 2, 3, 2]
def baseStart_4671152 : Nat := 118140960795 + 4671152 * 2 ^ 59
def prefixEnd_4671152 : Nat := 4983230072969 + 3 ^ 40 * 4671152 * 2
def baseEnd_4671152 : Nat := 2398546186210813330017769

theorem tailTrace_4671152 : CollatzResearch.WordTrace tailWord_4671152 prefixEnd_4671152 2398546186210813330017769 := by
  unfold tailWord_4671152
  simp only [CollatzResearch.WordTrace]
  refine ⟨85185454986610774046527855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113580606648814365395370473 85185454986610774046527855)
  ·
    refine ⟨127778182479916161069791783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85185454986610774046527855 127778182479916161069791783)
    ·
      refine ⟨191667273719874241604687675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127778182479916161069791783 191667273719874241604687675)
      ·
        refine ⟨287500910579811362407031513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191667273719874241604687675 287500910579811362407031513)
        ·
          refine ⟨215625682934858521805273635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287500910579811362407031513 215625682934858521805273635)
          ·
            refine ⟨323438524402287782707910453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215625682934858521805273635 323438524402287782707910453)
            ·
              refine ⟨30322361662714479628866605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 323438524402287782707910453 30322361662714479628866605)
              ·
                refine ⟨11370885623517929860824977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30322361662714479628866605 11370885623517929860824977)
                ·
                  refine ⟨8528164217638447395618733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11370885623517929860824977 8528164217638447395618733)
                  ·
                    refine ⟨3198061581614417773357025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8528164217638447395618733 3198061581614417773357025)
                    ·
                      refine ⟨2398546186210813330017769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198061581614417773357025 2398546186210813330017769)
                      ·
                        rfl

theorem cell23_4671152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 3, 2].length) (baseStart_4671152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671152 prefixEnd_4671152 := by exact prefixLift 4671152
  have htrace : WordTrace (prefixWord ++ tailWord_4671152) baseStart_4671152 baseEnd_4671152 := by
    simpa [prefixWord, tailWord_4671152, baseEnd_4671152] using wordTrace_append hprefix tailTrace_4671152
  have hstable : (prefixWord ++ tailWord_4671152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671152).length < 2 ^ (prefixWord ++ tailWord_4671152).sum := by decide
  have hdescent : baseEnd_4671152 < baseStart_4671152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671170 : List Nat := [3, 5, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_4671170 : Nat := 118140960795 + 4671170 * 2 ^ 59
def prefixEnd_4671170 : Nat := 4983230072969 + 3 ^ 40 * 4671170 * 2
def baseEnd_4671170 : Nat := 799518476287531419864229

theorem tailTrace_4671170 : CollatzResearch.WordTrace tailWord_4671170 prefixEnd_4671170 799518476287531419864229 := by
  unfold tailWord_4671170
  simp only [CollatzResearch.WordTrace]
  refine ⟨42592891621789084291802741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113581044324770891444807309 42592891621789084291802741)
  ·
    refine ⟨3993083589542726652356507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42592891621789084291802741 3993083589542726652356507)
    ·
      refine ⟨5989625384314089978534761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3993083589542726652356507 5989625384314089978534761)
      ·
        refine ⟨4492219038235567483901071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5989625384314089978534761 4492219038235567483901071)
        ·
          refine ⟨6738328557353351225851607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4492219038235567483901071 6738328557353351225851607)
          ·
            refine ⟨10107492836030026838777411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6738328557353351225851607 10107492836030026838777411)
            ·
              refine ⟨15161239254045040258166117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10107492836030026838777411 15161239254045040258166117)
              ·
                refine ⟨2842732360133445048406147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15161239254045040258166117 2842732360133445048406147)
                ·
                  refine ⟨4264098540200167572609221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842732360133445048406147 4264098540200167572609221)
                  ·
                    refine ⟨799518476287531419864229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4264098540200167572609221 799518476287531419864229)
                    ·
                      rfl

theorem cell23_4671170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_4671170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671170 prefixEnd_4671170 := by exact prefixLift 4671170
  have htrace : WordTrace (prefixWord ++ tailWord_4671170) baseStart_4671170 baseEnd_4671170 := by
    simpa [prefixWord, tailWord_4671170, baseEnd_4671170] using wordTrace_append hprefix tailTrace_4671170
  have hstable : (prefixWord ++ tailWord_4671170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671170).length < 2 ^ (prefixWord ++ tailWord_4671170).sum := by decide
  have hdescent : baseEnd_4671170 < baseStart_4671170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671192 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 2, 4]
def baseStart_4671192 : Nat := 118140960795 + 4671192 * 2 ^ 59
def prefixEnd_4671192 : Nat := 4983230072969 + 3 ^ 40 * 4671192 * 2
def baseEnd_4671192 : Nat := 799522241812331057839195

theorem tailTrace_4671192 : CollatzResearch.WordTrace tailWord_4671192 prefixEnd_4671192 799522241812331057839195 := by
  unfold tailWord_4671192
  simp only [CollatzResearch.WordTrace]
  refine ⟨85186184446538317462255915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113581579262051089949674553 85186184446538317462255915)
  ·
    refine ⟨127779276669807476193383873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85186184446538317462255915 127779276669807476193383873)
    ·
      refine ⟨95834457502355607145037905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127779276669807476193383873 95834457502355607145037905)
      ·
        refine ⟨71875843126766705358778429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95834457502355607145037905 71875843126766705358778429)
        ·
          refine ⟨26953441172537514509541911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71875843126766705358778429 26953441172537514509541911)
          ·
            refine ⟨40430161758806271764312867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26953441172537514509541911 40430161758806271764312867)
            ·
              refine ⟨60645242638209407646469301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40430161758806271764312867 60645242638209407646469301)
              ·
                refine ⟨5685491497332131966856497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60645242638209407646469301 5685491497332131966856497)
                ·
                  refine ⟨4264118622999098975142373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5685491497332131966856497 4264118622999098975142373)
                  ·
                    refine ⟨799522241812331057839195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4264118622999098975142373 799522241812331057839195)
                    ·
                      rfl

theorem cell23_4671192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_4671192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671192 prefixEnd_4671192 := by exact prefixLift 4671192
  have htrace : WordTrace (prefixWord ++ tailWord_4671192) baseStart_4671192 baseEnd_4671192 := by
    simpa [prefixWord, tailWord_4671192, baseEnd_4671192] using wordTrace_append hprefix tailTrace_4671192
  have hstable : (prefixWord ++ tailWord_4671192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671192).length < 2 ^ (prefixWord ++ tailWord_4671192).sum := by decide
  have hdescent : baseEnd_4671192 < baseStart_4671192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671199 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 3, 2, 2]
def baseStart_4671199 : Nat := 118140960795 + 4671199 * 2 ^ 59
def prefixEnd_4671199 : Nat := 4983230072969 + 3 ^ 40 * 4671199 * 2
def baseEnd_4671199 : Nat := 2398570319801574646130053

theorem tailTrace_4671199 : CollatzResearch.WordTrace tailWord_4671199 prefixEnd_4671199 2398570319801574646130053 := by
  unfold tailWord_4671199
  simp only [CollatzResearch.WordTrace]
  refine ⟨170372624204051275120016651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113581749469367516746677767 170372624204051275120016651)
  ·
    refine ⟨255558936306076912680024977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170372624204051275120016651 255558936306076912680024977)
    ·
      refine ⟨191669202229557684510018733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255558936306076912680024977 191669202229557684510018733)
      ·
        refine ⟨71875950836084131691257025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191669202229557684510018733 71875950836084131691257025)
        ·
          refine ⟨53906963127063098768442769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71875950836084131691257025 53906963127063098768442769)
          ·
            refine ⟨40430222345297324076332077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53906963127063098768442769 40430222345297324076332077)
            ·
              refine ⟨15161333379486496528624529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40430222345297324076332077 15161333379486496528624529)
              ·
                refine ⟨11371000034614872396468397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15161333379486496528624529 11371000034614872396468397)
                ·
                  refine ⟨4264125012980577148675649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11371000034614872396468397 4264125012980577148675649)
                  ·
                    refine ⟨3198093759735432861506737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4264125012980577148675649 3198093759735432861506737)
                    ·
                      refine ⟨2398570319801574646130053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198093759735432861506737 2398570319801574646130053)
                      ·
                        rfl

theorem cell23_4671199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_4671199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671199 prefixEnd_4671199 := by exact prefixLift 4671199
  have htrace : WordTrace (prefixWord ++ tailWord_4671199) baseStart_4671199 baseEnd_4671199 := by
    simpa [prefixWord, tailWord_4671199, baseEnd_4671199] using wordTrace_append hprefix tailTrace_4671199
  have hstable : (prefixWord ++ tailWord_4671199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671199).length < 2 ^ (prefixWord ++ tailWord_4671199).sum := by decide
  have hdescent : baseEnd_4671199 < baseStart_4671199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671203 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 2, 3, 2]
def baseStart_4671203 : Nat := 118140960795 + 4671203 * 2 ^ 59
def prefixEnd_4671203 : Nat := 4983230072969 + 3 ^ 40 * 4671203 * 2
def baseEnd_4671203 : Nat := 2398572373724192630480035

theorem tailTrace_4671203 : CollatzResearch.WordTrace tailWord_4671203 prefixEnd_4671203 2398572373724192630480035 := by
  unfold tailWord_4671203
  simp only [CollatzResearch.WordTrace]
  refine ⟨170372770096036783803162263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113581846730691189202108175 170372770096036783803162263)
  ·
    refine ⟨255559155144055175704743395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170372770096036783803162263 255559155144055175704743395)
    ·
      refine ⟨383338732716082763557115093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255559155144055175704743395 383338732716082763557115093)
      ·
        refine ⟨8984501548033189770869885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 383338732716082763557115093 8984501548033189770869885)
        ·
          refine ⟨3369188080512446164076207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8984501548033189770869885 3369188080512446164076207)
          ·
            refine ⟨5053782120768669246114311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3369188080512446164076207 5053782120768669246114311)
            ·
              refine ⟨7580673181153003869171467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5053782120768669246114311 7580673181153003869171467)
              ·
                refine ⟨11371009771729505803757201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7580673181153003869171467 11371009771729505803757201)
                ·
                  refine ⟨8528257328797129352817901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11371009771729505803757201 8528257328797129352817901)
                  ·
                    refine ⟨3198096498298923507306713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8528257328797129352817901 3198096498298923507306713)
                    ·
                      refine ⟨2398572373724192630480035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198096498298923507306713 2398572373724192630480035)
                      ·
                        rfl

theorem cell23_4671203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_4671203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671203 prefixEnd_4671203 := by exact prefixLift 4671203
  have htrace : WordTrace (prefixWord ++ tailWord_4671203) baseStart_4671203 baseEnd_4671203 := by
    simpa [prefixWord, tailWord_4671203, baseEnd_4671203] using wordTrace_append hprefix tailTrace_4671203
  have hstable : (prefixWord ++ tailWord_4671203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671203).length < 2 ^ (prefixWord ++ tailWord_4671203).sum := by decide
  have hdescent : baseEnd_4671203 < baseStart_4671203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671219 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 1, 2, 3]
def baseStart_4671219 : Nat := 118140960795 + 4671219 * 2 ^ 59
def prefixEnd_4671219 : Nat := 4983230072969 + 3 ^ 40 * 4671219 * 2
def baseEnd_4671219 : Nat := 2398580589414664567879961

theorem tailTrace_4671219 : CollatzResearch.WordTrace tailWord_4671219 prefixEnd_4671219 2398580589414664567879961 := by
  unfold tailWord_4671219
  simp only [CollatzResearch.WordTrace]
  refine ⟨170373353663978818535744711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113582235775985879023829807 170373353663978818535744711)
  ·
    refine ⟨255560030495968227803617067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170373353663978818535744711 255560030495968227803617067)
    ·
      refine ⟨383340045743952341705425601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255560030495968227803617067 383340045743952341705425601)
      ·
        refine ⟨287505034307964256279069201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383340045743952341705425601 287505034307964256279069201)
        ·
          refine ⟨215628775730973192209301901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287505034307964256279069201 215628775730973192209301901)
          ·
            refine ⟨80860790899114947078488213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215628775730973192209301901 80860790899114947078488213)
            ·
              refine ⟨3790349573396013144304135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80860790899114947078488213 3790349573396013144304135)
              ·
                refine ⟨5685524360094019716456203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3790349573396013144304135 5685524360094019716456203)
                ·
                  refine ⟨8528286540141029574684305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5685524360094019716456203 8528286540141029574684305)
                  ·
                    refine ⟨6396214905105772181013229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8528286540141029574684305 6396214905105772181013229)
                    ·
                      refine ⟨2398580589414664567879961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6396214905105772181013229 2398580589414664567879961)
                      ·
                        rfl

theorem cell23_4671219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 1, 2, 3].length) (baseStart_4671219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671219 prefixEnd_4671219 := by exact prefixLift 4671219
  have htrace : WordTrace (prefixWord ++ tailWord_4671219) baseStart_4671219 baseEnd_4671219 := by
    simpa [prefixWord, tailWord_4671219, baseEnd_4671219] using wordTrace_append hprefix tailTrace_4671219
  have hstable : (prefixWord ++ tailWord_4671219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671219).length < 2 ^ (prefixWord ++ tailWord_4671219).sum := by decide
  have hdescent : baseEnd_4671219 < baseStart_4671219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671232 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 4, 1, 3]
def baseStart_4671232 : Nat := 118140960795 + 4671232 * 2 ^ 59
def prefixEnd_4671232 : Nat := 4983230072969 + 3 ^ 40 * 4671232 * 2
def baseEnd_4671232 : Nat := 2398587264663173017017401

theorem tailTrace_4671232 : CollatzResearch.WordTrace tailWord_4671232 prefixEnd_4671232 2398587264663173017017401 := by
  unfold tailWord_4671232
  simp only [CollatzResearch.WordTrace]
  refine ⟨85186913906465860877983975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113582551875287814503978633 85186913906465860877983975)
  ·
    refine ⟨127780370859698791316975963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85186913906465860877983975 127780370859698791316975963)
    ·
      refine ⟨191670556289548186975463945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127780370859698791316975963 191670556289548186975463945)
      ·
        refine ⟨143752917217161140231597959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191670556289548186975463945 143752917217161140231597959)
        ·
          refine ⟨215629375825741710347396939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143752917217161140231597959 215629375825741710347396939)
          ·
            refine ⟨323444063738612565521095409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215629375825741710347396939 323444063738612565521095409)
            ·
              refine ⟨242583047803959424140821557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323444063738612565521095409 242583047803959424140821557)
              ·
                refine ⟨22742160731621196013202021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 242583047803959424140821557 22742160731621196013202021)
                ·
                  refine ⟨4264155137178974252475379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22742160731621196013202021 4264155137178974252475379)
                  ·
                    refine ⟨6396232705768461378713069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4264155137178974252475379 6396232705768461378713069)
                    ·
                      refine ⟨2398587264663173017017401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6396232705768461378713069 2398587264663173017017401)
                      ·
                        rfl

theorem cell23_4671232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_4671232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671232 prefixEnd_4671232 := by exact prefixLift 4671232
  have htrace : WordTrace (prefixWord ++ tailWord_4671232) baseStart_4671232 baseEnd_4671232 := by
    simpa [prefixWord, tailWord_4671232, baseEnd_4671232] using wordTrace_append hprefix tailTrace_4671232
  have hstable : (prefixWord ++ tailWord_4671232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671232).length < 2 ^ (prefixWord ++ tailWord_4671232).sum := by decide
  have hdescent : baseEnd_4671232 < baseStart_4671232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671306 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2]
def baseStart_4671306 : Nat := 118140960795 + 4671306 * 2 ^ 59
def prefixEnd_4671306 : Nat := 4983230072969 + 3 ^ 40 * 4671306 * 2
def baseEnd_4671306 : Nat := 2398625262231605727492061

theorem tailTrace_4671306 : CollatzResearch.WordTrace tailWord_4671306 prefixEnd_4671306 2398625262231605727492061 := by
  unfold tailWord_4671306
  simp only [CollatzResearch.WordTrace]
  refine ⟨42594131703665908098540443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113584351209775754929441181 42594131703665908098540443)
  ·
    refine ⟨63891197555498862147810665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42594131703665908098540443 63891197555498862147810665)
    ·
      refine ⟨47918398166624146610857999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63891197555498862147810665 47918398166624146610857999)
      ·
        refine ⟨71877597249936219916286999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47918398166624146610857999 71877597249936219916286999)
        ·
          refine ⟨107816395874904329874430499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71877597249936219916286999 107816395874904329874430499)
          ·
            refine ⟨161724593812356494811645749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107816395874904329874430499 161724593812356494811645749)
            ·
              refine ⟨15161680669908421388591789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 161724593812356494811645749 15161680669908421388591789)
              ·
                refine ⟨5685630251215658020721921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15161680669908421388591789 5685630251215658020721921)
                ·
                  refine ⟨4264222688411743515541441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5685630251215658020721921 4264222688411743515541441)
                  ·
                    refine ⟨3198167016308807636656081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4264222688411743515541441 3198167016308807636656081)
                    ·
                      refine ⟨2398625262231605727492061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198167016308807636656081 2398625262231605727492061)
                      ·
                        rfl

theorem cell23_4671306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_4671306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671306 prefixEnd_4671306 := by exact prefixLift 4671306
  have htrace : WordTrace (prefixWord ++ tailWord_4671306) baseStart_4671306 baseEnd_4671306 := by
    simpa [prefixWord, tailWord_4671306, baseEnd_4671306] using wordTrace_append hprefix tailTrace_4671306
  have hstable : (prefixWord ++ tailWord_4671306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671306).length < 2 ^ (prefixWord ++ tailWord_4671306).sum := by decide
  have hdescent : baseEnd_4671306 < baseStart_4671306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671309 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_4671309 : Nat := 118140960795 + 4671309 * 2 ^ 59
def prefixEnd_4671309 : Nat := 4983230072969 + 3 ^ 40 * 4671309 * 2
def baseEnd_4671309 : Nat := 2398626802673569215754547

theorem tailTrace_4671309 : CollatzResearch.WordTrace tailWord_4671309 prefixEnd_4671309 2398626802673569215754547 := by
  unfold tailWord_4671309
  simp only [CollatzResearch.WordTrace]
  refine ⟨170376636233652763906520981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113584424155768509271013987 170376636233652763906520981)
  ·
    refine ⟨7986404823452473308118171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 170376636233652763906520981 7986404823452473308118171)
    ·
      refine ⟨11979607235178709962177257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7986404823452473308118171 11979607235178709962177257)
      ·
        refine ⟨8984705426384032471632943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11979607235178709962177257 8984705426384032471632943)
        ·
          refine ⟨13477058139576048707449415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8984705426384032471632943 13477058139576048707449415)
          ·
            refine ⟨20215587209364073061174123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13477058139576048707449415 20215587209364073061174123)
            ·
              refine ⟨30323380814046109591761185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20215587209364073061174123 30323380814046109591761185)
              ·
                refine ⟨22742535610534582193820889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30323380814046109591761185 22742535610534582193820889)
                ·
                  refine ⟨17056901707900936645365667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22742535610534582193820889 17056901707900936645365667)
                  ·
                    refine ⟨25585352561851404968048501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17056901707900936645365667 25585352561851404968048501)
                    ·
                      refine ⟨2398626802673569215754547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25585352561851404968048501 2398626802673569215754547)
                      ·
                        rfl

theorem cell23_4671309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_4671309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671309 prefixEnd_4671309 := by exact prefixLift 4671309
  have htrace : WordTrace (prefixWord ++ tailWord_4671309) baseStart_4671309 baseEnd_4671309 := by
    simpa [prefixWord, tailWord_4671309, baseEnd_4671309] using wordTrace_append hprefix tailTrace_4671309
  have hstable : (prefixWord ++ tailWord_4671309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671309).length < 2 ^ (prefixWord ++ tailWord_4671309).sum := by decide
  have hdescent : baseEnd_4671309 < baseStart_4671309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671349 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_4671349 : Nat := 118140960795 + 4671349 * 2 ^ 59
def prefixEnd_4671349 : Nat := 4983230072969 + 3 ^ 40 * 4671349 * 2
def baseEnd_4671349 : Nat := 2398647341899749059254363

theorem tailTrace_4671349 : CollatzResearch.WordTrace tailWord_4671349 prefixEnd_4671349 2398647341899749059254363 := by
  unfold tailWord_4671349
  simp only [CollatzResearch.WordTrace]
  refine ⟨170378095153507850737977101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113585396769005233825318067 170378095153507850737977101)
  ·
    refine ⟨63891785682565444026741413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170378095153507850737977101 63891785682565444026741413)
    ·
      refine ⟨11979709815481020755014015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63891785682565444026741413 11979709815481020755014015)
      ·
        refine ⟨17969564723221531132521023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11979709815481020755014015 17969564723221531132521023)
        ·
          refine ⟨26954347084832296698781535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17969564723221531132521023 26954347084832296698781535)
          ·
            refine ⟨40431520627248445048172303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26954347084832296698781535 40431520627248445048172303)
            ·
              refine ⟨60647280940872667572258455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40431520627248445048172303 60647280940872667572258455)
              ·
                refine ⟨90970921411309001358387683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60647280940872667572258455 90970921411309001358387683)
                ·
                  refine ⟨136456382116963502037581525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90970921411309001358387683 136456382116963502037581525)
                  ·
                    refine ⟨3198196455866332079005817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 136456382116963502037581525 3198196455866332079005817)
                    ·
                      refine ⟨2398647341899749059254363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198196455866332079005817 2398647341899749059254363)
                      ·
                        rfl

theorem cell23_4671349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_4671349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671349 prefixEnd_4671349 := by exact prefixLift 4671349
  have htrace : WordTrace (prefixWord ++ tailWord_4671349) baseStart_4671349 baseEnd_4671349 := by
    simpa [prefixWord, tailWord_4671349, baseEnd_4671349] using wordTrace_append hprefix tailTrace_4671349
  have hstable : (prefixWord ++ tailWord_4671349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671349).length < 2 ^ (prefixWord ++ tailWord_4671349).sum := by decide
  have hdescent : baseEnd_4671349 < baseStart_4671349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671355 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 2, 8]
def baseStart_4671355 : Nat := 118140960795 + 4671355 * 2 ^ 59
def prefixEnd_4671355 : Nat := 4983230072969 + 3 ^ 40 * 4671355 * 2
def baseEnd_4671355 : Nat := 799550140927892011926445

theorem tailTrace_4671355 : CollatzResearch.WordTrace tailWord_4671355 prefixEnd_4671355 799550140927892011926445 := by
  unfold tailWord_4671355
  simp only [CollatzResearch.WordTrace]
  refine ⟨170378313991486113762695519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113585542660990742508463679 170378313991486113762695519)
  ·
    refine ⟨255567470987229170644043279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170378313991486113762695519 255567470987229170644043279)
    ·
      refine ⟨383351206480843755966064919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255567470987229170644043279 383351206480843755966064919)
      ·
        refine ⟨575026809721265633949097379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383351206480843755966064919 575026809721265633949097379)
        ·
          refine ⟨862540214581898450923646069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575026809721265633949097379 862540214581898450923646069)
          ·
            refine ⟨80863145117052979774091819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 862540214581898450923646069 80863145117052979774091819)
            ·
              refine ⟨121294717675579469661137729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80863145117052979774091819 121294717675579469661137729)
              ·
                refine ⟨90971038256684602245853297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121294717675579469661137729 90971038256684602245853297)
                ·
                  refine ⟨68228278692513451684389973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90971038256684602245853297 68228278692513451684389973)
                  ·
                    refine ⟨799550140927892011926445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68228278692513451684389973 799550140927892011926445)
                    ·
                      rfl

theorem cell23_4671355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 8].length) (baseStart_4671355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671355 prefixEnd_4671355 := by exact prefixLift 4671355
  have htrace : WordTrace (prefixWord ++ tailWord_4671355) baseStart_4671355 baseEnd_4671355 := by
    simpa [prefixWord, tailWord_4671355, baseEnd_4671355] using wordTrace_append hprefix tailTrace_4671355
  have hstable : (prefixWord ++ tailWord_4671355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671355).length < 2 ^ (prefixWord ++ tailWord_4671355).sum := by decide
  have hdescent : baseEnd_4671355 < baseStart_4671355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671429 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 5, 1, 3]
def baseStart_4671429 : Nat := 118140960795 + 4671429 * 2 ^ 59
def prefixEnd_4671429 : Nat := 4983230072969 + 3 ^ 40 * 4671429 * 2
def baseEnd_4671429 : Nat := 2398688420352108746253995

theorem tailTrace_4671429 : CollatzResearch.WordTrace tailWord_4671429 prefixEnd_4671429 2398688420352108746253995 := by
  unfold tailWord_4671429
  simp only [CollatzResearch.WordTrace]
  refine ⟨170381012993218024400889341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113587341995478682933926227 170381012993218024400889341)
  ·
    refine ⟨63892879872456759150333503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170381012993218024400889341 63892879872456759150333503)
    ·
      refine ⟨95839319808685138725500255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63892879872456759150333503 95839319808685138725500255)
      ·
        refine ⟨143758979713027708088250383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95839319808685138725500255 143758979713027708088250383)
        ·
          refine ⟨215638469569541562132375575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143758979713027708088250383 215638469569541562132375575)
          ·
            refine ⟨323457704354312343198563363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215638469569541562132375575 323457704354312343198563363)
            ·
              refine ⟨485186556531468514797845045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323457704354312343198563363 485186556531468514797845045)
              ·
                refine ⟨45486239674825173262297973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 485186556531468514797845045 45486239674825173262297973)
                ·
                  refine ⟨4264334969514859993340435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45486239674825173262297973 4264334969514859993340435)
                  ·
                    refine ⟨6396502454272289990010653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4264334969514859993340435 6396502454272289990010653)
                    ·
                      refine ⟨2398688420352108746253995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6396502454272289990010653 2398688420352108746253995)
                      ·
                        rfl

theorem cell23_4671429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_4671429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671429 prefixEnd_4671429 := by exact prefixLift 4671429
  have htrace : WordTrace (prefixWord ++ tailWord_4671429) baseStart_4671429 baseEnd_4671429 := by
    simpa [prefixWord, tailWord_4671429, baseEnd_4671429] using wordTrace_append hprefix tailTrace_4671429
  have hstable : (prefixWord ++ tailWord_4671429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671429).length < 2 ^ (prefixWord ++ tailWord_4671429).sum := by decide
  have hdescent : baseEnd_4671429 < baseStart_4671429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671439 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 1, 5, 2]
def baseStart_4671439 : Nat := 118140960795 + 4671439 * 2 ^ 59
def prefixEnd_4671439 : Nat := 4983230072969 + 3 ^ 40 * 4671439 * 2
def baseEnd_4671439 : Nat := 2398693555158653707128949

theorem tailTrace_4671439 : CollatzResearch.WordTrace tailWord_4671439 prefixEnd_4671439 2398693555158653707128949 := by
  unfold tailWord_4671439
  simp only [CollatzResearch.WordTrace]
  refine ⟨170381377723181796108753371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113587585148787864072502247 170381377723181796108753371)
  ·
    refine ⟨255572066584772694163130057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170381377723181796108753371 255572066584772694163130057)
    ·
      refine ⟨191679049938579520622347543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255572066584772694163130057 191679049938579520622347543)
      ·
        refine ⟨287518574907869280933521315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191679049938579520622347543 287518574907869280933521315)
        ·
          refine ⟨431277862361803921400281973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287518574907869280933521315 431277862361803921400281973)
          ·
            refine ⟨40432299596419117631276435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 431277862361803921400281973 40432299596419117631276435)
            ·
              refine ⟨60648449394628676446914653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40432299596419117631276435 60648449394628676446914653)
              ·
                refine ⟨22743168522985753667592995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60648449394628676446914653 22743168522985753667592995)
                ·
                  refine ⟨34114752784478630501389493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22743168522985753667592995 34114752784478630501389493)
                  ·
                    refine ⟨3198258073544871609505265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34114752784478630501389493 3198258073544871609505265)
                    ·
                      refine ⟨2398693555158653707128949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198258073544871609505265 2398693555158653707128949)
                      ·
                        rfl

theorem cell23_4671439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 5, 2].length) (baseStart_4671439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671439 prefixEnd_4671439 := by exact prefixLift 4671439
  have htrace : WordTrace (prefixWord ++ tailWord_4671439) baseStart_4671439 baseEnd_4671439 := by
    simpa [prefixWord, tailWord_4671439, baseEnd_4671439] using wordTrace_append hprefix tailTrace_4671439
  have hstable : (prefixWord ++ tailWord_4671439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671439).length < 2 ^ (prefixWord ++ tailWord_4671439).sum := by decide
  have hdescent : baseEnd_4671439 < baseStart_4671439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671499 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 4]
def baseStart_4671499 : Nat := 118140960795 + 4671499 * 2 ^ 59
def prefixEnd_4671499 : Nat := 4983230072969 + 3 ^ 40 * 4671499 * 2
def baseEnd_4671499 : Nat := 2398724363997923472378673

theorem tailTrace_4671499 : CollatzResearch.WordTrace tailWord_4671499 prefixEnd_4671499 2398724363997923472378673 := by
  unfold tailWord_4671499
  simp only [CollatzResearch.WordTrace]
  refine ⟨170383566102964426355937551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113589044068642950903958367 170383566102964426355937551)
  ·
    refine ⟨255575349154446639533906327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170383566102964426355937551 255575349154446639533906327)
    ·
      refine ⟨383363023731669959300859491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255575349154446639533906327 383363023731669959300859491)
      ·
        refine ⟨575044535597504938951289237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383363023731669959300859491 575044535597504938951289237)
        ·
          refine ⟨26955212606133044013341683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 575044535597504938951289237 26955212606133044013341683)
          ·
            refine ⟨40432818909199566020012525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26955212606133044013341683 40432818909199566020012525)
            ·
              refine ⟨15162307090949837257504697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40432818909199566020012525 15162307090949837257504697)
              ·
                refine ⟨11371730318212377943128523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15162307090949837257504697 11371730318212377943128523)
                ·
                  refine ⟨17057595477318566914692785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11371730318212377943128523 17057595477318566914692785)
                  ·
                    refine ⟨12793196607988925186019589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17057595477318566914692785 12793196607988925186019589)
                    ·
                      refine ⟨2398724363997923472378673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12793196607988925186019589 2398724363997923472378673)
                      ·
                        rfl

theorem cell23_4671499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 4].length) (baseStart_4671499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671499 prefixEnd_4671499 := by exact prefixLift 4671499
  have htrace : WordTrace (prefixWord ++ tailWord_4671499) baseStart_4671499 baseEnd_4671499 := by
    simpa [prefixWord, tailWord_4671499, baseEnd_4671499] using wordTrace_append hprefix tailTrace_4671499
  have hstable : (prefixWord ++ tailWord_4671499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671499).length < 2 ^ (prefixWord ++ tailWord_4671499).sum := by decide
  have hdescent : baseEnd_4671499 < baseStart_4671499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671509 : List Nat := [1, 3, 2, 1, 6, 10]
def baseStart_4671509 : Nat := 118140960795 + 4671509 * 2 ^ 59
def prefixEnd_4671509 : Nat := 4983230072969 + 3 ^ 40 * 4671509 * 2
def baseEnd_4671509 : Nat := 9871314809894931824089

theorem tailTrace_4671509 : CollatzResearch.WordTrace tailWord_4671509 prefixEnd_4671509 9871314809894931824089 := by
  unfold tailWord_4671509
  simp only [CollatzResearch.WordTrace]
  refine ⟨170383930832928198063801581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113589287221952132042534387 170383930832928198063801581)
  ·
    refine ⟨63893974062348074273925593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170383930832928198063801581 63893974062348074273925593)
    ·
      refine ⟨47920480546761055705444195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63893974062348074273925593 47920480546761055705444195)
      ·
        refine ⟨71880720820141583558166293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47920480546761055705444195 71880720820141583558166293)
        ·
          refine ⟨3369408788444136729289045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71880720820141583558166293 3369408788444136729289045)
          ·
            refine ⟨9871314809894931824089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3369408788444136729289045 9871314809894931824089)
            ·
              rfl

theorem cell23_4671509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 10].length) (baseStart_4671509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671509 prefixEnd_4671509 := by exact prefixLift 4671509
  have htrace : WordTrace (prefixWord ++ tailWord_4671509) baseStart_4671509 baseEnd_4671509 := by
    simpa [prefixWord, tailWord_4671509, baseEnd_4671509] using wordTrace_append hprefix tailTrace_4671509
  have hstable : (prefixWord ++ tailWord_4671509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671509).length < 2 ^ (prefixWord ++ tailWord_4671509).sum := by decide
  have hdescent : baseEnd_4671509 < baseStart_4671509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671519 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 3]
def baseStart_4671519 : Nat := 118140960795 + 4671519 * 2 ^ 59
def prefixEnd_4671519 : Nat := 4983230072969 + 3 ^ 40 * 4671519 * 2
def baseEnd_4671519 : Nat := 2398734633611013394128581

theorem tailTrace_4671519 : CollatzResearch.WordTrace tailWord_4671519 prefixEnd_4671519 2398734633611013394128581 := by
  unfold tailWord_4671519
  simp only [CollatzResearch.WordTrace]
  refine ⟨170384295562891969771665611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113589530375261313181110407 170384295562891969771665611)
  ·
    refine ⟨255576443344337954657498417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170384295562891969771665611 255576443344337954657498417)
    ·
      refine ⟨191682332508253465993123813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255576443344337954657498417 191682332508253465993123813)
      ·
        refine ⟨35940437345297524873710715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191682332508253465993123813 35940437345297524873710715)
        ·
          refine ⟨53910656017946287310566073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35940437345297524873710715 53910656017946287310566073)
          ·
            refine ⟨40432992013459715482924555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53910656017946287310566073 40432992013459715482924555)
            ·
              refine ⟨60649488020189573224386833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40432992013459715482924555 60649488020189573224386833)
              ·
                refine ⟨45487116015142179918290125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60649488020189573224386833 45487116015142179918290125)
                ·
                  refine ⟨17057668505678317469358797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45487116015142179918290125 17057668505678317469358797)
                  ·
                    refine ⟨6396625689629369051009549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17057668505678317469358797 6396625689629369051009549)
                    ·
                      refine ⟨2398734633611013394128581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6396625689629369051009549 2398734633611013394128581)
                      ·
                        rfl

theorem cell23_4671519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_4671519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671519 prefixEnd_4671519 := by exact prefixLift 4671519
  have htrace : WordTrace (prefixWord ++ tailWord_4671519) baseStart_4671519 baseEnd_4671519 := by
    simpa [prefixWord, tailWord_4671519, baseEnd_4671519] using wordTrace_append hprefix tailTrace_4671519
  have hstable : (prefixWord ++ tailWord_4671519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671519).length < 2 ^ (prefixWord ++ tailWord_4671519).sum := by decide
  have hdescent : baseEnd_4671519 < baseStart_4671519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671536 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 3]
def baseStart_4671536 : Nat := 118140960795 + 4671536 * 2 ^ 59
def prefixEnd_4671536 : Nat := 4983230072969 + 3 ^ 40 * 4671536 * 2
def baseEnd_4671536 : Nat := 2398743362782139827616003

theorem tailTrace_4671536 : CollatzResearch.WordTrace tailWord_4671536 prefixEnd_4671536 2398743362782139827616003 := by
  unfold tailWord_4671536
  simp only [CollatzResearch.WordTrace]
  refine ⟨85192457801915190837517231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113589943735886921116689641 85192457801915190837517231)
  ·
    refine ⟨127788686702872786256275847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85192457801915190837517231 127788686702872786256275847)
    ·
      refine ⟨191683030054309179384413771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127788686702872786256275847 191683030054309179384413771)
      ·
        refine ⟨287524545081463769076620657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191683030054309179384413771 287524545081463769076620657)
        ·
          refine ⟨215643408811097826807465493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287524545081463769076620657 215643408811097826807465493)
          ·
            refine ⟨10108284788020210631599945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 215643408811097826807465493 10108284788020210631599945)
            ·
              refine ⟨7581213591015157973699959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10108284788020210631599945 7581213591015157973699959)
              ·
                refine ⟨11371820386522736960549939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7581213591015157973699959 11371820386522736960549939)
                ·
                  refine ⟨17057730579784105440824909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11371820386522736960549939 17057730579784105440824909)
                  ·
                    refine ⟨6396648967419039540309341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17057730579784105440824909 6396648967419039540309341)
                    ·
                      refine ⟨2398743362782139827616003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6396648967419039540309341 2398743362782139827616003)
                      ·
                        rfl

theorem cell23_4671536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 3].length) (baseStart_4671536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671536 prefixEnd_4671536 := by exact prefixLift 4671536
  have htrace : WordTrace (prefixWord ++ tailWord_4671536) baseStart_4671536 baseEnd_4671536 := by
    simpa [prefixWord, tailWord_4671536, baseEnd_4671536] using wordTrace_append hprefix tailTrace_4671536
  have hstable : (prefixWord ++ tailWord_4671536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671536).length < 2 ^ (prefixWord ++ tailWord_4671536).sum := by decide
  have hdescent : baseEnd_4671536 < baseStart_4671536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671549 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4671549 : Nat := 118140960795 + 4671549 * 2 ^ 59
def prefixEnd_4671549 : Nat := 4983230072969 + 3 ^ 40 * 4671549 * 2
def baseEnd_4671549 : Nat := 2398750038030648276753443

theorem tailTrace_4671549 : CollatzResearch.WordTrace tailWord_4671549 prefixEnd_4671549 2398750038030648276753443 := by
  unfold tailWord_4671549
  simp only [CollatzResearch.WordTrace]
  refine ⟨170385389752783284895257701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113590259835188856596838467 170385389752783284895257701)
  ·
    refine ⟨31947260578646865917860819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170385389752783284895257701 31947260578646865917860819)
    ·
      refine ⟨47920890867970298876791229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31947260578646865917860819 47920890867970298876791229)
      ·
        refine ⟨17970334075488862078796711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47920890867970298876791229 17970334075488862078796711)
        ·
          refine ⟨26955501113233293118195067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17970334075488862078796711 26955501113233293118195067)
          ·
            refine ⟨40433251669849939677292601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26955501113233293118195067 40433251669849939677292601)
            ·
              refine ⟨30324938752387454757969451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40433251669849939677292601 30324938752387454757969451)
              ·
                refine ⟨45487408128581182136954177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30324938752387454757969451 45487408128581182136954177)
                ·
                  refine ⟨34115556096435886602715633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45487408128581182136954177 34115556096435886602715633)
                  ·
                    refine ⟨25586667072326914952036725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34115556096435886602715633 25586667072326914952036725)
                    ·
                      refine ⟨2398750038030648276753443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25586667072326914952036725 2398750038030648276753443)
                      ·
                        rfl

theorem cell23_4671549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4671549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671549 prefixEnd_4671549 := by exact prefixLift 4671549
  have htrace : WordTrace (prefixWord ++ tailWord_4671549) baseStart_4671549 baseEnd_4671549 := by
    simpa [prefixWord, tailWord_4671549, baseEnd_4671549] using wordTrace_append hprefix tailTrace_4671549
  have hstable : (prefixWord ++ tailWord_4671549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671549).length < 2 ^ (prefixWord ++ tailWord_4671549).sum := by decide
  have hdescent : baseEnd_4671549 < baseStart_4671549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671599 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 7]
def baseStart_4671599 : Nat := 118140960795 + 4671599 * 2 ^ 59
def prefixEnd_4671599 : Nat := 4983230072969 + 3 ^ 40 * 4671599 * 2
def baseEnd_4671599 : Nat := 266530634673708120125357

theorem tailTrace_4671599 : CollatzResearch.WordTrace tailWord_4671599 prefixEnd_4671599 266530634673708120125357 := by
  unfold tailWord_4671599
  simp only [CollatzResearch.WordTrace]
  refine ⟨170387213402602143434577851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113591475601734762289718567 170387213402602143434577851)
  ·
    refine ⟨255580820103903215151866777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170387213402602143434577851 255580820103903215151866777)
    ·
      refine ⟨191685615077927411363900083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255580820103903215151866777 191685615077927411363900083)
      ·
        refine ⟨287528422616891117045850125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191685615077927411363900083 287528422616891117045850125)
        ·
          refine ⟨107823158481334168892193797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287528422616891117045850125 107823158481334168892193797)
          ·
            refine ⟨20216842215250156667286337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107823158481334168892193797 20216842215250156667286337)
            ·
              refine ⟨15162631661437617500464753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20216842215250156667286337 15162631661437617500464753)
              ·
                refine ⟨11371973746078213125348565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15162631661437617500464753 11371973746078213125348565)
                ·
                  refine ⟨266530634673708120125357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11371973746078213125348565 266530634673708120125357)
                  ·
                    rfl

theorem cell23_4671599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 7].length) (baseStart_4671599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671599 prefixEnd_4671599 := by exact prefixLift 4671599
  have htrace : WordTrace (prefixWord ++ tailWord_4671599) baseStart_4671599 baseEnd_4671599 := by
    simpa [prefixWord, tailWord_4671599, baseEnd_4671599] using wordTrace_append hprefix tailTrace_4671599
  have hstable : (prefixWord ++ tailWord_4671599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671599).length < 2 ^ (prefixWord ++ tailWord_4671599).sum := by decide
  have hdescent : baseEnd_4671599 < baseStart_4671599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671679 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_4671679 : Nat := 118140960795 + 4671679 * 2 ^ 59
def prefixEnd_4671679 : Nat := 4983230072969 + 3 ^ 40 * 4671679 * 2
def baseEnd_4671679 : Nat := 2398816790515732768127845

theorem tailTrace_4671679 : CollatzResearch.WordTrace tailWord_4671679 prefixEnd_4671679 2398816790515732768127845 := by
  unfold tailWord_4671679
  simp only [CollatzResearch.WordTrace]
  refine ⟨170390131242312317097490091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113593420828208211398326727 170390131242312317097490091)
  ·
    refine ⟨255585196863468475646235137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170390131242312317097490091 255585196863468475646235137)
    ·
      refine ⟨191688897647601356734676353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255585196863468475646235137 191688897647601356734676353)
      ·
        refine ⟨143766673235701017551007265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191688897647601356734676353 143766673235701017551007265)
        ·
          refine ⟨107825004926775763163255449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143766673235701017551007265 107825004926775763163255449)
          ·
            refine ⟨80868753695081822372441587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107825004926775763163255449 80868753695081822372441587)
            ·
              refine ⟨121303130542622733558662381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80868753695081822372441587 121303130542622733558662381)
              ·
                refine ⟨45488673953483525084498393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121303130542622733558662381 45488673953483525084498393)
                ·
                  refine ⟨34116505465112643813373795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45488673953483525084498393 34116505465112643813373795)
                  ·
                    refine ⟨51174758197668965720060693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34116505465112643813373795 51174758197668965720060693)
                    ·
                      refine ⟨2398816790515732768127845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51174758197668965720060693 2398816790515732768127845)
                      ·
                        rfl

theorem cell23_4671679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_4671679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671679 prefixEnd_4671679 := by exact prefixLift 4671679
  have htrace : WordTrace (prefixWord ++ tailWord_4671679) baseStart_4671679 baseEnd_4671679 := by
    simpa [prefixWord, tailWord_4671679, baseEnd_4671679] using wordTrace_append hprefix tailTrace_4671679
  have hstable : (prefixWord ++ tailWord_4671679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671679).length < 2 ^ (prefixWord ++ tailWord_4671679).sum := by decide
  have hdescent : baseEnd_4671679 < baseStart_4671679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671706 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 6]
def baseStart_4671706 : Nat := 118140960795 + 4671706 * 2 ^ 59
def prefixEnd_4671706 : Nat := 4983230072969 + 3 ^ 40 * 4671706 * 2
def baseEnd_4671706 : Nat := 266536739388156018054469

theorem tailTrace_4671706 : CollatzResearch.WordTrace tailWord_4671706 prefixEnd_4671706 266536739388156018054469 := by
  unfold tailWord_4671706
  simp only [CollatzResearch.WordTrace]
  refine ⟨42597779003303625177180743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113594077342143000472481981 42597779003303625177180743)
  ·
    refine ⟨63896668504955437765771115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42597779003303625177180743 63896668504955437765771115)
    ·
      refine ⟨95845002757433156648656673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63896668504955437765771115 95845002757433156648656673)
      ·
        refine ⟨71883752068074867486492505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95845002757433156648656673 71883752068074867486492505)
        ·
          refine ⟨53912814051056150614869379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71883752068074867486492505 53912814051056150614869379)
          ·
            refine ⟨80869221076584225922304069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53912814051056150614869379 80869221076584225922304069)
            ·
              refine ⟨15162978951859542360432013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80869221076584225922304069 15162978951859542360432013)
              ·
                refine ⟨5686117106947328385162005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15162978951859542360432013 5686117106947328385162005)
                ·
                  refine ⟨266536739388156018054469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5686117106947328385162005 266536739388156018054469)
                  ·
                    rfl

theorem cell23_4671706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_4671706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671706 prefixEnd_4671706 := by exact prefixLift 4671706
  have htrace : WordTrace (prefixWord ++ tailWord_4671706) baseStart_4671706 baseEnd_4671706 := by
    simpa [prefixWord, tailWord_4671706, baseEnd_4671706] using wordTrace_append hprefix tailTrace_4671706
  have hstable : (prefixWord ++ tailWord_4671706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671706).length < 2 ^ (prefixWord ++ tailWord_4671706).sum := by decide
  have hdescent : baseEnd_4671706 < baseStart_4671706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671714 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4671714 : Nat := 118140960795 + 4671714 * 2 ^ 59
def prefixEnd_4671714 : Nat := 4983230072969 + 3 ^ 40 * 4671714 * 2
def baseEnd_4671714 : Nat := 799611587446213377063395

theorem tailTrace_4671714 : CollatzResearch.WordTrace tailWord_4671714 prefixEnd_4671714 799611587446213377063395 := by
  unfold tailWord_4671714
  simp only [CollatzResearch.WordTrace]
  refine ⟨42597851949296379518753549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113594271864790345383342797 42597851949296379518753549)
  ·
    refine ⟨15974194480986142319532581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42597851949296379518753549 15974194480986142319532581)
    ·
      refine ⟨2995161465184901684912359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15974194480986142319532581 2995161465184901684912359)
      ·
        refine ⟨4492742197777352527368539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2995161465184901684912359 4492742197777352527368539)
        ·
          refine ⟨6739113296666028791052809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4492742197777352527368539 6739113296666028791052809)
          ·
            refine ⟨5054334972499521593289607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6739113296666028791052809 5054334972499521593289607)
            ·
              refine ⟨7581502458749282389934411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054334972499521593289607 7581502458749282389934411)
              ·
                refine ⟨11372253688123923584901617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7581502458749282389934411 11372253688123923584901617)
                ·
                  refine ⟨8529190266092942688676213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11372253688123923584901617 8529190266092942688676213)
                  ·
                    refine ⟨799611587446213377063395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8529190266092942688676213 799611587446213377063395)
                    ·
                      rfl

theorem cell23_4671714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4671714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671714 prefixEnd_4671714 := by exact prefixLift 4671714
  have htrace : WordTrace (prefixWord ++ tailWord_4671714) baseStart_4671714 baseEnd_4671714 := by
    simpa [prefixWord, tailWord_4671714, baseEnd_4671714] using wordTrace_append hprefix tailTrace_4671714
  have hstable : (prefixWord ++ tailWord_4671714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671714).length < 2 ^ (prefixWord ++ tailWord_4671714).sum := by decide
  have hdescent : baseEnd_4671714 < baseStart_4671714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671720 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_4671720 : Nat := 118140960795 + 4671720 * 2 ^ 59
def prefixEnd_4671720 : Nat := 4983230072969 + 3 ^ 40 * 4671720 * 2
def baseEnd_4671720 : Nat := 2398837843222567107715157

theorem tailTrace_4671720 : CollatzResearch.WordTrace tailWord_4671720 prefixEnd_4671720 2398837843222567107715157 := by
  unfold tailWord_4671720
  simp only [CollatzResearch.WordTrace]
  refine ⟨85195813317581890549866307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113594417756775854066488409 85195813317581890549866307)
  ·
    refine ⟨127793719976372835824799461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85195813317581890549866307 127793719976372835824799461)
    ·
      refine ⟨23961322495569906717149899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127793719976372835824799461 23961322495569906717149899)
      ·
        refine ⟨35941983743354860075724849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23961322495569906717149899 35941983743354860075724849)
        ·
          refine ⟨26956487807516145056793637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35941983743354860075724849 26956487807516145056793637)
          ·
            refine ⟨5054341463909277198148807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26956487807516145056793637 5054341463909277198148807)
            ·
              refine ⟨7581512195863915797223211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054341463909277198148807 7581512195863915797223211)
              ·
                refine ⟨11372268293795873695834817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7581512195863915797223211 11372268293795873695834817)
                ·
                  refine ⟨8529201220346905271876113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11372268293795873695834817 8529201220346905271876113)
                  ·
                    refine ⟨6396900915260178953907085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8529201220346905271876113 6396900915260178953907085)
                    ·
                      refine ⟨2398837843222567107715157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6396900915260178953907085 2398837843222567107715157)
                      ·
                        rfl

theorem cell23_4671720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_4671720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671720 prefixEnd_4671720 := by exact prefixLift 4671720
  have htrace : WordTrace (prefixWord ++ tailWord_4671720) baseStart_4671720 baseEnd_4671720 := by
    simpa [prefixWord, tailWord_4671720, baseEnd_4671720] using wordTrace_append hprefix tailTrace_4671720
  have hstable : (prefixWord ++ tailWord_4671720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671720).length < 2 ^ (prefixWord ++ tailWord_4671720).sum := by decide
  have hdescent : baseEnd_4671720 < baseStart_4671720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671743 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 4, 3, 2]
def baseStart_4671743 : Nat := 118140960795 + 4671743 * 2 ^ 59
def prefixEnd_4671743 : Nat := 4983230072969 + 3 ^ 40 * 4671743 * 2
def baseEnd_4671743 : Nat := 2398849653277620517727551

theorem tailTrace_4671743 : CollatzResearch.WordTrace tailWord_4671743 prefixEnd_4671743 2398849653277620517727551 := by
  unfold tailWord_4671743
  simp only [CollatzResearch.WordTrace]
  refine ⟨170392465514080456027819883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113594977009386970685213255 170392465514080456027819883)
  ·
    refine ⟨255588698271120684041729825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170392465514080456027819883 255588698271120684041729825)
    ·
      refine ⟨191691523703340513031297369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255588698271120684041729825 191691523703340513031297369)
      ·
        refine ⟨143768642777505384773473027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191691523703340513031297369 143768642777505384773473027)
        ·
          refine ⟨215652964166258077160209541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143768642777505384773473027 215652964166258077160209541)
          ·
            refine ⟨40434930781173389467539289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215652964166258077160209541 40434930781173389467539289)
            ·
              refine ⟨30326198085880042100654467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40434930781173389467539289 30326198085880042100654467)
              ·
                refine ⟨45489297128820063150981701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30326198085880042100654467 45489297128820063150981701)
                ·
                  refine ⟨8529243211653761840809069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45489297128820063150981701 8529243211653761840809069)
                  ·
                    refine ⟨3198466204370160690303401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8529243211653761840809069 3198466204370160690303401)
                    ·
                      refine ⟨2398849653277620517727551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198466204370160690303401 2398849653277620517727551)
                      ·
                        rfl

theorem cell23_4671743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 3, 2].length) (baseStart_4671743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671743 prefixEnd_4671743 := by exact prefixLift 4671743
  have htrace : WordTrace (prefixWord ++ tailWord_4671743) baseStart_4671743 baseEnd_4671743 := by
    simpa [prefixWord, tailWord_4671743, baseEnd_4671743] using wordTrace_append hprefix tailTrace_4671743
  have hstable : (prefixWord ++ tailWord_4671743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671743).length < 2 ^ (prefixWord ++ tailWord_4671743).sum := by decide
  have hdescent : baseEnd_4671743 < baseStart_4671743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671770 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 1, 5]
def baseStart_4671770 : Nat := 118140960795 + 4671770 * 2 ^ 59
def prefixEnd_4671770 : Nat := 4983230072969 + 3 ^ 40 * 4671770 * 2
def baseEnd_4671770 : Nat := 799621172418430637363309

theorem tailTrace_4671770 : CollatzResearch.WordTrace tailWord_4671770 prefixEnd_4671770 799621172418430637363309 := by
  unfold tailWord_4671770
  simp only [CollatzResearch.WordTrace]
  refine ⟨42598362571245659909763191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113595633523321759759368509 42598362571245659909763191)
  ·
    refine ⟨63897543856868489864644787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42598362571245659909763191 63897543856868489864644787)
    ·
      refine ⟨95846315785302734796967181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63897543856868489864644787 95846315785302734796967181)
      ·
        refine ⟨35942368419488525548862693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95846315785302734796967181 35942368419488525548862693)
        ·
          refine ⟨6739194078654098540411755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35942368419488525548862693 6739194078654098540411755)
          ·
            refine ⟨10108791117981147810617633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6739194078654098540411755 10108791117981147810617633)
            ·
              refine ⟨7581593338485860857963225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10108791117981147810617633 7581593338485860857963225)
              ·
                refine ⟨5686195003864395643472419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7581593338485860857963225 5686195003864395643472419)
                ·
                  refine ⟨8529292505796593465208629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5686195003864395643472419 8529292505796593465208629)
                  ·
                    refine ⟨799621172418430637363309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8529292505796593465208629 799621172418430637363309)
                    ·
                      rfl

theorem cell23_4671770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_4671770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671770 prefixEnd_4671770 := by exact prefixLift 4671770
  have htrace : WordTrace (prefixWord ++ tailWord_4671770) baseStart_4671770 baseEnd_4671770 := by
    simpa [prefixWord, tailWord_4671770, baseEnd_4671770] using wordTrace_append hprefix tailTrace_4671770
  have hstable : (prefixWord ++ tailWord_4671770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671770).length < 2 ^ (prefixWord ++ tailWord_4671770).sum := by decide
  have hdescent : baseEnd_4671770 < baseStart_4671770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671823 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 6, 1, 3]
def baseStart_4671823 : Nat := 118140960795 + 4671823 * 2 ^ 59
def prefixEnd_4671823 : Nat := 4983230072969 + 3 ^ 40 * 4671823 * 2
def baseEnd_4671823 : Nat := 2398890731729980204727183

theorem tailTrace_4671823 : CollatzResearch.WordTrace tailWord_4671823 prefixEnd_4671823 2398890731729980204727183 := by
  unfold tailWord_4671823
  simp only [CollatzResearch.WordTrace]
  refine ⟨170395383353790629690732123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113596922235860419793821415 170395383353790629690732123)
  ·
    refine ⟨255593075030685944536098185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170395383353790629690732123 255593075030685944536098185)
    ·
      refine ⟨191694806273014458402073639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255593075030685944536098185 191694806273014458402073639)
      ·
        refine ⟨287542209409521687603110459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191694806273014458402073639 287542209409521687603110459)
        ·
          refine ⟨431313314114282531404665689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287542209409521687603110459 431313314114282531404665689)
          ·
            refine ⟨323484985585711898553499267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431313314114282531404665689 323484985585711898553499267)
            ·
              refine ⟨485227478378567847830248901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323484985585711898553499267 485227478378567847830248901)
              ·
                refine ⟨90980152195981471468171669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 485227478378567847830248901 90980152195981471468171669)
                ·
                  refine ⟨4264694634186631475070547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90980152195981471468171669 4264694634186631475070547)
                  ·
                    refine ⟨6397041951279947212605821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4264694634186631475070547 6397041951279947212605821)
                    ·
                      refine ⟨2398890731729980204727183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6397041951279947212605821 2398890731729980204727183)
                      ·
                        rfl

theorem cell23_4671823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 1, 3].length) (baseStart_4671823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671823 prefixEnd_4671823 := by exact prefixLift 4671823
  have htrace : WordTrace (prefixWord ++ tailWord_4671823) baseStart_4671823 baseEnd_4671823 := by
    simpa [prefixWord, tailWord_4671823, baseEnd_4671823] using wordTrace_append hprefix tailTrace_4671823
  have hstable : (prefixWord ++ tailWord_4671823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671823).length < 2 ^ (prefixWord ++ tailWord_4671823).sum := by decide
  have hdescent : baseEnd_4671823 < baseStart_4671823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671838 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4671838 : Nat := 118140960795 + 4671838 * 2 ^ 59
def prefixEnd_4671838 : Nat := 4983230072969 + 3 ^ 40 * 4671838 * 2
def baseEnd_4671838 : Nat := 799632811313265882013205

theorem tailTrace_4671838 : CollatzResearch.WordTrace tailWord_4671838 prefixEnd_4671838 799632811313265882013205 := by
  unfold tailWord_4671838
  simp only [CollatzResearch.WordTrace]
  refine ⟨21299491306092035906566021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113597286965824191501685445 21299491306092035906566021)
  ·
    refine ⟨3993654619892256732481129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21299491306092035906566021 3993654619892256732481129)
    ·
      refine ⟨2995240964919192549360847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3993654619892256732481129 2995240964919192549360847)
      ·
        refine ⟨4492861447378788824041271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2995240964919192549360847 4492861447378788824041271)
        ·
          refine ⟨6739292171068183236061907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4492861447378788824041271 6739292171068183236061907)
          ·
            refine ⟨10108938256602274854092861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6739292171068183236061907 10108938256602274854092861)
            ·
              refine ⟨3790851846225853070284823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10108938256602274854092861 3790851846225853070284823)
              ·
                refine ⟨5686277769338779605427235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3790851846225853070284823 5686277769338779605427235)
                ·
                  refine ⟨8529416654008169408140853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5686277769338779605427235 8529416654008169408140853)
                  ·
                    refine ⟨799632811313265882013205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8529416654008169408140853 799632811313265882013205)
                    ·
                      rfl

theorem cell23_4671838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4671838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671838 prefixEnd_4671838 := by exact prefixLift 4671838
  have htrace : WordTrace (prefixWord ++ tailWord_4671838) baseStart_4671838 baseEnd_4671838 := by
    simpa [prefixWord, tailWord_4671838, baseEnd_4671838] using wordTrace_append hprefix tailTrace_4671838
  have hstable : (prefixWord ++ tailWord_4671838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671838).length < 2 ^ (prefixWord ++ tailWord_4671838).sum := by decide
  have hdescent : baseEnd_4671838 < baseStart_4671838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671840 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 3]
def baseStart_4671840 : Nat := 118140960795 + 4671840 * 2 ^ 59
def prefixEnd_4671840 : Nat := 4983230072969 + 3 ^ 40 * 4671840 * 2
def baseEnd_4671840 : Nat := 2398899460901106638214605

theorem tailTrace_4671840 : CollatzResearch.WordTrace tailWord_4671840 prefixEnd_4671840 2398899460901106638214605 := by
  unfold tailWord_4671840
  simp only [CollatzResearch.WordTrace]
  refine ⟨85198001697364520797050487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113597335596486027729400649 85198001697364520797050487)
  ·
    refine ⟨127797002546046781195575731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85198001697364520797050487 127797002546046781195575731)
    ·
      refine ⟨191695503819070171793363597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127797002546046781195575731 191695503819070171793363597)
      ·
        refine ⟨71885813932151314422511349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191695503819070171793363597 71885813932151314422511349)
        ·
          refine ⟨6739295056139185727110439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71885813932151314422511349 6739295056139185727110439)
          ·
            refine ⟨10108942584208778590665659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6739295056139185727110439 10108942584208778590665659)
            ·
              refine ⟨15163413876313167885998489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10108942584208778590665659 15163413876313167885998489)
              ·
                refine ⟨11372560407234875914498867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15163413876313167885998489 11372560407234875914498867)
                ·
                  refine ⟨17058840610852313871748301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11372560407234875914498867 17058840610852313871748301)
                  ·
                    refine ⟨6397065229069617701905613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17058840610852313871748301 6397065229069617701905613)
                    ·
                      refine ⟨2398899460901106638214605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6397065229069617701905613 2398899460901106638214605)
                      ·
                        rfl

theorem cell23_4671840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_4671840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671840 prefixEnd_4671840 := by exact prefixLift 4671840
  have htrace : WordTrace (prefixWord ++ tailWord_4671840) baseStart_4671840 baseEnd_4671840 := by
    simpa [prefixWord, tailWord_4671840, baseEnd_4671840] using wordTrace_append hprefix tailTrace_4671840
  have hstable : (prefixWord ++ tailWord_4671840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671840).length < 2 ^ (prefixWord ++ tailWord_4671840).sum := by decide
  have hdescent : baseEnd_4671840 < baseStart_4671840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671873 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 1, 8]
def baseStart_4671873 : Nat := 118140960795 + 4671873 * 2 ^ 59
def prefixEnd_4671873 : Nat := 4983230072969 + 3 ^ 40 * 4671873 * 2
def baseEnd_4671873 : Nat := 799638801920901669700651

theorem tailTrace_4671873 : CollatzResearch.WordTrace tailWord_4671873 prefixEnd_4671873 799638801920901669700651 := by
  unfold tailWord_4671873
  simp only [CollatzResearch.WordTrace]
  refine ⟨170397207003609488230052273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113598138002406325486701515 170397207003609488230052273)
  ·
    refine ⟨127797905252707116172539205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170397207003609488230052273 127797905252707116172539205)
    ·
      refine ⟨23962107234882584282351101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127797905252707116172539205 23962107234882584282351101)
      ·
        refine ⟨8985790213080969105881663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23962107234882584282351101 8985790213080969105881663)
        ·
          refine ⟨13478685319621453658822495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8985790213080969105881663 13478685319621453658822495)
          ·
            refine ⟨20218027979432180488233743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13478685319621453658822495 20218027979432180488233743)
            ·
              refine ⟨30327041969148270732350615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20218027979432180488233743 30327041969148270732350615)
              ·
                refine ⟨45490562953722406098525923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30327041969148270732350615 45490562953722406098525923)
                ·
                  refine ⟨68235844430583609147788885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45490562953722406098525923 68235844430583609147788885)
                  ·
                    refine ⟨799638801920901669700651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68235844430583609147788885 799638801920901669700651)
                    ·
                      rfl

theorem cell23_4671873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_4671873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671873 prefixEnd_4671873 := by exact prefixLift 4671873
  have htrace : WordTrace (prefixWord ++ tailWord_4671873) baseStart_4671873 baseEnd_4671873 := by
    simpa [prefixWord, tailWord_4671873, baseEnd_4671873] using wordTrace_append hprefix tailTrace_4671873
  have hstable : (prefixWord ++ tailWord_4671873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671873).length < 2 ^ (prefixWord ++ tailWord_4671873).sum := by decide
  have hdescent : baseEnd_4671873 < baseStart_4671873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671874 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_4671874 : Nat := 118140960795 + 4671874 * 2 ^ 59
def prefixEnd_4671874 : Nat := 4983230072969 + 3 ^ 40 * 4671874 * 2
def baseEnd_4671874 : Nat := 2398916919243359505189449

theorem tailTrace_4671874 : CollatzResearch.WordTrace tailWord_4671874 prefixEnd_4671874 2398916919243359505189449 := by
  unfold tailWord_4671874
  simp only [CollatzResearch.WordTrace]
  refine ⟨42599310869151466350209669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113598162317737243600559117 42599310869151466350209669)
  ·
    refine ⟨7987370787965899940664313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42599310869151466350209669 7987370787965899940664313)
    ·
      refine ⟨5990528090974424955498235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7987370787965899940664313 5990528090974424955498235)
      ·
        refine ⟨8985792136461637433247353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5990528090974424955498235 8985792136461637433247353)
        ·
          refine ⟨6739344102346228074935515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8985792136461637433247353 6739344102346228074935515)
          ·
            refine ⟨10109016153519342112403273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6739344102346228074935515 10109016153519342112403273)
            ·
              refine ⟨7581762115139506584302455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10109016153519342112403273 7581762115139506584302455)
              ·
                refine ⟨11372643172709259876453683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7581762115139506584302455 11372643172709259876453683)
                ·
                  refine ⟨17058964759063889814680525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11372643172709259876453683 17058964759063889814680525)
                  ·
                    refine ⟨6397111784648958680505197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17058964759063889814680525 6397111784648958680505197)
                    ·
                      refine ⟨2398916919243359505189449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6397111784648958680505197 2398916919243359505189449)
                      ·
                        rfl

theorem cell23_4671874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_4671874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671874 prefixEnd_4671874 := by exact prefixLift 4671874
  have htrace : WordTrace (prefixWord ++ tailWord_4671874) baseStart_4671874 baseEnd_4671874 := by
    simpa [prefixWord, tailWord_4671874, baseEnd_4671874] using wordTrace_append hprefix tailTrace_4671874
  have hstable : (prefixWord ++ tailWord_4671874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671874).length < 2 ^ (prefixWord ++ tailWord_4671874).sum := by decide
  have hdescent : baseEnd_4671874 < baseStart_4671874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671901 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_4671901 : Nat := 118140960795 + 4671901 * 2 ^ 59
def prefixEnd_4671901 : Nat := 4983230072969 + 3 ^ 40 * 4671901 * 2
def baseEnd_4671901 : Nat := 2398930783221030899551825

theorem tailTrace_4671901 : CollatzResearch.WordTrace tailWord_4671901 prefixEnd_4671901 2398930783221030899551825 := by
  unfold tailWord_4671901
  simp only [CollatzResearch.WordTrace]
  refine ⟨170398228247508049012071557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113598818831672032674714371 170398228247508049012071557)
  ·
    refine ⟨31949667796407759189763417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170398228247508049012071557 31949667796407759189763417)
    ·
      refine ⟨23962250847305819392322563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31949667796407759189763417 23962250847305819392322563)
      ·
        refine ⟨35943376270958729088483845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23962250847305819392322563 35943376270958729088483845)
        ·
          refine ⟨6739383050804761704090721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35943376270958729088483845 6739383050804761704090721)
          ·
            refine ⟨5054537288103571278068041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6739383050804761704090721 5054537288103571278068041)
            ·
              refine ⟨3790902966077678458551031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5054537288103571278068041 3790902966077678458551031)
              ·
                refine ⟨5686354449116517687826547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3790902966077678458551031 5686354449116517687826547)
                ·
                  refine ⟨8529531673674776531739821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5686354449116517687826547 8529531673674776531739821)
                  ·
                    refine ⟨3198574377628041199402433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8529531673674776531739821 3198574377628041199402433)
                    ·
                      refine ⟨2398930783221030899551825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198574377628041199402433 2398930783221030899551825)
                      ·
                        rfl

theorem cell23_4671901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_4671901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671901 prefixEnd_4671901 := by exact prefixLift 4671901
  have htrace : WordTrace (prefixWord ++ tailWord_4671901) baseStart_4671901 baseEnd_4671901 := by
    simpa [prefixWord, tailWord_4671901, baseEnd_4671901] using wordTrace_append hprefix tailTrace_4671901
  have hstable : (prefixWord ++ tailWord_4671901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671901).length < 2 ^ (prefixWord ++ tailWord_4671901).sum := by decide
  have hdescent : baseEnd_4671901 < baseStart_4671901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671933 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_4671933 : Nat := 118140960795 + 4671933 * 2 ^ 59
def prefixEnd_4671933 : Nat := 4983230072969 + 3 ^ 40 * 4671933 * 2
def baseEnd_4671933 : Nat := 799649071533991591450559

theorem tailTrace_4671933 : CollatzResearch.WordTrace tailWord_4671933 prefixEnd_4671933 799649071533991591450559 := by
  unfold tailWord_4671933
  simp only [CollatzResearch.WordTrace]
  refine ⟨170399395383392118477236453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113599596922261412318157635 170399395383392118477236453)
  ·
    refine ⟨31949886634386022214481835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170399395383392118477236453 31949886634386022214481835)
    ·
      refine ⟨47924829951579033321722753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31949886634386022214481835 47924829951579033321722753)
      ·
        refine ⟨35943622463684274991292065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47924829951579033321722753 35943622463684274991292065)
        ·
          refine ⟨26957716847763206243469049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35943622463684274991292065 26957716847763206243469049)
          ·
            refine ⟨20218287635822404682601787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26957716847763206243469049 20218287635822404682601787)
            ·
              refine ⟨30327431453733607023902681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20218287635822404682601787 30327431453733607023902681)
              ·
                refine ⟨22745573590300205267927011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30327431453733607023902681 22745573590300205267927011)
                ·
                  refine ⟨34118360385450307901890517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22745573590300205267927011 34118360385450307901890517)
                  ·
                    refine ⟨799649071533991591450559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34118360385450307901890517 799649071533991591450559)
                    ·
                      rfl

theorem cell23_4671933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_4671933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671933 prefixEnd_4671933 := by exact prefixLift 4671933
  have htrace : WordTrace (prefixWord ++ tailWord_4671933) baseStart_4671933 baseEnd_4671933 := by
    simpa [prefixWord, tailWord_4671933, baseEnd_4671933] using wordTrace_append hprefix tailTrace_4671933
  have hstable : (prefixWord ++ tailWord_4671933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671933).length < 2 ^ (prefixWord ++ tailWord_4671933).sum := by decide
  have hdescent : baseEnd_4671933 < baseStart_4671933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4671953 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_4671953 : Nat := 118140960795 + 4671953 * 2 ^ 59
def prefixEnd_4671953 : Nat := 4983230072969 + 3 ^ 40 * 4671953 * 2
def baseEnd_4671953 : Nat := 2398957484215064696101585

theorem tailTrace_4671953 : CollatzResearch.WordTrace tailWord_4671953 prefixEnd_4671953 2398957484215064696101585 := by
  unfold tailWord_4671953
  simp only [CollatzResearch.WordTrace]
  refine ⟨170400124843319661892964513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113600083228879774595309675 170400124843319661892964513)
  ·
    refine ⟨127800093632489746419723385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170400124843319661892964513 127800093632489746419723385)
    ·
      refine ⟨95850070224367309814792539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127800093632489746419723385 95850070224367309814792539)
      ·
        refine ⟨143775105336550964722188809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95850070224367309814792539 143775105336550964722188809)
        ·
          refine ⟨107831329002413223541641607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143775105336550964722188809 107831329002413223541641607)
          ·
            refine ⟨161746993503619835312462411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107831329002413223541641607 161746993503619835312462411)
            ·
              refine ⟨242620490255429752968693617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161746993503619835312462411 242620490255429752968693617)
              ·
                refine ⟨181965367691572314726520213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242620490255429752968693617 181965367691572314726520213)
                ·
                  refine ⟨8529626610542452252805635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 181965367691572314726520213 8529626610542452252805635)
                  ·
                    refine ⟨12794439915813678379208453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8529626610542452252805635 12794439915813678379208453)
                    ·
                      refine ⟨2398957484215064696101585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12794439915813678379208453 2398957484215064696101585)
                      ·
                        rfl

theorem cell23_4671953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_4671953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4671953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4671953 prefixEnd_4671953 := by exact prefixLift 4671953
  have htrace : WordTrace (prefixWord ++ tailWord_4671953) baseStart_4671953 baseEnd_4671953 := by
    simpa [prefixWord, tailWord_4671953, baseEnd_4671953] using wordTrace_append hprefix tailTrace_4671953
  have hstable : (prefixWord ++ tailWord_4671953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4671953).length < 2 ^ (prefixWord ++ tailWord_4671953).sum := by decide
  have hdescent : baseEnd_4671953 < baseStart_4671953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4671953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672054 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_4672054 : Nat := 118140960795 + 4672054 * 2 ^ 59
def prefixEnd_4672054 : Nat := 4983230072969 + 3 ^ 40 * 4672054 * 2
def baseEnd_4672054 : Nat := 2399009345761168800938621

theorem tailTrace_4672054 : CollatzResearch.WordTrace tailWord_4672054 prefixEnd_4672054 2399009345761168800938621 := by
  unfold tailWord_4672054
  simp only [CollatzResearch.WordTrace]
  refine ⟨10650238038497109758899451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113602539077302504094927477 10650238038497109758899451)
  ·
    refine ⟨15975357057745664638349177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10650238038497109758899451 15975357057745664638349177)
    ·
      refine ⟨11981517793309248478761883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15975357057745664638349177 11981517793309248478761883)
      ·
        refine ⟨17972276689963872718142825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11981517793309248478761883 17972276689963872718142825)
        ·
          refine ⟨13479207517472904538607119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17972276689963872718142825 13479207517472904538607119)
          ·
            refine ⟨20218811276209356807910679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13479207517472904538607119 20218811276209356807910679)
            ·
              refine ⟨30328216914314035211866019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20218811276209356807910679 30328216914314035211866019)
              ·
                refine ⟨45492325371471052817799029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30328216914314035211866019 45492325371471052817799029)
                ·
                  refine ⟨4264905503575411201668659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45492325371471052817799029 4264905503575411201668659)
                  ·
                    refine ⟨6397358255363116802502989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4264905503575411201668659 6397358255363116802502989)
                    ·
                      refine ⟨2399009345761168800938621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6397358255363116802502989 2399009345761168800938621)
                      ·
                        rfl

theorem cell23_4672054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_4672054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672054 prefixEnd_4672054 := by exact prefixLift 4672054
  have htrace : WordTrace (prefixWord ++ tailWord_4672054) baseStart_4672054 baseEnd_4672054 := by
    simpa [prefixWord, tailWord_4672054, baseEnd_4672054] using wordTrace_append hprefix tailTrace_4672054
  have hstable : (prefixWord ++ tailWord_4672054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672054).length < 2 ^ (prefixWord ++ tailWord_4672054).sum := by decide
  have hdescent : baseEnd_4672054 < baseStart_4672054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672071 : List Nat := [1, 1, 4, 1, 4, 2, 2, 3, 1, 1, 3]
def baseStart_4672071 : Nat := 118140960795 + 4672071 * 2 ^ 59
def prefixEnd_4672071 : Nat := 4983230072969 + 3 ^ 40 * 4672071 * 2
def baseEnd_4672071 : Nat := 2399018074932295234426043

theorem tailTrace_4672071 : CollatzResearch.WordTrace tailWord_4672071 prefixEnd_4672071 2399018074932295234426043 := by
  unfold tailWord_4672071
  simp only [CollatzResearch.WordTrace]
  refine ⟨170404428656892168045760067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113602952437928112030506711 170404428656892168045760067)
  ·
    refine ⟨255606642985338252068640101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170404428656892168045760067 255606642985338252068640101)
    ·
      refine ⟨47926245559750922262870019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255606642985338252068640101 47926245559750922262870019)
      ·
        refine ⟨71889368339626383394305029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47926245559750922262870019 71889368339626383394305029)
        ·
          refine ⟨13479256563679946886432193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71889368339626383394305029 13479256563679946886432193)
          ·
            refine ⟨10109442422759960164824145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13479256563679946886432193 10109442422759960164824145)
            ·
              refine ⟨7582081817069970123618109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10109442422759960164824145 7582081817069970123618109)
              ·
                refine ⟨2843280681401238796356791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7582081817069970123618109 2843280681401238796356791)
                ·
                  refine ⟨4264921022101858194535187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2843280681401238796356791 4264921022101858194535187)
                  ·
                    refine ⟨6397381533152787291802781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4264921022101858194535187 6397381533152787291802781)
                    ·
                      refine ⟨2399018074932295234426043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6397381533152787291802781 2399018074932295234426043)
                      ·
                        rfl

theorem cell23_4672071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_4672071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672071 prefixEnd_4672071 := by exact prefixLift 4672071
  have htrace : WordTrace (prefixWord ++ tailWord_4672071) baseStart_4672071 baseEnd_4672071 := by
    simpa [prefixWord, tailWord_4672071, baseEnd_4672071] using wordTrace_append hprefix tailTrace_4672071
  have hstable : (prefixWord ++ tailWord_4672071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672071).length < 2 ^ (prefixWord ++ tailWord_4672071).sum := by decide
  have hdescent : baseEnd_4672071 < baseStart_4672071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672073 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_4672073 : Nat := 118140960795 + 4672073 * 2 ^ 59
def prefixEnd_4672073 : Nat := 4983230072969 + 3 ^ 40 * 4672073 * 2
def baseEnd_4672073 : Nat := 2399019101893604226601033

theorem tailTrace_4672073 : CollatzResearch.WordTrace tailWord_4672073 prefixEnd_4672073 2399019101893604226601033 := by
  unfold tailWord_4672073
  simp only [CollatzResearch.WordTrace]
  refine ⟨170404501602884922387332873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113603001068589948258221915 170404501602884922387332873)
  ·
    refine ⟨127803376202163691790499655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170404501602884922387332873 127803376202163691790499655)
    ·
      refine ⟨191705064303245537685749483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127803376202163691790499655 191705064303245537685749483)
      ·
        refine ⟨287557596454868306528624225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191705064303245537685749483 287557596454868306528624225)
        ·
          refine ⟨215668197341151229896468169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287557596454868306528624225 215668197341151229896468169)
          ·
            refine ⟨161751148005863422422351127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215668197341151229896468169 161751148005863422422351127)
            ·
              refine ⟨242626722008795133633526691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161751148005863422422351127 242626722008795133633526691)
              ·
                refine ⟨363940083013192700450290037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242626722008795133633526691 363940083013192700450290037)
                ·
                  refine ⟨34119382782486815667214691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 363940083013192700450290037 34119382782486815667214691)
                  ·
                    refine ⟨51179074173730223500822037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34119382782486815667214691 51179074173730223500822037)
                    ·
                      refine ⟨2399019101893604226601033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51179074173730223500822037 2399019101893604226601033)
                      ·
                        rfl

theorem cell23_4672073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_4672073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672073 prefixEnd_4672073 := by exact prefixLift 4672073
  have htrace : WordTrace (prefixWord ++ tailWord_4672073) baseStart_4672073 baseEnd_4672073 := by
    simpa [prefixWord, tailWord_4672073, baseEnd_4672073] using wordTrace_append hprefix tailTrace_4672073
  have hstable : (prefixWord ++ tailWord_4672073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672073).length < 2 ^ (prefixWord ++ tailWord_4672073).sum := by decide
  have hdescent : baseEnd_4672073 < baseStart_4672073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672074 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 1, 5]
def baseStart_4672074 : Nat := 118140960795 + 4672074 * 2 ^ 59
def prefixEnd_4672074 : Nat := 4983230072969 + 3 ^ 40 * 4672074 * 2
def baseEnd_4672074 : Nat := 799673205124752907562843

theorem tailTrace_4672074 : CollatzResearch.WordTrace tailWord_4672074 prefixEnd_4672074 799673205124752907562843 := by
  unfold tailWord_4672074
  simp only [CollatzResearch.WordTrace]
  refine ⟨42601134518970324889529819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113603025383920866372079517 42601134518970324889529819)
  ·
    refine ⟨63901701778455487334294729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42601134518970324889529819 63901701778455487334294729)
    ·
      refine ⟨47926276333841615500721047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63901701778455487334294729 47926276333841615500721047)
      ·
        refine ⟨71889414500762423251081571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47926276333841615500721047 71889414500762423251081571)
        ·
          refine ⟨107834121751143634876622357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71889414500762423251081571 107834121751143634876622357)
          ·
            refine ⟨5054724457084857884841673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107834121751143634876622357 5054724457084857884841673)
            ·
              refine ⟨3791043342813643413631255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5054724457084857884841673 3791043342813643413631255)
              ·
                refine ⟨5686565014220465120446883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791043342813643413631255 5686565014220465120446883)
                ·
                  refine ⟨8529847521330697680670325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5686565014220465120446883 8529847521330697680670325)
                  ·
                    refine ⟨799673205124752907562843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8529847521330697680670325 799673205124752907562843)
                    ·
                      rfl

theorem cell23_4672074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_4672074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672074 prefixEnd_4672074 := by exact prefixLift 4672074
  have htrace : WordTrace (prefixWord ++ tailWord_4672074) baseStart_4672074 baseEnd_4672074 := by
    simpa [prefixWord, tailWord_4672074, baseEnd_4672074] using wordTrace_append hprefix tailTrace_4672074
  have hstable : (prefixWord ++ tailWord_4672074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672074).length < 2 ^ (prefixWord ++ tailWord_4672074).sum := by decide
  have hdescent : baseEnd_4672074 < baseStart_4672074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672080 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 3]
def baseStart_4672080 : Nat := 118140960795 + 4672080 * 2 ^ 59
def prefixEnd_4672080 : Nat := 4983230072969 + 3 ^ 40 * 4672080 * 2
def baseEnd_4672080 : Nat := 2399022696258185699213501

theorem tailTrace_4672080 : CollatzResearch.WordTrace tailWord_4672080 prefixEnd_4672080 2399022696258185699213501 := by
  unfold tailWord_4672080
  simp only [CollatzResearch.WordTrace]
  refine ⟨85202378456929781291418847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113603171275906375055225129 85202378456929781291418847)
  ·
    refine ⟨127803567685394671937128271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85202378456929781291418847 127803567685394671937128271)
    ·
      refine ⟨191705351528092007905692407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127803567685394671937128271 191705351528092007905692407)
      ·
        refine ⟨287558027292138011858538611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191705351528092007905692407 287558027292138011858538611)
        ·
          refine ⟨431337040938207017787807917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287558027292138011858538611 431337040938207017787807917)
          ·
            refine ⟨161751390351827631670427969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 431337040938207017787807917 161751390351827631670427969)
            ·
              refine ⟨121313542763870723752820977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161751390351827631670427969 121313542763870723752820977)
              ·
                refine ⟨90985157072903042814615733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121313542763870723752820977 90985157072903042814615733)
                ·
                  refine ⟨8529858475584660263870225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90985157072903042814615733 8529858475584660263870225)
                  ·
                    refine ⟨6397393856688495197902669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8529858475584660263870225 6397393856688495197902669)
                    ·
                      refine ⟨2399022696258185699213501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6397393856688495197902669 2399022696258185699213501)
                      ·
                        rfl

theorem cell23_4672080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 3].length) (baseStart_4672080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672080 prefixEnd_4672080 := by exact prefixLift 4672080
  have htrace : WordTrace (prefixWord ++ tailWord_4672080) baseStart_4672080 baseEnd_4672080 := by
    simpa [prefixWord, tailWord_4672080, baseEnd_4672080] using wordTrace_append hprefix tailTrace_4672080
  have hstable : (prefixWord ++ tailWord_4672080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672080).length < 2 ^ (prefixWord ++ tailWord_4672080).sum := by decide
  have hdescent : baseEnd_4672080 < baseStart_4672080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672104 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 1, 6]
def baseStart_4672104 : Nat := 118140960795 + 4672104 * 2 ^ 59
def prefixEnd_4672104 : Nat := 4983230072969 + 3 ^ 40 * 4672104 * 2
def baseEnd_4672104 : Nat := 799678339931297868437797

theorem tailTrace_4672104 : CollatzResearch.WordTrace tailWord_4672104 prefixEnd_4672104 799678339931297868437797 := by
  unfold tailWord_4672104
  simp only [CollatzResearch.WordTrace]
  refine ⟨85202816132886307340855683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113603754843848409787807577 85202816132886307340855683)
  ·
    refine ⟨127804224199329461011283525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85202816132886307340855683 127804224199329461011283525)
    ·
      refine ⟨23963292037374273939615661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127804224199329461011283525 23963292037374273939615661)
      ·
        refine ⟨8986234514015352727355873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23963292037374273939615661 8986234514015352727355873)
        ·
          refine ⟨6739675885511514545516905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8986234514015352727355873 6739675885511514545516905)
          ·
            refine ⟨5054756914133635909137679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6739675885511514545516905 5054756914133635909137679)
            ·
              refine ⟨7582135371200453863706519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054756914133635909137679 7582135371200453863706519)
              ·
                refine ⟨11373203056800680795559779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7582135371200453863706519 11373203056800680795559779)
                ·
                  refine ⟨17059804585201021193339669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11373203056800680795559779 17059804585201021193339669)
                  ·
                    refine ⟨799678339931297868437797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17059804585201021193339669 799678339931297868437797)
                    ·
                      rfl

theorem cell23_4672104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_4672104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672104 prefixEnd_4672104 := by exact prefixLift 4672104
  have htrace : WordTrace (prefixWord ++ tailWord_4672104) baseStart_4672104 baseEnd_4672104 := by
    simpa [prefixWord, tailWord_4672104, baseEnd_4672104] using wordTrace_append hprefix tailTrace_4672104
  have hstable : (prefixWord ++ tailWord_4672104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672104).length < 2 ^ (prefixWord ++ tailWord_4672104).sum := by decide
  have hdescent : baseEnd_4672104 < baseStart_4672104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672117 : List Nat := [1, 3, 4, 2, 2, 1, 1, 9]
def baseStart_4672117 : Nat := 118140960795 + 4672117 * 2 ^ 59
def prefixEnd_4672117 : Nat := 4983230072969 + 3 ^ 40 * 4672117 * 2
def baseEnd_4672117 : Nat := 88853396112681557572253

theorem tailTrace_4672117 : CollatzResearch.WordTrace tailWord_4672117 prefixEnd_4672117 88853396112681557572253 := by
  unfold tailWord_4672117
  simp only [CollatzResearch.WordTrace]
  refine ⟨170406106414725517901934605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113604070943150345267956403 170406106414725517901934605)
  ·
    refine ⟨63902289905522069213225477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170406106414725517901934605 63902289905522069213225477)
    ·
      refine ⟨11981679357285387977479777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63902289905522069213225477 11981679357285387977479777)
      ·
        refine ⟨8986259517964040983109833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11981679357285387977479777 8986259517964040983109833)
        ·
          refine ⟨6739694638473030737332375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8986259517964040983109833 6739694638473030737332375)
          ·
            refine ⟨10109541957709546105998563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6739694638473030737332375 10109541957709546105998563)
            ·
              refine ⟨15164312936564319158997845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10109541957709546105998563 15164312936564319158997845)
              ·
                refine ⟨88853396112681557572253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15164312936564319158997845 88853396112681557572253)
                ·
                  rfl

theorem cell23_4672117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 9].length) (baseStart_4672117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672117 prefixEnd_4672117 := by exact prefixLift 4672117
  have htrace : WordTrace (prefixWord ++ tailWord_4672117) baseStart_4672117 baseEnd_4672117 := by
    simpa [prefixWord, tailWord_4672117, baseEnd_4672117] using wordTrace_append hprefix tailTrace_4672117
  have hstable : (prefixWord ++ tailWord_4672117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672117).length < 2 ^ (prefixWord ++ tailWord_4672117).sum := by decide
  have hdescent : baseEnd_4672117 < baseStart_4672117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672128 : List Nat := [2, 1, 1, 2, 1, 7, 1, 3, 1, 2, 2]
def baseStart_4672128 : Nat := 118140960795 + 4672128 * 2 ^ 59
def prefixEnd_4672128 : Nat := 4983230072969 + 3 ^ 40 * 4672128 * 2
def baseEnd_4672128 : Nat := 2399047343329601511413281

theorem tailTrace_4672128 : CollatzResearch.WordTrace tailWord_4672128 prefixEnd_4672128 2399047343329601511413281 := by
  unfold tailWord_4672128
  simp only [CollatzResearch.WordTrace]
  refine ⟨85203253808842833390292519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113604338411790444520390025 85203253808842833390292519)
  ·
    refine ⟨127804880713264250085438779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85203253808842833390292519 127804880713264250085438779)
    ·
      refine ⟨191707321069896375128158169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127804880713264250085438779 191707321069896375128158169)
      ·
        refine ⟨143780490802422281346118627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191707321069896375128158169 143780490802422281346118627)
        ·
          refine ⟨215670736203633422019177941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143780490802422281346118627 215670736203633422019177941)
          ·
            refine ⟨5054782879772658328574483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 215670736203633422019177941 5054782879772658328574483)
            ·
              refine ⟨7582174319658987492861725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054782879772658328574483 7582174319658987492861725)
              ·
                refine ⟨2843315369872120309823147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7582174319658987492861725 2843315369872120309823147)
                ·
                  refine ⟨4264973054808180464734721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2843315369872120309823147 4264973054808180464734721)
                  ·
                    refine ⟨3198729791106135348551041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4264973054808180464734721 3198729791106135348551041)
                    ·
                      refine ⟨2399047343329601511413281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198729791106135348551041 2399047343329601511413281)
                      ·
                        rfl

theorem cell23_4672128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 1, 2, 2].length) (baseStart_4672128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672128 prefixEnd_4672128 := by exact prefixLift 4672128
  have htrace : WordTrace (prefixWord ++ tailWord_4672128) baseStart_4672128 baseEnd_4672128 := by
    simpa [prefixWord, tailWord_4672128, baseEnd_4672128] using wordTrace_append hprefix tailTrace_4672128
  have hstable : (prefixWord ++ tailWord_4672128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672128).length < 2 ^ (prefixWord ++ tailWord_4672128).sum := by decide
  have hdescent : baseEnd_4672128 < baseStart_4672128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672137 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 5, 3, 2]
def baseStart_4672137 : Nat := 118140960795 + 4672137 * 2 ^ 59
def prefixEnd_4672137 : Nat := 4983230072969 + 3 ^ 40 * 4672137 * 2
def baseEnd_4672137 : Nat := 2399051964655491976200739

theorem tailTrace_4672137 : CollatzResearch.WordTrace tailWord_4672137 prefixEnd_4672137 2399051964655491976200739 := by
  unfold tailWord_4672137
  simp only [CollatzResearch.WordTrace]
  refine ⟨170406835874653061317662665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113604557249768707545108443 170406835874653061317662665)
  ·
    refine ⟨127805126905989795988246999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170406835874653061317662665 127805126905989795988246999)
    ·
      refine ⟨191707690358984693982370499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127805126905989795988246999 191707690358984693982370499)
      ·
        refine ⟨287561535538477040973555749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191707690358984693982370499 287561535538477040973555749)
        ·
          refine ⟨53917787913464445182541703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 287561535538477040973555749 53917787913464445182541703)
          ·
            refine ⟨80876681870196667773812555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53917787913464445182541703 80876681870196667773812555)
            ·
              refine ⟨121315022805295001660718833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80876681870196667773812555 121315022805295001660718833)
              ·
                refine ⟨90986267103971251245539125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121315022805295001660718833 90986267103971251245539125)
                ·
                  refine ⟨8529962540997304804269293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90986267103971251245539125 8529962540997304804269293)
                  ·
                    refine ⟨3198735952873989301600985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8529962540997304804269293 3198735952873989301600985)
                    ·
                      refine ⟨2399051964655491976200739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198735952873989301600985 2399051964655491976200739)
                      ·
                        rfl

theorem cell23_4672137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 3, 2].length) (baseStart_4672137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672137 prefixEnd_4672137 := by exact prefixLift 4672137
  have htrace : WordTrace (prefixWord ++ tailWord_4672137) baseStart_4672137 baseEnd_4672137 := by
    simpa [prefixWord, tailWord_4672137, baseEnd_4672137] using wordTrace_append hprefix tailTrace_4672137
  have hstable : (prefixWord ++ tailWord_4672137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672137).length < 2 ^ (prefixWord ++ tailWord_4672137).sum := by decide
  have hdescent : baseEnd_4672137 < baseStart_4672137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672161 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_4672161 : Nat := 118140960795 + 4672161 * 2 ^ 59
def prefixEnd_4672161 : Nat := 4983230072969 + 3 ^ 40 * 4672161 * 2
def baseEnd_4672161 : Nat := 2399064288191199882300629

theorem tailTrace_4672161 : CollatzResearch.WordTrace tailWord_4672161 prefixEnd_4672161 2399064288191199882300629 := by
  unfold tailWord_4672161
  simp only [CollatzResearch.WordTrace]
  refine ⟨170407711226566113416536337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113605140817710742277690891 170407711226566113416536337)
  ·
    refine ⟨127805783419924585062402253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170407711226566113416536337 127805783419924585062402253)
    ·
      refine ⟨47927168782471719398400845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127805783419924585062402253 47927168782471719398400845)
      ·
        refine ⟨17972688293426894774400317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47927168782471719398400845 17972688293426894774400317)
        ·
          refine ⟨6739758110035085540400119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17972688293426894774400317 6739758110035085540400119)
          ·
            refine ⟨10109637165052628310600179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6739758110035085540400119 10109637165052628310600179)
            ·
              refine ⟨15164455747578942465900269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10109637165052628310600179 15164455747578942465900269)
              ·
                refine ⟨5686670905342103424712601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15164455747578942465900269 5686670905342103424712601)
                ·
                  refine ⟨4265003179006577568534451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5686670905342103424712601 4265003179006577568534451)
                  ·
                    refine ⟨6397504768509866352801677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4265003179006577568534451 6397504768509866352801677)
                    ·
                      refine ⟨2399064288191199882300629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6397504768509866352801677 2399064288191199882300629)
                      ·
                        rfl

theorem cell23_4672161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_4672161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672161 prefixEnd_4672161 := by exact prefixLift 4672161
  have htrace : WordTrace (prefixWord ++ tailWord_4672161) baseStart_4672161 baseEnd_4672161 := by
    simpa [prefixWord, tailWord_4672161, baseEnd_4672161] using wordTrace_append hprefix tailTrace_4672161
  have hstable : (prefixWord ++ tailWord_4672161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672161).length < 2 ^ (prefixWord ++ tailWord_4672161).sum := by decide
  have hdescent : baseEnd_4672161 < baseStart_4672161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672217 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 2, 3, 3]
def baseStart_4672217 : Nat := 118140960795 + 4672217 * 2 ^ 59
def prefixEnd_4672217 : Nat := 4983230072969 + 3 ^ 40 * 4672217 * 2
def baseEnd_4672217 : Nat := 2399093043107851663200371

theorem tailTrace_4672217 : CollatzResearch.WordTrace tailWord_4672217 prefixEnd_4672217 2399093043107851663200371 := by
  unfold tailWord_4672217
  simp only [CollatzResearch.WordTrace]
  refine ⟨170409753714363234980574905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113606502476242156653716603 170409753714363234980574905)
  ·
    refine ⟨127807315285772426235431179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170409753714363234980574905 127807315285772426235431179)
    ·
      refine ⟨191710972928658639353146769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127807315285772426235431179 191710972928658639353146769)
      ·
        refine ⟨143783229696493979514860077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191710972928658639353146769 143783229696493979514860077)
        ·
          refine ⟨53918711136185242318072529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143783229696493979514860077 53918711136185242318072529)
          ·
            refine ⟨40439033352138931738554397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53918711136185242318072529 40439033352138931738554397)
            ·
              refine ⟨15164637507052099401957899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40439033352138931738554397 15164637507052099401957899)
              ·
                refine ⟨22746956260578149102936849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15164637507052099401957899 22746956260578149102936849)
                ·
                  refine ⟨17060217195433611827202637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22746956260578149102936849 17060217195433611827202637)
                  ·
                    refine ⟨6397581448287604435200989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17060217195433611827202637 6397581448287604435200989)
                    ·
                      refine ⟨2399093043107851663200371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6397581448287604435200989 2399093043107851663200371)
                      ·
                        rfl

theorem cell23_4672217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_4672217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672217 prefixEnd_4672217 := by exact prefixLift 4672217
  have htrace : WordTrace (prefixWord ++ tailWord_4672217) baseStart_4672217 baseEnd_4672217 := by
    simpa [prefixWord, tailWord_4672217, baseEnd_4672217] using wordTrace_append hprefix tailTrace_4672217
  have hstable : (prefixWord ++ tailWord_4672217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672217).length < 2 ^ (prefixWord ++ tailWord_4672217).sum := by decide
  have hdescent : baseEnd_4672217 < baseStart_4672217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672237 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_4672237 : Nat := 118140960795 + 4672237 * 2 ^ 59
def prefixEnd_4672237 : Nat := 4983230072969 + 3 ^ 40 * 4672237 * 2
def baseEnd_4672237 : Nat := 799701104240313861650093

theorem tailTrace_4672237 : CollatzResearch.WordTrace tailWord_4672237 prefixEnd_4672237 799701104240313861650093 := by
  unfold tailWord_4672237
  simp only [CollatzResearch.WordTrace]
  refine ⟨170410483174290778396302965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113606988782860518930868643 170410483174290778396302965)
  ·
    refine ⟨15975982797589760474653403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170410483174290778396302965 15975982797589760474653403)
    ·
      refine ⟨23963974196384640711980105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15975982797589760474653403 23963974196384640711980105)
      ·
        refine ⟨17972980647288480533985079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23963974196384640711980105 17972980647288480533985079)
        ·
          refine ⟨26959470970932720800977619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17972980647288480533985079 26959470970932720800977619)
          ·
            refine ⟨40439206456399081201466429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26959470970932720800977619 40439206456399081201466429)
            ·
              refine ⟨15164702421149655450549911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40439206456399081201466429 15164702421149655450549911)
              ·
                refine ⟨22747053631724483175824867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15164702421149655450549911 22747053631724483175824867)
                ·
                  refine ⟨34120580447586724763737301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22747053631724483175824867 34120580447586724763737301)
                  ·
                    refine ⟨799701104240313861650093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34120580447586724763737301 799701104240313861650093)
                    ·
                      rfl

theorem cell23_4672237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_4672237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672237 prefixEnd_4672237 := by exact prefixLift 4672237
  have htrace : WordTrace (prefixWord ++ tailWord_4672237) baseStart_4672237 baseEnd_4672237 := by
    simpa [prefixWord, tailWord_4672237, baseEnd_4672237] using wordTrace_append hprefix tailTrace_4672237
  have hstable : (prefixWord ++ tailWord_4672237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672237).length < 2 ^ (prefixWord ++ tailWord_4672237).sum := by decide
  have hdescent : baseEnd_4672237 < baseStart_4672237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672257 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_4672257 : Nat := 118140960795 + 4672257 * 2 ^ 59
def prefixEnd_4672257 : Nat := 4983230072969 + 3 ^ 40 * 4672257 * 2
def baseEnd_4672257 : Nat := 2399113582334031506700187

theorem tailTrace_4672257 : CollatzResearch.WordTrace tailWord_4672257 prefixEnd_4672257 2399113582334031506700187 := by
  unfold tailWord_4672257
  simp only [CollatzResearch.WordTrace]
  refine ⟨170411212634218321812031025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113607475089478881208020683 170411212634218321812031025)
  ·
    refine ⟨127808409475663741359023269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170411212634218321812031025 127808409475663741359023269)
    ·
      refine ⟨23964076776686951504816863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127808409475663741359023269 23964076776686951504816863)
      ·
        refine ⟨35946115165030427257225295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23964076776686951504816863 35946115165030427257225295)
        ·
          refine ⟨53919172747545640885837943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35946115165030427257225295 53919172747545640885837943)
          ·
            refine ⟨80878759121318461328756915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53919172747545640885837943 80878759121318461328756915)
            ·
              refine ⟨121318138681977691993135373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80878759121318461328756915 121318138681977691993135373)
              ·
                refine ⟨45494302005741634497425765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121318138681977691993135373 45494302005741634497425765)
                ·
                  refine ⟨8530181626076556468267331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45494302005741634497425765 8530181626076556468267331)
                  ·
                    refine ⟨12795272439114834702400997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8530181626076556468267331 12795272439114834702400997)
                    ·
                      refine ⟨2399113582334031506700187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12795272439114834702400997 2399113582334031506700187)
                      ·
                        rfl

theorem cell23_4672257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_4672257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672257 prefixEnd_4672257 := by exact prefixLift 4672257
  have htrace : WordTrace (prefixWord ++ tailWord_4672257) baseStart_4672257 baseEnd_4672257 := by
    simpa [prefixWord, tailWord_4672257, baseEnd_4672257] using wordTrace_append hprefix tailTrace_4672257
  have hstable : (prefixWord ++ tailWord_4672257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672257).length < 2 ^ (prefixWord ++ tailWord_4672257).sum := by decide
  have hdescent : baseEnd_4672257 < baseStart_4672257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672277 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_4672277 : Nat := 118140960795 + 4672277 * 2 ^ 59
def prefixEnd_4672277 : Nat := 4983230072969 + 3 ^ 40 * 4672277 * 2
def baseEnd_4672277 : Nat := 2399123851947121428450095

theorem tailTrace_4672277 : CollatzResearch.WordTrace tailWord_4672277 prefixEnd_4672277 2399123851947121428450095 := by
  unfold tailWord_4672277
  simp only [CollatzResearch.WordTrace]
  refine ⟨170411942094145865227759085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113607961396097243485172723 170411942094145865227759085)
  ·
    refine ⟨63904478285304699460409657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170411942094145865227759085 63904478285304699460409657)
    ·
      refine ⟨47928358713978524595307243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63904478285304699460409657 47928358713978524595307243)
      ·
        refine ⟨71892538070967786892960865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47928358713978524595307243 71892538070967786892960865)
        ·
          refine ⟨53919403553225840169720649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71892538070967786892960865 53919403553225840169720649)
          ·
            refine ⟨40439552664919380127290487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53919403553225840169720649 40439552664919380127290487)
            ·
              refine ⟨60659328997379070190935731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40439552664919380127290487 60659328997379070190935731)
              ·
                refine ⟨90988993496068605286403597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60659328997379070190935731 90988993496068605286403597)
                ·
                  refine ⟨34120872561025726982401349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90988993496068605286403597 34120872561025726982401349)
                  ·
                    refine ⟨6397663605192323809200253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34120872561025726982401349 6397663605192323809200253)
                    ·
                      refine ⟨2399123851947121428450095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6397663605192323809200253 2399123851947121428450095)
                      ·
                        rfl

theorem cell23_4672277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_4672277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672277 prefixEnd_4672277 := by exact prefixLift 4672277
  have htrace : WordTrace (prefixWord ++ tailWord_4672277) baseStart_4672277 baseEnd_4672277 := by
    simpa [prefixWord, tailWord_4672277, baseEnd_4672277] using wordTrace_append hprefix tailTrace_4672277
  have hstable : (prefixWord ++ tailWord_4672277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672277).length < 2 ^ (prefixWord ++ tailWord_4672277).sum := by decide
  have hdescent : baseEnd_4672277 < baseStart_4672277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672284 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 3, 4]
def baseStart_4672284 : Nat := 118140960795 + 4672284 * 2 ^ 59
def prefixEnd_4672284 : Nat := 4983230072969 + 3 ^ 40 * 4672284 * 2
def baseEnd_4672284 : Nat := 799709148770567633687521

theorem tailTrace_4672284 : CollatzResearch.WordTrace tailWord_4672284 prefixEnd_4672284 799709148770567633687521 := by
  unfold tailWord_4672284
  simp only [CollatzResearch.WordTrace]
  refine ⟨85206098702560252711631953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113608131603413670282175937 85206098702560252711631953)
  ·
    refine ⟨63904574026920189533723965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85206098702560252711631953 63904574026920189533723965)
    ·
      refine ⟨23964215260095071075146487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63904574026920189533723965 23964215260095071075146487)
      ·
        refine ⟨35946322890142606612719731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23964215260095071075146487 35946322890142606612719731)
        ·
          refine ⟨53919484335213909919079597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35946322890142606612719731 53919484335213909919079597)
          ·
            refine ⟨20219806625705216219654849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53919484335213909919079597 20219806625705216219654849)
            ·
              refine ⟨15164854969278912164741137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20219806625705216219654849 15164854969278912164741137)
              ·
                refine ⟨11373641226959184123555853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15164854969278912164741137 11373641226959184123555853)
                ·
                  refine ⟨4265115460109694046333445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11373641226959184123555853 4265115460109694046333445)
                  ·
                    refine ⟨799709148770567633687521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4265115460109694046333445 799709148770567633687521)
                    ·
                      rfl

theorem cell23_4672284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_4672284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672284 prefixEnd_4672284 := by exact prefixLift 4672284
  have htrace : WordTrace (prefixWord ++ tailWord_4672284) baseStart_4672284 baseEnd_4672284 := by
    simpa [prefixWord, tailWord_4672284, baseEnd_4672284] using wordTrace_append hprefix tailTrace_4672284
  have hstable : (prefixWord ++ tailWord_4672284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672284).length < 2 ^ (prefixWord ++ tailWord_4672284).sum := by decide
  have hdescent : baseEnd_4672284 < baseStart_4672284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672318 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_4672318 : Nat := 118140960795 + 4672318 * 2 ^ 59
def prefixEnd_4672318 : Nat := 4983230072969 + 3 ^ 40 * 4672318 * 2
def baseEnd_4672318 : Nat := 799714968217985256012469

theorem tailTrace_4672318 : CollatzResearch.WordTrace tailWord_4672318 prefixEnd_4672318 799714968217985256012469 := by
  unfold tailWord_4672318
  simp only [CollatzResearch.WordTrace]
  refine ⟨21301679685874666153750201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113608958324664886153334405 21301679685874666153750201)
  ·
    refine ⟨15976259764405999615312651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21301679685874666153750201 15976259764405999615312651)
    ·
      refine ⟨23964389646608999422968977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15976259764405999615312651 23964389646608999422968977)
      ·
        refine ⟨17973292234956749567226733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23964389646608999422968977 17973292234956749567226733)
        ·
          refine ⟨6739984588108781087710025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17973292234956749567226733 6739984588108781087710025)
          ·
            refine ⟨5054988441081585815782519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6739984588108781087710025 5054988441081585815782519)
            ·
              refine ⟨7582482661622378723673779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5054988441081585815782519 7582482661622378723673779)
              ·
                refine ⟨11373723992433568085510669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7582482661622378723673779 11373723992433568085510669)
                ·
                  refine ⟨4265146497162588032066501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11373723992433568085510669 4265146497162588032066501)
                  ·
                    refine ⟨799714968217985256012469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4265146497162588032066501 799714968217985256012469)
                    ·
                      rfl

theorem cell23_4672318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_4672318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672318 prefixEnd_4672318 := by exact prefixLift 4672318
  have htrace : WordTrace (prefixWord ++ tailWord_4672318) baseStart_4672318 baseEnd_4672318 := by
    simpa [prefixWord, tailWord_4672318, baseEnd_4672318] using wordTrace_append hprefix tailTrace_4672318
  have hstable : (prefixWord ++ tailWord_4672318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672318).length < 2 ^ (prefixWord ++ tailWord_4672318).sum := by decide
  have hdescent : baseEnd_4672318 < baseStart_4672318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672327 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 3, 5]
def baseStart_4672327 : Nat := 118140960795 + 4672327 * 2 ^ 59
def prefixEnd_4672327 : Nat := 4983230072969 + 3 ^ 40 * 4672327 * 2
def baseEnd_4672327 : Nat := 799716508659948744274955

theorem tailTrace_4672327 : CollatzResearch.WordTrace tailWord_4672327 prefixEnd_4672327 799716508659948744274955 := by
  unfold tailWord_4672327
  simp only [CollatzResearch.WordTrace]
  refine ⟨170413765743964723767079235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113609177162643149178052823 170413765743964723767079235)
  ·
    refine ⟨255620648615947085650618853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170413765743964723767079235 255620648615947085650618853)
    ·
      refine ⟨47928871615490078559491035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255620648615947085650618853 47928871615490078559491035)
      ·
        refine ⟨71893307423235117839236553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47928871615490078559491035 71893307423235117839236553)
        ·
          refine ⟨53919980567426338379427415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71893307423235117839236553 53919980567426338379427415)
          ·
            refine ⟨80879970851139507569141123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53919980567426338379427415 80879970851139507569141123)
            ·
              refine ⟨121319956276709261353711685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80879970851139507569141123 121319956276709261353711685)
              ·
                refine ⟨22747491801882986503820941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121319956276709261353711685 22747491801882986503820941)
                ·
                  refine ⟨8530309425706119938932853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22747491801882986503820941 8530309425706119938932853)
                  ·
                    refine ⟨799716508659948744274955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8530309425706119938932853 799716508659948744274955)
                    ·
                      rfl

theorem cell23_4672327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_4672327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672327 prefixEnd_4672327 := by exact prefixLift 4672327
  have htrace : WordTrace (prefixWord ++ tailWord_4672327) baseStart_4672327 baseEnd_4672327 := by
    simpa [prefixWord, tailWord_4672327, baseEnd_4672327] using wordTrace_append hprefix tailTrace_4672327
  have hstable : (prefixWord ++ tailWord_4672327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672327).length < 2 ^ (prefixWord ++ tailWord_4672327).sum := by decide
  have hdescent : baseEnd_4672327 < baseStart_4672327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672334 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2]
def baseStart_4672334 : Nat := 118140960795 + 4672334 * 2 ^ 59
def prefixEnd_4672334 : Nat := 4983230072969 + 3 ^ 40 * 4672334 * 2
def baseEnd_4672334 : Nat := 2399153120344427705437333

theorem tailTrace_4672334 : CollatzResearch.WordTrace tailWord_4672334 prefixEnd_4672334 2399153120344427705437333 := by
  unfold tailWord_4672334
  simp only [CollatzResearch.WordTrace]
  refine ⟨21301752631867420495323007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113609347369959575975056037 21301752631867420495323007)
  ·
    refine ⟨31952628947801130742984511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21301752631867420495323007 31952628947801130742984511)
    ·
      refine ⟨47928943421701696114476767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31952628947801130742984511 47928943421701696114476767)
      ·
        refine ⟨71893415132552544171715151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47928943421701696114476767 71893415132552544171715151)
        ·
          refine ⟨107840122698828816257572727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71893415132552544171715151 107840122698828816257572727)
          ·
            refine ⟨161760184048243224386359091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107840122698828816257572727 161760184048243224386359091)
            ·
              refine ⟨242640276072364836579538637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161760184048243224386359091 242640276072364836579538637)
              ·
                refine ⟨90990103527136813717326989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242640276072364836579538637 90990103527136813717326989)
                ·
                  refine ⟨34121288822676305143997621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90990103527136813717326989 34121288822676305143997621)
                  ·
                    refine ⟨3198870827125903607249777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34121288822676305143997621 3198870827125903607249777)
                    ·
                      refine ⟨2399153120344427705437333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198870827125903607249777 2399153120344427705437333)
                      ·
                        rfl

theorem cell23_4672334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_4672334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672334 prefixEnd_4672334 := by exact prefixLift 4672334
  have htrace : WordTrace (prefixWord ++ tailWord_4672334) baseStart_4672334 baseEnd_4672334 := by
    simpa [prefixWord, tailWord_4672334, baseEnd_4672334] using wordTrace_append hprefix tailTrace_4672334
  have hstable : (prefixWord ++ tailWord_4672334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672334).length < 2 ^ (prefixWord ++ tailWord_4672334).sum := by decide
  have hdescent : baseEnd_4672334 < baseStart_4672334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672351 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 2, 3, 2]
def baseStart_4672351 : Nat := 118140960795 + 4672351 * 2 ^ 59
def prefixEnd_4672351 : Nat := 4983230072969 + 3 ^ 40 * 4672351 * 2
def baseEnd_4672351 : Nat := 2399161849515554138924755

theorem tailTrace_4672351 : CollatzResearch.WordTrace tailWord_4672351 prefixEnd_4672351 2399161849515554138924755 := by
  unfold tailWord_4672351
  simp only [CollatzResearch.WordTrace]
  refine ⟨170414641095877775865952907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113609760730585183910635271 170414641095877775865952907)
  ·
    refine ⟨255621961643816663798929361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170414641095877775865952907 255621961643816663798929361)
    ·
      refine ⟨191716471232862497849197021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255621961643816663798929361 191716471232862497849197021)
      ·
        refine ⟨71893676712323436693448883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191716471232862497849197021 71893676712323436693448883)
        ·
          refine ⟨107840515068485155040173325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71893676712323436693448883 107840515068485155040173325)
          ·
            refine ⟨40440193150681933140064997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107840515068485155040173325 40440193150681933140064997)
            ·
              refine ⟨7582536215752862463762187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40440193150681933140064997 7582536215752862463762187)
              ·
                refine ⟨11373804323629293695643281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7582536215752862463762187 11373804323629293695643281)
                ·
                  refine ⟨8530353242721970271732461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11373804323629293695643281 8530353242721970271732461)
                  ·
                    refine ⟨3198882466020738851899673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8530353242721970271732461 3198882466020738851899673)
                    ·
                      refine ⟨2399161849515554138924755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198882466020738851899673 2399161849515554138924755)
                      ·
                        rfl

theorem cell23_4672351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_4672351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672351 prefixEnd_4672351 := by exact prefixLift 4672351
  have htrace : WordTrace (prefixWord ++ tailWord_4672351) baseStart_4672351 baseEnd_4672351 := by
    simpa [prefixWord, tailWord_4672351, baseEnd_4672351] using wordTrace_append hprefix tailTrace_4672351
  have hstable : (prefixWord ++ tailWord_4672351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672351).length < 2 ^ (prefixWord ++ tailWord_4672351).sum := by decide
  have hdescent : baseEnd_4672351 < baseStart_4672351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672357 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_4672357 : Nat := 118140960795 + 4672357 * 2 ^ 59
def prefixEnd_4672357 : Nat := 4983230072969 + 3 ^ 40 * 4672357 * 2
def baseEnd_4672357 : Nat := 799721643466493705149909

theorem tailTrace_4672357 : CollatzResearch.WordTrace tailWord_4672357 prefixEnd_4672357 799721643466493705149909 := by
  unfold tailWord_4672357
  simp only [CollatzResearch.WordTrace]
  refine ⟨170414859933856038890671325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113609906622570692593780883 170414859933856038890671325)
  ·
    refine ⟨63905572475196014584001747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170414859933856038890671325 63905572475196014584001747)
    ·
      refine ⟨95858358712794021876002621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63905572475196014584001747 95858358712794021876002621)
      ·
        refine ⟨35946884517297758203500983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95858358712794021876002621 35946884517297758203500983)
        ·
          refine ⟨53920326775946637305251475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35946884517297758203500983 53920326775946637305251475)
          ·
            refine ⟨80880490163919955957877213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53920326775946637305251475 80880490163919955957877213)
            ·
              refine ⟨30330183811469983484203955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80880490163919955957877213 30330183811469983484203955)
              ·
                refine ⟨45495275717204975226305933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30330183811469983484203955 45495275717204975226305933)
                ·
                  refine ⟨17060728393951865709864725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45495275717204975226305933 17060728393951865709864725)
                  ·
                    refine ⟨799721643466493705149909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17060728393951865709864725 799721643466493705149909)
                    ·
                      rfl

theorem cell23_4672357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_4672357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672357 prefixEnd_4672357 := by exact prefixLift 4672357
  have htrace : WordTrace (prefixWord ++ tailWord_4672357) baseStart_4672357 baseEnd_4672357 := by
    simpa [prefixWord, tailWord_4672357, baseEnd_4672357] using wordTrace_append hprefix tailTrace_4672357
  have hstable : (prefixWord ++ tailWord_4672357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672357).length < 2 ^ (prefixWord ++ tailWord_4672357).sum := by decide
  have hdescent : baseEnd_4672357 < baseStart_4672357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672391 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 2, 4]
def baseStart_4672391 : Nat := 118140960795 + 4672391 * 2 ^ 59
def prefixEnd_4672391 : Nat := 4983230072969 + 3 ^ 40 * 4672391 * 2
def baseEnd_4672391 : Nat := 799727462913911327474857

theorem tailTrace_4672391 : CollatzResearch.WordTrace tailWord_4672391 prefixEnd_4672391 799727462913911327474857 := by
  unfold tailWord_4672391
  simp only [CollatzResearch.WordTrace]
  refine ⟨170416100015732862697409027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113610733343821908464939351 170416100015732862697409027)
  ·
    refine ⟨255624150023599294046113541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170416100015732862697409027 255624150023599294046113541)
    ·
      refine ⟨47929528129424867633646289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255624150023599294046113541 47929528129424867633646289)
      ·
        refine ⟨35947146097068650725234717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47929528129424867633646289 35947146097068650725234717)
        ·
          refine ⟨13480179786400744021963019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35947146097068650725234717 13480179786400744021963019)
          ·
            refine ⟨20220269679601116032944529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13480179786400744021963019 20220269679601116032944529)
            ·
              refine ⟨15165202259700837024708397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20220269679601116032944529 15165202259700837024708397)
              ·
                refine ⟨5686950847387813884265649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15165202259700837024708397 5686950847387813884265649)
                ·
                  refine ⟨4265213135540860413199237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5686950847387813884265649 4265213135540860413199237)
                  ·
                    refine ⟨799727462913911327474857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4265213135540860413199237 799727462913911327474857)
                    ·
                      rfl

theorem cell23_4672391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_4672391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672391 prefixEnd_4672391 := by exact prefixLift 4672391
  have htrace : WordTrace (prefixWord ++ tailWord_4672391) baseStart_4672391 baseEnd_4672391 := by
    simpa [prefixWord, tailWord_4672391, baseEnd_4672391] using wordTrace_append hprefix tailTrace_4672391
  have hstable : (prefixWord ++ tailWord_4672391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672391).length < 2 ^ (prefixWord ++ tailWord_4672391).sum := by decide
  have hdescent : baseEnd_4672391 < baseStart_4672391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672402 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_4672402 : Nat := 118140960795 + 4672402 * 2 ^ 59
def prefixEnd_4672402 : Nat := 4983230072969 + 3 ^ 40 * 4672402 * 2
def baseEnd_4672402 : Nat := 2399188037028933439387021

theorem tailTrace_4672402 : CollatzResearch.WordTrace tailWord_4672402 prefixEnd_4672402 2399188037028933439387021 := by
  unfold tailWord_4672402
  simp only [CollatzResearch.WordTrace]
  refine ⟨42604125304673252894014865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113611000812462007717372973 42604125304673252894014865)
  ·
    refine ⟨31953093978504939670511149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42604125304673252894014865 31953093978504939670511149)
    ·
      refine ⟨11982410241939352376441681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31953093978504939670511149 11982410241939352376441681)
      ·
        refine ⟨8986807681454514282331261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11982410241939352376441681 8986807681454514282331261)
        ·
          refine ⟨3370052880545442855874223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8986807681454514282331261 3370052880545442855874223)
          ·
            refine ⟨5055079320818164283811335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3370052880545442855874223 5055079320818164283811335)
            ·
              refine ⟨7582618981227246425717003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5055079320818164283811335 7582618981227246425717003)
              ·
                refine ⟨11373928471840869638575505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7582618981227246425717003 11373928471840869638575505)
                ·
                  refine ⟨8530446353880652228931629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11373928471840869638575505 8530446353880652228931629)
                  ·
                    refine ⟨3198917382705244585849361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8530446353880652228931629 3198917382705244585849361)
                    ·
                      refine ⟨2399188037028933439387021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198917382705244585849361 2399188037028933439387021)
                      ·
                        rfl

theorem cell23_4672402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_4672402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672402 prefixEnd_4672402 := by exact prefixLift 4672402
  have htrace : WordTrace (prefixWord ++ tailWord_4672402) baseStart_4672402 baseEnd_4672402 := by
    simpa [prefixWord, tailWord_4672402, baseEnd_4672402] using wordTrace_append hprefix tailTrace_4672402
  have hstable : (prefixWord ++ tailWord_4672402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672402).length < 2 ^ (prefixWord ++ tailWord_4672402).sum := by decide
  have hdescent : baseEnd_4672402 < baseStart_4672402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672415 : List Nat := [1, 1, 2, 5, 2, 1, 1, 5, 1, 2, 2]
def baseStart_4672415 : Nat := 118140960795 + 4672415 * 2 ^ 59
def prefixEnd_4672415 : Nat := 4983230072969 + 3 ^ 40 * 4672415 * 2
def baseEnd_4672415 : Nat := 2399194712277441888524461

theorem tailTrace_4672415 : CollatzResearch.WordTrace tailWord_4672415 prefixEnd_4672415 2399194712277441888524461 := by
  unfold tailWord_4672415
  simp only [CollatzResearch.WordTrace]
  refine ⟨170416975367645914796282699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113611316911763943197521799 170416975367645914796282699)
  ·
    refine ⟨255625463051468872194424049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170416975367645914796282699 255625463051468872194424049)
    ·
      refine ⟨191719097288601654145818037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255625463051468872194424049 191719097288601654145818037)
      ·
        refine ⟨17973665370806405076170441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191719097288601654145818037 17973665370806405076170441)
        ·
          refine ⟨13480249028104803807127831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17973665370806405076170441 13480249028104803807127831)
          ·
            refine ⟨20220373542157205710691747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13480249028104803807127831 20220373542157205710691747)
            ·
              refine ⟨30330560313235808566037621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20220373542157205710691747 30330560313235808566037621)
              ·
                refine ⟨2843490029365857053066027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30330560313235808566037621 2843490029365857053066027)
                ·
                  refine ⟨4265235044048785579599041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2843490029365857053066027 4265235044048785579599041)
                  ·
                    refine ⟨3198926283036589184699281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4265235044048785579599041 3198926283036589184699281)
                    ·
                      refine ⟨2399194712277441888524461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198926283036589184699281 2399194712277441888524461)
                      ·
                        rfl

theorem cell23_4672415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_4672415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672415 prefixEnd_4672415 := by exact prefixLift 4672415
  have htrace : WordTrace (prefixWord ++ tailWord_4672415) baseStart_4672415 baseEnd_4672415 := by
    simpa [prefixWord, tailWord_4672415, baseEnd_4672415] using wordTrace_append hprefix tailTrace_4672415
  have hstable : (prefixWord ++ tailWord_4672415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672415).length < 2 ^ (prefixWord ++ tailWord_4672415).sum := by decide
  have hdescent : baseEnd_4672415 < baseStart_4672415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672418 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_4672418 : Nat := 118140960795 + 4672418 * 2 ^ 59
def prefixEnd_4672418 : Nat := 4983230072969 + 3 ^ 40 * 4672418 * 2
def baseEnd_4672418 : Nat := 2399196252719405376786947

theorem tailTrace_4672418 : CollatzResearch.WordTrace tailWord_4672418 prefixEnd_4672418 2399196252719405376786947 := by
  unfold tailWord_4672418
  simp only [CollatzResearch.WordTrace]
  refine ⟨42604271196658761577160477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113611389857756697539094605 42604271196658761577160477)
  ·
    refine ⟨15976601698747035591435179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42604271196658761577160477 15976601698747035591435179)
    ·
      refine ⟨23964902548120553387152769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15976601698747035591435179 23964902548120553387152769)
      ·
        refine ⟨17973676911090415040364577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23964902548120553387152769 17973676911090415040364577)
        ·
          refine ⟨13480257683317811280273433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17973676911090415040364577 13480257683317811280273433)
          ·
            refine ⟨10110193262488358460205075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13480257683317811280273433 10110193262488358460205075)
            ·
              refine ⟨15165289893732537690307613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10110193262488358460205075 15165289893732537690307613)
              ·
                refine ⟨5686983710149701633865355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15165289893732537690307613 5686983710149701633865355)
                ·
                  refine ⟨8530475565224552450798033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5686983710149701633865355 8530475565224552450798033)
                  ·
                    refine ⟨6397856673918414338098525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8530475565224552450798033 6397856673918414338098525)
                    ·
                      refine ⟨2399196252719405376786947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6397856673918414338098525 2399196252719405376786947)
                      ·
                        rfl

theorem cell23_4672418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_4672418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672418 prefixEnd_4672418 := by exact prefixLift 4672418
  have htrace : WordTrace (prefixWord ++ tailWord_4672418) baseStart_4672418 baseEnd_4672418 := by
    simpa [prefixWord, tailWord_4672418, baseEnd_4672418] using wordTrace_append hprefix tailTrace_4672418
  have hstable : (prefixWord ++ tailWord_4672418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672418).length < 2 ^ (prefixWord ++ tailWord_4672418).sum := by decide
  have hdescent : baseEnd_4672418 < baseStart_4672418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672427 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 5]
def baseStart_4672427 : Nat := 118140960795 + 4672427 * 2 ^ 59
def prefixEnd_4672427 : Nat := 4983230072969 + 3 ^ 40 * 4672427 * 2
def baseEnd_4672427 : Nat := 2399200874045295841574405

theorem tailTrace_4672427 : CollatzResearch.WordTrace tailWord_4672427 prefixEnd_4672427 2399200874045295841574405 := by
  unfold tailWord_4672427
  simp only [CollatzResearch.WordTrace]
  refine ⟨170417413043602440845719535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113611608695734960563813023 170417413043602440845719535)
  ·
    refine ⟨255626119565403661268579303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170417413043602440845719535 255626119565403661268579303)
    ·
      refine ⟨383439179348105491902868955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255626119565403661268579303 383439179348105491902868955)
      ·
        refine ⟨575158769022158237854303433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383439179348105491902868955 575158769022158237854303433)
        ·
          refine ⟨431369076766618678390727575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575158769022158237854303433 431369076766618678390727575)
          ·
            refine ⟨647053615149928017586091363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431369076766618678390727575 647053615149928017586091363)
            ·
              refine ⟨970580422724892026379137045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647053615149928017586091363 970580422724892026379137045)
              ·
                refine ⟨45495957315229313736522049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 970580422724892026379137045 45495957315229313736522049)
                ·
                  refine ⟨34121967986421985302391537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45495957315229313736522049 34121967986421985302391537)
                  ·
                    refine ⟨25591475989816488976793653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34121967986421985302391537 25591475989816488976793653)
                    ·
                      refine ⟨2399200874045295841574405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25591475989816488976793653 2399200874045295841574405)
                      ·
                        rfl

theorem cell23_4672427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_4672427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672427 prefixEnd_4672427 := by exact prefixLift 4672427
  have htrace : WordTrace (prefixWord ++ tailWord_4672427) baseStart_4672427 baseEnd_4672427 := by
    simpa [prefixWord, tailWord_4672427, baseEnd_4672427] using wordTrace_append hprefix tailTrace_4672427
  have hstable : (prefixWord ++ tailWord_4672427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672427).length < 2 ^ (prefixWord ++ tailWord_4672427).sum := by decide
  have hdescent : baseEnd_4672427 < baseStart_4672427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672431 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 2, 1, 3]
def baseStart_4672431 : Nat := 118140960795 + 4672431 * 2 ^ 59
def prefixEnd_4672431 : Nat := 4983230072969 + 3 ^ 40 * 4672431 * 2
def baseEnd_4672431 : Nat := 2399202927967913825924387

theorem tailTrace_4672431 : CollatzResearch.WordTrace tailWord_4672431 prefixEnd_4672431 2399202927967913825924387 := by
  unfold tailWord_4672431
  simp only [CollatzResearch.WordTrace]
  refine ⟨170417558935587949528865147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113611705957058633019243431 170417558935587949528865147)
  ·
    refine ⟨255626338403381924293297721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170417558935587949528865147 255626338403381924293297721)
    ·
      refine ⟨191719753802536443219973291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255626338403381924293297721 191719753802536443219973291)
      ·
        refine ⟨287579630703804664829959937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191719753802536443219973291 287579630703804664829959937)
        ·
          refine ⟨215684723027853498622469953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287579630703804664829959937 215684723027853498622469953)
          ·
            refine ⟨161763542270890123966852465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215684723027853498622469953 161763542270890123966852465)
            ·
              refine ⟨121322656703167592975139349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161763542270890123966852465 121322656703167592975139349)
              ·
                refine ⟨5686999532960980920709657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 121322656703167592975139349 5686999532960980920709657)
                ·
                  refine ⟨4265249649720735690532243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5686999532960980920709657 4265249649720735690532243)
                  ·
                    refine ⟨6397874474581103535798365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4265249649720735690532243 6397874474581103535798365)
                    ·
                      refine ⟨2399202927967913825924387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6397874474581103535798365 2399202927967913825924387)
                      ·
                        rfl

theorem cell23_4672431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 1, 3].length) (baseStart_4672431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672431 prefixEnd_4672431 := by exact prefixLift 4672431
  have htrace : WordTrace (prefixWord ++ tailWord_4672431) baseStart_4672431 baseEnd_4672431 := by
    simpa [prefixWord, tailWord_4672431, baseEnd_4672431] using wordTrace_append hprefix tailTrace_4672431
  have hstable : (prefixWord ++ tailWord_4672431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672431).length < 2 ^ (prefixWord ++ tailWord_4672431).sum := by decide
  have hdescent : baseEnd_4672431 < baseStart_4672431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672447 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 1, 8]
def baseStart_4672447 : Nat := 118140960795 + 4672447 * 2 ^ 59
def prefixEnd_4672447 : Nat := 4983230072969 + 3 ^ 40 * 4672447 * 2
def baseEnd_4672447 : Nat := 799737047886128587774771

theorem tailTrace_4672447 : CollatzResearch.WordTrace tailWord_4672447 prefixEnd_4672447 799737047886128587774771 := by
  unfold tailWord_4672447
  simp only [CollatzResearch.WordTrace]
  refine ⟨170418142503529984261447595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113612095002353322840965063 170418142503529984261447595)
  ·
    refine ⟨255627213755294976392171393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170418142503529984261447595 255627213755294976392171393)
    ·
      refine ⟨191720410316471232294128545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255627213755294976392171393 191720410316471232294128545)
      ·
        refine ⟨143790307737353424220596409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191720410316471232294128545 143790307737353424220596409)
        ·
          refine ⟨107842730803015068165447307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143790307737353424220596409 107842730803015068165447307)
          ·
            refine ⟨161764096204522602248170961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107842730803015068165447307 161764096204522602248170961)
            ·
              refine ⟨121323072153391951686128221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161764096204522602248170961 121323072153391951686128221)
              ·
                refine ⟨45496152057521981882298083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121323072153391951686128221 45496152057521981882298083)
                ·
                  refine ⟨68244228086282972823447125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45496152057521981882298083 68244228086282972823447125)
                  ·
                    refine ⟨799737047886128587774771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68244228086282972823447125 799737047886128587774771)
                    ·
                      rfl

theorem cell23_4672447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 8].length) (baseStart_4672447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672447 prefixEnd_4672447 := by exact prefixLift 4672447
  have htrace : WordTrace (prefixWord ++ tailWord_4672447) baseStart_4672447 baseEnd_4672447 := by
    simpa [prefixWord, tailWord_4672447, baseEnd_4672447] using wordTrace_append hprefix tailTrace_4672447
  have hstable : (prefixWord ++ tailWord_4672447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672447).length < 2 ^ (prefixWord ++ tailWord_4672447).sum := by decide
  have hdescent : baseEnd_4672447 < baseStart_4672447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
