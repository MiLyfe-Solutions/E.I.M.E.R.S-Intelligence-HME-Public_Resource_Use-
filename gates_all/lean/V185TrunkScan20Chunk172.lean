import V185TrunkScan20Chunk171

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_1047735 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_1047735 : Nat := 118140960795 + 1047735 * 2 ^ 59
def prefixEnd_1047735 : Nat := 4983230072969 + 3 ^ 40 * 1047735 * 2
def baseEnd_1047735 : Nat := 478214803145389747283609

theorem tailTrace_1047735 : CollatzResearch.WordTrace tailWord_1047735 prefixEnd_1047735 478214803145389747283609 := by
  unfold tailWord_1047735
  simp only [CollatzResearch.WordTrace]
  refine ⟨38214034859242508737056659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25476023239495005824704439 38214034859242508737056659)
  ·
    refine ⟨57321052288863763105584989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38214034859242508737056659 57321052288863763105584989)
    ·
      refine ⟨21495394608323911164594371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57321052288863763105584989 21495394608323911164594371)
      ·
        refine ⟨32243091912485866746891557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21495394608323911164594371 32243091912485866746891557)
        ·
          refine ⟨6045579733591100015042167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32243091912485866746891557 6045579733591100015042167)
          ·
            refine ⟨9068369600386650022563251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6045579733591100015042167 9068369600386650022563251)
            ·
              refine ⟨13602554400579975033844877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068369600386650022563251 13602554400579975033844877)
              ·
                refine ⟨5100957900217490637691829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13602554400579975033844877 5100957900217490637691829)
                ·
                  refine ⟨478214803145389747283609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5100957900217490637691829 478214803145389747283609)
                  ·
                    rfl

theorem cell20_1047735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_1047735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047735 prefixEnd_1047735 := by exact prefixLift 1047735
  have htrace : WordTrace (prefixWord ++ tailWord_1047735) baseStart_1047735 baseEnd_1047735 := by
    simpa [prefixWord, tailWord_1047735, baseEnd_1047735] using wordTrace_append hprefix tailTrace_1047735
  have hstable : (prefixWord ++ tailWord_1047735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047735).length < 2 ^ (prefixWord ++ tailWord_1047735).sum := by decide
  have hdescent : baseEnd_1047735 < baseStart_1047735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047745 : List Nat := [1, 2, 6, 1, 1, 1, 1, 7]
def baseStart_1047745 : Nat := 118140960795 + 1047745 * 2 ^ 59
def prefixEnd_1047745 : Nat := 4983230072969 + 3 ^ 40 * 1047745 * 2
def baseEnd_1047745 : Nat := 159406455805958052316745

theorem tailTrace_1047745 : CollatzResearch.WordTrace tailWord_1047745 prefixEnd_1047745 159406455805958052316745 := by
  unfold tailWord_1047745
  simp only [CollatzResearch.WordTrace]
  refine ⟨38214399589206280444920689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25476266392804186963280459 38214399589206280444920689)
  ·
    refine ⟨28660799691904710333690517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38214399589206280444920689 28660799691904710333690517)
    ·
      refine ⟨1343474985558033296891743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28660799691904710333690517 1343474985558033296891743)
      ·
        refine ⟨2015212478337049945337615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343474985558033296891743 2015212478337049945337615)
        ·
          refine ⟨3022818717505574918006423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015212478337049945337615 3022818717505574918006423)
          ·
            refine ⟨4534228076258362377009635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022818717505574918006423 4534228076258362377009635)
            ·
              refine ⟨6801342114387543565514453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4534228076258362377009635 6801342114387543565514453)
              ·
                refine ⟨159406455805958052316745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6801342114387543565514453 159406455805958052316745)
                ·
                  rfl

theorem cell20_1047745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 7].length) (baseStart_1047745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047745 prefixEnd_1047745 := by exact prefixLift 1047745
  have htrace : WordTrace (prefixWord ++ tailWord_1047745) baseStart_1047745 baseEnd_1047745 := by
    simpa [prefixWord, tailWord_1047745, baseEnd_1047745] using wordTrace_append hprefix tailTrace_1047745
  have hstable : (prefixWord ++ tailWord_1047745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047745).length < 2 ^ (prefixWord ++ tailWord_1047745).sum := by decide
  have hdescent : baseEnd_1047745 < baseStart_1047745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047783 : List Nat := [1, 1, 5, 3, 3, 7]
def baseStart_1047783 : Nat := 118140960795 + 1047783 * 2 ^ 59
def prefixEnd_1047783 : Nat := 4983230072969 + 3 ^ 40 * 1047783 * 2
def baseEnd_1047783 : Nat := 17712470801974626432719

theorem tailTrace_1047783 : CollatzResearch.WordTrace tailWord_1047783 prefixEnd_1047783 17712470801974626432719 := by
  unfold tailWord_1047783
  simp only [CollatzResearch.WordTrace]
  refine ⟨38215785563068612934804003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25477190375379075289869335 38215785563068612934804003)
  ·
    refine ⟨57323678344602919402206005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38215785563068612934804003 57323678344602919402206005)
    ·
      refine ⟨5374094844806523693956813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57323678344602919402206005 5374094844806523693956813)
      ·
        refine ⟨2015285566802446385233805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5374094844806523693956813 2015285566802446385233805)
        ·
          refine ⟨755732087550917394462677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2015285566802446385233805 755732087550917394462677)
          ·
            refine ⟨17712470801974626432719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 755732087550917394462677 17712470801974626432719)
            ·
              rfl

theorem cell20_1047783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 7].length) (baseStart_1047783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047783 prefixEnd_1047783 := by exact prefixLift 1047783
  have htrace : WordTrace (prefixWord ++ tailWord_1047783) baseStart_1047783 baseEnd_1047783 := by
    simpa [prefixWord, tailWord_1047783, baseEnd_1047783] using wordTrace_append hprefix tailTrace_1047783
  have hstable : (prefixWord ++ tailWord_1047783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047783).length < 2 ^ (prefixWord ++ tailWord_1047783).sum := by decide
  have hdescent : baseEnd_1047783 < baseStart_1047783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047787 : List Nat := [1, 1, 1, 1, 2, 14]
def baseStart_1047787 : Nat := 118140960795 + 1047787 * 2 ^ 59
def prefixEnd_1047787 : Nat := 4983230072969 + 3 ^ 40 * 1047787 * 2
def baseEnd_1047787 : Nat := 17712538420826247316669

theorem tailTrace_1047787 : CollatzResearch.WordTrace tailWord_1047787 prefixEnd_1047787 17712538420826247316669 := by
  unfold tailWord_1047787
  simp only [CollatzResearch.WordTrace]
  refine ⟨38215931455054121617949615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25477287636702747745299743 38215931455054121617949615)
  ·
    refine ⟨57323897182581182426924423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38215931455054121617949615 57323897182581182426924423)
    ·
      refine ⟨85985845773871773640386635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57323897182581182426924423 85985845773871773640386635)
      ·
        refine ⟨128978768660807660460579953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85985845773871773640386635 128978768660807660460579953)
        ·
          refine ⟨96734076495605745345434965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128978768660807660460579953 96734076495605745345434965)
          ·
            refine ⟨17712538420826247316669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 96734076495605745345434965 17712538420826247316669)
            ·
              rfl

theorem cell20_1047787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 14].length) (baseStart_1047787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047787 prefixEnd_1047787 := by exact prefixLift 1047787
  have htrace : WordTrace (prefixWord ++ tailWord_1047787) baseStart_1047787 baseEnd_1047787 := by
    simpa [prefixWord, tailWord_1047787, baseEnd_1047787] using wordTrace_append hprefix tailTrace_1047787
  have hstable : (prefixWord ++ tailWord_1047787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047787).length < 2 ^ (prefixWord ++ tailWord_1047787).sum := by decide
  have hdescent : baseEnd_1047787 < baseStart_1047787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047790 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_1047790 : Nat := 118140960795 + 1047790 * 2 ^ 59
def prefixEnd_1047790 : Nat := 4983230072969 + 3 ^ 40 * 1047790 * 2
def baseEnd_1047790 : Nat := 478239906644054000450051

theorem tailTrace_1047790 : CollatzResearch.WordTrace tailWord_1047790 prefixEnd_1047790 478239906644054000450051 := by
  unfold tailWord_1047790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4777005109255406641288603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25477360582695502086872549 4777005109255406641288603)
  ·
    refine ⟨7165507663883109961932905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4777005109255406641288603 7165507663883109961932905)
    ·
      refine ⟨5374130747912332471449679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7165507663883109961932905 5374130747912332471449679)
      ·
        refine ⟨8061196121868498707174519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5374130747912332471449679 8061196121868498707174519)
        ·
          refine ⟨12091794182802748060761779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8061196121868498707174519 12091794182802748060761779)
          ·
            refine ⟨18137691274204122091142669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12091794182802748060761779 18137691274204122091142669)
            ·
              refine ⟨6801634227826545784178501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18137691274204122091142669 6801634227826545784178501)
              ·
                refine ⟨1275306417717477334533469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6801634227826545784178501 1275306417717477334533469)
                ·
                  refine ⟨478239906644054000450051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1275306417717477334533469 478239906644054000450051)
                  ·
                    rfl

theorem cell20_1047790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_1047790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047790 prefixEnd_1047790 := by exact prefixLift 1047790
  have htrace : WordTrace (prefixWord ++ tailWord_1047790) baseStart_1047790 baseEnd_1047790 := by
    simpa [prefixWord, tailWord_1047790, baseEnd_1047790] using wordTrace_append hprefix tailTrace_1047790
  have hstable : (prefixWord ++ tailWord_1047790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047790).length < 2 ^ (prefixWord ++ tailWord_1047790).sum := by decide
  have hdescent : baseEnd_1047790 < baseStart_1047790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047796 : List Nat := [2, 6, 1, 2, 1, 2, 1, 5]
def baseStart_1047796 : Nat := 118140960795 + 1047796 * 2 ^ 59
def prefixEnd_1047796 : Nat := 4983230072969 + 3 ^ 40 * 1047796 * 2
def baseEnd_1047796 : Nat := 159414215069181548750009

theorem tailTrace_1047796 : CollatzResearch.WordTrace tailWord_1047796 prefixEnd_1047796 159414215069181548750009 := by
  unfold tailWord_1047796
  simp only [CollatzResearch.WordTrace]
  refine ⟨19108129856010758077513621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25477506474681010770018161 19108129856010758077513621)
  ·
    refine ⟨895693587000504284883451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19108129856010758077513621 895693587000504284883451)
    ·
      refine ⟨1343540380500756427325177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 895693587000504284883451 1343540380500756427325177)
      ·
        refine ⟨1007655285375567320493883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1343540380500756427325177 1007655285375567320493883)
        ·
          refine ⟨1511482928063350980740825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007655285375567320493883 1511482928063350980740825)
          ·
            refine ⟨1133612196047513235555619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1511482928063350980740825 1133612196047513235555619)
            ·
              refine ⟨1700418294071269853333429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133612196047513235555619 1700418294071269853333429)
              ·
                refine ⟨159414215069181548750009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1700418294071269853333429 159414215069181548750009)
                ·
                  rfl

theorem cell20_1047796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_1047796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047796 prefixEnd_1047796 := by exact prefixLift 1047796
  have htrace : WordTrace (prefixWord ++ tailWord_1047796) baseStart_1047796 baseEnd_1047796 := by
    simpa [prefixWord, tailWord_1047796, baseEnd_1047796] using wordTrace_append hprefix tailTrace_1047796
  have hstable : (prefixWord ++ tailWord_1047796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047796).length < 2 ^ (prefixWord ++ tailWord_1047796).sum := by decide
  have hdescent : baseEnd_1047796 < baseStart_1047796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047838 : List Nat := [4, 3, 2, 1, 2, 1, 7]
def baseStart_1047838 : Nat := 118140960795 + 1047838 * 2 ^ 59
def prefixEnd_1047838 : Nat := 4983230072969 + 3 ^ 40 * 1047838 * 2
def baseEnd_1047838 : Nat := 53140201683553240761095

theorem tailTrace_1047838 : CollatzResearch.WordTrace tailWord_1047838 prefixEnd_1047838 53140201683553240761095 := by
  unfold tailWord_1047838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4777223947233669666007021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25478527718579571552037445 4777223947233669666007021)
  ·
    refine ⟨1791458980212626124752633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4777223947233669666007021 1791458980212626124752633)
    ·
      refine ⟨1343594235159469593564475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1791458980212626124752633 1343594235159469593564475)
      ·
        refine ⟨2015391352739204390346713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343594235159469593564475 2015391352739204390346713)
        ·
          refine ⟨1511543514554403292760035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2015391352739204390346713 1511543514554403292760035)
          ·
            refine ⟨2267315271831604939140053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511543514554403292760035 2267315271831604939140053)
            ·
              refine ⟨53140201683553240761095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2267315271831604939140053 53140201683553240761095)
              ·
                rfl

theorem cell20_1047838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 7].length) (baseStart_1047838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047838 prefixEnd_1047838 := by exact prefixLift 1047838
  have htrace : WordTrace (prefixWord ++ tailWord_1047838) baseStart_1047838 baseEnd_1047838 := by
    simpa [prefixWord, tailWord_1047838, baseEnd_1047838] using wordTrace_append hprefix tailTrace_1047838
  have hstable : (prefixWord ++ tailWord_1047838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047838).length < 2 ^ (prefixWord ++ tailWord_1047838).sum := by decide
  have hdescent : baseEnd_1047838 < baseStart_1047838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047845 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 3]
def baseStart_1047845 : Nat := 118140960795 + 1047845 * 2 ^ 59
def prefixEnd_1047845 : Nat := 4983230072969 + 3 ^ 40 * 1047845 * 2
def baseEnd_1047845 : Nat := 478265010142718253616493

theorem tailTrace_1047845 : CollatzResearch.WordTrace tailWord_1047845 prefixEnd_1047845 478265010142718253616493 := by
  unfold tailWord_1047845
  simp only [CollatzResearch.WordTrace]
  refine ⟨38218046888843997523560989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25478697925895998349040659 38218046888843997523560989)
  ·
    refine ⟨14331767583316499071335371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38218046888843997523560989 14331767583316499071335371)
    ·
      refine ⟨21497651374974748607003057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14331767583316499071335371 21497651374974748607003057)
      ·
        refine ⟨16123238531231061455252293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21497651374974748607003057 16123238531231061455252293)
        ·
          refine ⟨3023107224605824022859805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16123238531231061455252293 3023107224605824022859805)
          ·
            refine ⟨1133665209227184008572427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3023107224605824022859805 1133665209227184008572427)
            ·
              refine ⟨1700497813840776012858641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133665209227184008572427 1700497813840776012858641)
              ·
                refine ⟨1275373360380582009643981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1700497813840776012858641 1275373360380582009643981)
                ·
                  refine ⟨478265010142718253616493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1275373360380582009643981 478265010142718253616493)
                  ·
                    rfl

theorem cell20_1047845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_1047845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047845 prefixEnd_1047845 := by exact prefixLift 1047845
  have htrace : WordTrace (prefixWord ++ tailWord_1047845) baseStart_1047845 baseEnd_1047845 := by
    simpa [prefixWord, tailWord_1047845, baseEnd_1047845] using wordTrace_append hprefix tailTrace_1047845
  have hstable : (prefixWord ++ tailWord_1047845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047845).length < 2 ^ (prefixWord ++ tailWord_1047845).sum := by decide
  have hdescent : baseEnd_1047845 < baseStart_1047845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047876 : List Nat := [2, 3, 4, 1, 1, 1, 4, 4]
def baseStart_1047876 : Nat := 118140960795 + 1047876 * 2 ^ 59
def prefixEnd_1047876 : Nat := 4983230072969 + 3 ^ 40 * 1047876 * 2
def baseEnd_1047876 : Nat := 159426386462473307861011

theorem tailTrace_1047876 : CollatzResearch.WordTrace tailWord_1047876 prefixEnd_1047876 159426386462473307861011 := by
  unfold tailWord_1047876
  simp only [CollatzResearch.WordTrace]
  refine ⟨19109588775865844908969741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25479451701154459878626321 19109588775865844908969741)
  ·
    refine ⟨7166095790949691840863653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19109588775865844908969741 7166095790949691840863653)
    ·
      refine ⟨1343642960803067220161935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7166095790949691840863653 1343642960803067220161935)
      ·
        refine ⟨2015464441204600830242903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343642960803067220161935 2015464441204600830242903)
        ·
          refine ⟨3023196661806901245364355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015464441204600830242903 3023196661806901245364355)
          ·
            refine ⟨4534794992710351868046533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023196661806901245364355 4534794992710351868046533)
            ·
              refine ⟨850274061133190975258725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4534794992710351868046533 850274061133190975258725)
              ·
                refine ⟨159426386462473307861011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 850274061133190975258725 159426386462473307861011)
                ·
                  rfl

theorem cell20_1047876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_1047876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047876 prefixEnd_1047876 := by exact prefixLift 1047876
  have htrace : WordTrace (prefixWord ++ tailWord_1047876) baseStart_1047876 baseEnd_1047876 := by
    simpa [prefixWord, tailWord_1047876, baseEnd_1047876] using wordTrace_append hprefix tailTrace_1047876
  have hstable : (prefixWord ++ tailWord_1047876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047876).length < 2 ^ (prefixWord ++ tailWord_1047876).sum := by decide
  have hdescent : baseEnd_1047876 < baseStart_1047876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047907 : List Nat := [1, 1, 1, 5, 2, 3, 3, 2, 2]
def baseStart_1047907 : Nat := 118140960795 + 1047907 * 2 ^ 59
def prefixEnd_1047907 : Nat := 4983230072969 + 3 ^ 40 * 1047907 * 2
def baseEnd_1047907 : Nat := 478293308632121593549573

theorem tailTrace_1047907 : CollatzResearch.WordTrace tailWord_1047907 prefixEnd_1047907 478293308632121593549573 := by
  unfold tailWord_1047907
  simp only [CollatzResearch.WordTrace]
  refine ⟨38220308214619382112317975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25480205476412921408211983 38220308214619382112317975)
  ·
    refine ⟨57330462321929073168476963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38220308214619382112317975 57330462321929073168476963)
    ·
      refine ⟨85995693482893609752715445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57330462321929073168476963 85995693482893609752715445)
      ·
        refine ⟨8062096264021275914317073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85995693482893609752715445 8062096264021275914317073)
        ·
          refine ⟨6046572198015956935737805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8062096264021275914317073 6046572198015956935737805)
          ·
            refine ⟨2267464574255983850901677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6046572198015956935737805 2267464574255983850901677)
            ·
              refine ⟨850299215345993944088129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2267464574255983850901677 850299215345993944088129)
              ·
                refine ⟨637724411509495458066097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850299215345993944088129 637724411509495458066097)
                ·
                  refine ⟨478293308632121593549573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637724411509495458066097 478293308632121593549573)
                  ·
                    rfl

theorem cell20_1047907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 2].length) (baseStart_1047907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047907 prefixEnd_1047907 := by exact prefixLift 1047907
  have htrace : WordTrace (prefixWord ++ tailWord_1047907) baseStart_1047907 baseEnd_1047907 := by
    simpa [prefixWord, tailWord_1047907, baseEnd_1047907] using wordTrace_append hprefix tailTrace_1047907
  have hstable : (prefixWord ++ tailWord_1047907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047907).length < 2 ^ (prefixWord ++ tailWord_1047907).sum := by decide
  have hdescent : baseEnd_1047907 < baseStart_1047907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047932 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1047932 : Nat := 118140960795 + 1047932 * 2 ^ 59
def prefixEnd_1047932 : Nat := 4983230072969 + 3 ^ 40 * 1047932 * 2
def baseEnd_1047932 : Nat := 478304719313332617716137

theorem tailTrace_1047932 : CollatzResearch.WordTrace tailWord_1047932 prefixEnd_1047932 478304719313332617716137 := by
  unfold tailWord_1047932
  simp only [CollatzResearch.WordTrace]
  refine ⟨19110610019764405690989025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25480813359685874254652033 19110610019764405690989025)
  ·
    refine ⟨14332957514823304268241769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19110610019764405690989025 14332957514823304268241769)
    ·
      refine ⟨10749718136117478201181327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14332957514823304268241769 10749718136117478201181327)
      ·
        refine ⟨16124577204176217301771991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10749718136117478201181327 16124577204176217301771991)
        ·
          refine ⟨24186865806264325952657987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16124577204176217301771991 24186865806264325952657987)
          ·
            refine ⟨36280298709396488928986981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24186865806264325952657987 36280298709396488928986981)
            ·
              refine ⟨6802556008011841674185059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36280298709396488928986981 6802556008011841674185059)
              ·
                refine ⟨10203834012017762511277589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6802556008011841674185059 10203834012017762511277589)
                ·
                  refine ⟨478304719313332617716137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10203834012017762511277589 478304719313332617716137)
                  ·
                    rfl

theorem cell20_1047932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1047932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047932 prefixEnd_1047932 := by exact prefixLift 1047932
  have htrace : WordTrace (prefixWord ++ tailWord_1047932) baseStart_1047932 baseEnd_1047932 := by
    simpa [prefixWord, tailWord_1047932, baseEnd_1047932] using wordTrace_append hprefix tailTrace_1047932
  have hstable : (prefixWord ++ tailWord_1047932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047932).length < 2 ^ (prefixWord ++ tailWord_1047932).sum := by decide
  have hdescent : baseEnd_1047932 < baseStart_1047932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047956 : List Nat := [2, 4, 2, 1, 2, 9]
def baseStart_1047956 : Nat := 118140960795 + 1047956 * 2 ^ 59
def prefixEnd_1047956 : Nat := 4983230072969 + 3 ^ 40 * 1047956 * 2
def baseEnd_1047956 : Nat := 17715395317307229663557

theorem tailTrace_1047956 : CollatzResearch.WordTrace tailWord_1047956 prefixEnd_1047956 17715395317307229663557 := by
  unfold tailWord_1047956
  simp only [CollatzResearch.WordTrace]
  refine ⟨19111047695720931740425861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25481396927627908987234481 19111047695720931740425861)
  ·
    refine ⟨3583321442947674701329849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19111047695720931740425861 3583321442947674701329849)
    ·
      refine ⟨2687491082210756025997387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3583321442947674701329849 2687491082210756025997387)
      ·
        refine ⟨4031236623316134038996081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2687491082210756025997387 4031236623316134038996081)
        ·
          refine ⟨3023427467487100529247061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4031236623316134038996081 3023427467487100529247061)
          ·
            refine ⟨17715395317307229663557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3023427467487100529247061 17715395317307229663557)
            ·
              rfl

theorem cell20_1047956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 9].length) (baseStart_1047956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1047956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1047956 prefixEnd_1047956 := by exact prefixLift 1047956
  have htrace : WordTrace (prefixWord ++ tailWord_1047956) baseStart_1047956 baseEnd_1047956 := by
    simpa [prefixWord, tailWord_1047956, baseEnd_1047956] using wordTrace_append hprefix tailTrace_1047956
  have hstable : (prefixWord ++ tailWord_1047956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047956).length < 2 ^ (prefixWord ++ tailWord_1047956).sum := by decide
  have hdescent : baseEnd_1047956 < baseStart_1047956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048008 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_1048008 : Nat := 118140960795 + 1048008 * 2 ^ 59
def prefixEnd_1048008 : Nat := 4983230072969 + 3 ^ 40 * 1048008 * 2
def baseEnd_1048008 : Nat := 478339407784214131182493

theorem tailTrace_1048008 : CollatzResearch.WordTrace tailWord_1048008 prefixEnd_1048008 478339407784214131182493 := by
  unfold tailWord_1048008
  simp only [CollatzResearch.WordTrace]
  refine ⟨19111995993626738180872339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25482661324835650907829785 19111995993626738180872339)
  ·
    refine ⟨28667993990440107271308509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19111995993626738180872339 28667993990440107271308509)
    ·
      refine ⟨10750497746415040226740691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28667993990440107271308509 10750497746415040226740691)
      ·
        refine ⟨16125746619622560340111037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10750497746415040226740691 16125746619622560340111037)
        ·
          refine ⟨6047154982358460127541639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16125746619622560340111037 6047154982358460127541639)
          ·
            refine ⟨9070732473537690191312459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6047154982358460127541639 9070732473537690191312459)
            ·
              refine ⟨13606098710306535286968689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9070732473537690191312459 13606098710306535286968689)
              ·
                refine ⟨10204574032729901465226517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13606098710306535286968689 10204574032729901465226517)
                ·
                  refine ⟨478339407784214131182493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10204574032729901465226517 478339407784214131182493)
                  ·
                    rfl

theorem cell20_1048008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_1048008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048008 prefixEnd_1048008 := by exact prefixLift 1048008
  have htrace : WordTrace (prefixWord ++ tailWord_1048008) baseStart_1048008 baseEnd_1048008 := by
    simpa [prefixWord, tailWord_1048008, baseEnd_1048008] using wordTrace_append hprefix tailTrace_1048008
  have hstable : (prefixWord ++ tailWord_1048008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048008).length < 2 ^ (prefixWord ++ tailWord_1048008).sum := by decide
  have hdescent : baseEnd_1048008 < baseStart_1048008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048025 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 4]
def baseStart_1048025 : Nat := 118140960795 + 1048025 * 2 ^ 59
def prefixEnd_1048025 : Nat := 4983230072969 + 3 ^ 40 * 1048025 * 2
def baseEnd_1048025 : Nat := 478347167047437627615757

theorem tailTrace_1048025 : CollatzResearch.WordTrace tailWord_1048025 prefixEnd_1048025 478347167047437627615757 := by
  unfold tailWord_1048025
  simp only [CollatzResearch.WordTrace]
  refine ⟨38224612028191888265113529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25483074685461258843409019 38224612028191888265113529)
  ·
    refine ⟨28668459021143916198835147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38224612028191888265113529 28668459021143916198835147)
    ·
      refine ⟨43002688531715874298252721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28668459021143916198835147 43002688531715874298252721)
      ·
        refine ⟨32252016398786905723689541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43002688531715874298252721 32252016398786905723689541)
        ·
          refine ⟨6047253074772544823191789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32252016398786905723689541 6047253074772544823191789)
          ·
            refine ⟨2267719903039704308696921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6047253074772544823191789 2267719903039704308696921)
            ·
              refine ⟨1700789927279778231522691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2267719903039704308696921 1700789927279778231522691)
              ·
                refine ⟨2551184890919667347284037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1700789927279778231522691 2551184890919667347284037)
                ·
                  refine ⟨478347167047437627615757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2551184890919667347284037 478347167047437627615757)
                  ·
                    rfl

theorem cell20_1048025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_1048025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048025 prefixEnd_1048025 := by exact prefixLift 1048025
  have htrace : WordTrace (prefixWord ++ tailWord_1048025) baseStart_1048025 baseEnd_1048025 := by
    simpa [prefixWord, tailWord_1048025, baseEnd_1048025] using wordTrace_append hprefix tailTrace_1048025
  have hstable : (prefixWord ++ tailWord_1048025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048025).length < 2 ^ (prefixWord ++ tailWord_1048025).sum := by decide
  have hdescent : baseEnd_1048025 < baseStart_1048025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048035 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 3]
def baseStart_1048035 : Nat := 118140960795 + 1048035 * 2 ^ 59
def prefixEnd_1048035 : Nat := 4983230072969 + 3 ^ 40 * 1048035 * 2
def baseEnd_1048035 : Nat := 478351731319922037282383

theorem tailTrace_1048035 : CollatzResearch.WordTrace tailWord_1048035 prefixEnd_1048035 478351731319922037282383 := by
  unfold tailWord_1048035
  simp only [CollatzResearch.WordTrace]
  refine ⟨38224976758155659972977559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25483317838770439981985039 38224976758155659972977559)
  ·
    refine ⟨57337465137233489959466339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38224976758155659972977559 57337465137233489959466339)
    ·
      refine ⟨86006197705850234939199509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57337465137233489959466339 86006197705850234939199509)
      ·
        refine ⟨4031540517461729762774977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86006197705850234939199509 4031540517461729762774977)
        ·
          refine ⟨3023655388096297322081233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4031540517461729762774977 3023655388096297322081233)
          ·
            refine ⟨2267741541072222991560925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3023655388096297322081233 2267741541072222991560925)
            ·
              refine ⟨850403077902083621835347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2267741541072222991560925 850403077902083621835347)
              ·
                refine ⟨1275604616853125432753021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850403077902083621835347 1275604616853125432753021)
                ·
                  refine ⟨478351731319922037282383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1275604616853125432753021 478351731319922037282383)
                  ·
                    rfl

theorem cell20_1048035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 3].length) (baseStart_1048035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048035 prefixEnd_1048035 := by exact prefixLift 1048035
  have htrace : WordTrace (prefixWord ++ tailWord_1048035) baseStart_1048035 baseEnd_1048035 := by
    simpa [prefixWord, tailWord_1048035, baseEnd_1048035] using wordTrace_append hprefix tailTrace_1048035
  have hstable : (prefixWord ++ tailWord_1048035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048035).length < 2 ^ (prefixWord ++ tailWord_1048035).sum := by decide
  have hdescent : baseEnd_1048035 < baseStart_1048035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048045 : List Nat := [1, 5, 1, 3, 3, 1, 2, 4]
def baseStart_1048045 : Nat := 118140960795 + 1048045 * 2 ^ 59
def prefixEnd_1048045 : Nat := 4983230072969 + 3 ^ 40 * 1048045 * 2
def baseEnd_1048045 : Nat := 159452098530802148983003

theorem tailTrace_1048045 : CollatzResearch.WordTrace tailWord_1048045 prefixEnd_1048045 159452098530802148983003 := by
  unfold tailWord_1048045
  simp only [CollatzResearch.WordTrace]
  refine ⟨38225341488119431680841589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25483560992079621120561059 38225341488119431680841589)
  ·
    refine ⟨3583625764511196720078899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38225341488119431680841589 3583625764511196720078899)
    ·
      refine ⟨5375438646766795080118349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3583625764511196720078899 5375438646766795080118349)
      ·
        refine ⟨2015789492537548155044381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5375438646766795080118349 2015789492537548155044381)
        ·
          refine ⟨755921059701580558141643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2015789492537548155044381 755921059701580558141643)
          ·
            refine ⟨1133881589552370837212465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755921059701580558141643 1133881589552370837212465)
            ·
              refine ⟨850411192164278127909349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133881589552370837212465 850411192164278127909349)
              ·
                refine ⟨159452098530802148983003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 850411192164278127909349 159452098530802148983003)
                ·
                  rfl

theorem cell20_1048045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 4].length) (baseStart_1048045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048045 prefixEnd_1048045 := by exact prefixLift 1048045
  have htrace : WordTrace (prefixWord ++ tailWord_1048045) baseStart_1048045 baseEnd_1048045 := by
    simpa [prefixWord, tailWord_1048045, baseEnd_1048045] using wordTrace_append hprefix tailTrace_1048045
  have hstable : (prefixWord ++ tailWord_1048045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048045).length < 2 ^ (prefixWord ++ tailWord_1048045).sum := by decide
  have hdescent : baseEnd_1048045 < baseStart_1048045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048049 : List Nat := [1, 2, 2, 2, 3, 4, 2, 4]
def baseStart_1048049 : Nat := 118140960795 + 1048049 * 2 ^ 59
def prefixEnd_1048049 : Nat := 4983230072969 + 3 ^ 40 * 1048049 * 2
def baseEnd_1048049 : Nat := 159452707100466736938553

theorem tailTrace_1048049 : CollatzResearch.WordTrace tailWord_1048049 prefixEnd_1048049 159452707100466736938553 := by
  unfold tailWord_1048049
  simp only [CollatzResearch.WordTrace]
  refine ⟨38225487380104940363987201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25483658253403293575991467 38225487380104940363987201)
  ·
    refine ⟨28669115535078705272990401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38225487380104940363987201 28669115535078705272990401)
    ·
      refine ⟨21501836651309028954742801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28669115535078705272990401 21501836651309028954742801)
      ·
        refine ⟨16126377488481771716057101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21501836651309028954742801 16126377488481771716057101)
        ·
          refine ⟨6047391558180664393521413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16126377488481771716057101 6047391558180664393521413)
          ·
            refine ⟨1133885917158874573785265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6047391558180664393521413 1133885917158874573785265)
            ·
              refine ⟨850414437869155930338949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133885917158874573785265 850414437869155930338949)
              ·
                refine ⟨159452707100466736938553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 850414437869155930338949 159452707100466736938553)
                ·
                  rfl

theorem cell20_1048049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 4].length) (baseStart_1048049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048049 prefixEnd_1048049 := by exact prefixLift 1048049
  have htrace : WordTrace (prefixWord ++ tailWord_1048049) baseStart_1048049 baseEnd_1048049 := by
    simpa [prefixWord, tailWord_1048049, baseEnd_1048049] using wordTrace_append hprefix tailTrace_1048049
  have hstable : (prefixWord ++ tailWord_1048049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048049).length < 2 ^ (prefixWord ++ tailWord_1048049).sum := by decide
  have hdescent : baseEnd_1048049 < baseStart_1048049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048063 : List Nat := [1, 1, 2, 2, 1, 2, 2, 7, 2]
def baseStart_1048063 : Nat := 118140960795 + 1048063 * 2 ^ 59
def prefixEnd_1048063 : Nat := 4983230072969 + 3 ^ 40 * 1048063 * 2
def baseEnd_1048063 : Nat := 478364511282878384348935

theorem tailTrace_1048063 : CollatzResearch.WordTrace tailWord_1048063 prefixEnd_1048063 478364511282878384348935 := by
  unfold tailWord_1048063
  simp only [CollatzResearch.WordTrace]
  refine ⟨38225998002054220754996843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25483998668036147169997895 38225998002054220754996843)
  ·
    refine ⟨57338997003081331132495265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38225998002054220754996843 57338997003081331132495265)
    ·
      refine ⟨43004247752310998349371449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57338997003081331132495265 43004247752310998349371449)
      ·
        refine ⟨32253185814233248762028587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43004247752310998349371449 32253185814233248762028587)
        ·
          refine ⟨48379778721349873143042881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32253185814233248762028587 48379778721349873143042881)
          ·
            refine ⟨36284834041012404857282161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48379778721349873143042881 36284834041012404857282161)
            ·
              refine ⟨27213625530759303642961621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36284834041012404857282161 27213625530759303642961621)
              ·
                refine ⟨637819348377171179131913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27213625530759303642961621 637819348377171179131913)
                ·
                  refine ⟨478364511282878384348935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637819348377171179131913 478364511282878384348935)
                  ·
                    rfl

theorem cell20_1048063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 2].length) (baseStart_1048063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048063 prefixEnd_1048063 := by exact prefixLift 1048063
  have htrace : WordTrace (prefixWord ++ tailWord_1048063) baseStart_1048063 baseEnd_1048063 := by
    simpa [prefixWord, tailWord_1048063, baseEnd_1048063] using wordTrace_append hprefix tailTrace_1048063
  have hstable : (prefixWord ++ tailWord_1048063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048063).length < 2 ^ (prefixWord ++ tailWord_1048063).sum := by decide
  have hdescent : baseEnd_1048063 < baseStart_1048063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048146 : List Nat := [3, 2, 2, 1, 2, 2, 3, 5]
def baseStart_1048146 : Nat := 118140960795 + 1048146 * 2 ^ 59
def prefixEnd_1048146 : Nat := 4983230072969 + 3 ^ 40 * 1048146 * 2
def baseEnd_1048146 : Nat := 159467464914832994860643

theorem tailTrace_1048146 : CollatzResearch.WordTrace tailWord_1048146 prefixEnd_1048146 159467464914832994860643 := by
  unfold tailWord_1048146
  simp only [CollatzResearch.WordTrace]
  refine ⟨9557256315188381482567073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25486016840502350620178861 9557256315188381482567073)
  ·
    refine ⟨7167942236391286111925305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9557256315188381482567073 7167942236391286111925305)
    ·
      refine ⟨5375956677293464583943979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7167942236391286111925305 5375956677293464583943979)
      ·
        refine ⟨8063935015940196875915969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5375956677293464583943979 8063935015940196875915969)
        ·
          refine ⟨6047951261955147656936977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8063935015940196875915969 6047951261955147656936977)
          ·
            refine ⟨4535963446466360742702733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6047951261955147656936977 4535963446466360742702733)
            ·
              refine ⟨1700986292424885278513525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4535963446466360742702733 1700986292424885278513525)
              ·
                refine ⟨159467464914832994860643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1700986292424885278513525 159467464914832994860643)
                ·
                  rfl

theorem cell20_1048146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_1048146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048146 prefixEnd_1048146 := by exact prefixLift 1048146
  have htrace : WordTrace (prefixWord ++ tailWord_1048146) baseStart_1048146 baseEnd_1048146 := by
    simpa [prefixWord, tailWord_1048146, baseEnd_1048146] using wordTrace_append hprefix tailTrace_1048146
  have hstable : (prefixWord ++ tailWord_1048146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048146).length < 2 ^ (prefixWord ++ tailWord_1048146).sum := by decide
  have hdescent : baseEnd_1048146 < baseStart_1048146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048167 : List Nat := [1, 1, 5, 1, 1, 1, 2, 8]
def baseStart_1048167 : Nat := 118140960795 + 1048167 * 2 ^ 59
def prefixEnd_1048167 : Nat := 4983230072969 + 3 ^ 40 * 1048167 * 2
def baseEnd_1048167 : Nat := 159470659905572081627281

theorem tailTrace_1048167 : CollatzResearch.WordTrace tailWord_1048167 prefixEnd_1048167 159470659905572081627281 := by
  unfold tailWord_1048167
  simp only [CollatzResearch.WordTrace]
  refine ⟨38229791193677446516782755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25486527462451631011188503 38229791193677446516782755)
  ·
    refine ⟨57344686790516169775174133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38229791193677446516782755 57344686790516169775174133)
    ·
      refine ⟨5376064386610890916422575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57344686790516169775174133 5376064386610890916422575)
      ·
        refine ⟨8064096579916336374633863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5376064386610890916422575 8064096579916336374633863)
        ·
          refine ⟨12096144869874504561950795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8064096579916336374633863 12096144869874504561950795)
          ·
            refine ⟨18144217304811756842926193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12096144869874504561950795 18144217304811756842926193)
            ·
              refine ⟨13608162978608817632194645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18144217304811756842926193 13608162978608817632194645)
              ·
                refine ⟨159470659905572081627281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13608162978608817632194645 159470659905572081627281)
                ·
                  rfl

theorem cell20_1048167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_1048167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048167 prefixEnd_1048167 := by exact prefixLift 1048167
  have htrace : WordTrace (prefixWord ++ tailWord_1048167) baseStart_1048167 baseEnd_1048167 := by
    simpa [prefixWord, tailWord_1048167, baseEnd_1048167] using wordTrace_append hprefix tailTrace_1048167
  have hstable : (prefixWord ++ tailWord_1048167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048167).length < 2 ^ (prefixWord ++ tailWord_1048167).sum := by decide
  have hdescent : baseEnd_1048167 < baseStart_1048167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048173 : List Nat := [1, 5, 1, 1, 4, 1, 2, 3, 2]
def baseStart_1048173 : Nat := 118140960795 + 1048173 * 2 ^ 59
def prefixEnd_1048173 : Nat := 4983230072969 + 3 ^ 40 * 1048173 * 2
def baseEnd_1048173 : Nat := 478414718280206890681819

theorem tailTrace_1048173 : CollatzResearch.WordTrace tailWord_1048173 prefixEnd_1048173 478414718280206890681819 := by
  unfold tailWord_1048173
  simp only [CollatzResearch.WordTrace]
  refine ⟨38230010031655709541501173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25486673354437139694334115 38230010031655709541501173)
  ·
    refine ⟨3584063440467722769515735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38230010031655709541501173 3584063440467722769515735)
    ·
      refine ⟨5376095160701584154273603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3584063440467722769515735 5376095160701584154273603)
      ·
        refine ⟨8064142741052376231410405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5376095160701584154273603 8064142741052376231410405)
        ·
          refine ⟨1512026763947320543389451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8064142741052376231410405 1512026763947320543389451)
          ·
            refine ⟨2268040145920980815084177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512026763947320543389451 2268040145920980815084177)
            ·
              refine ⟨1701030109440735611313133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2268040145920980815084177 1701030109440735611313133)
              ·
                refine ⟨637886291040275854242425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1701030109440735611313133 637886291040275854242425)
                ·
                  refine ⟨478414718280206890681819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637886291040275854242425 478414718280206890681819)
                  ·
                    rfl

theorem cell20_1048173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_1048173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048173 prefixEnd_1048173 := by exact prefixLift 1048173
  have htrace : WordTrace (prefixWord ++ tailWord_1048173) baseStart_1048173 baseEnd_1048173 := by
    simpa [prefixWord, tailWord_1048173, baseEnd_1048173] using wordTrace_append hprefix tailTrace_1048173
  have hstable : (prefixWord ++ tailWord_1048173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048173).length < 2 ^ (prefixWord ++ tailWord_1048173).sum := by decide
  have hdescent : baseEnd_1048173 < baseStart_1048173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048260 : List Nat := [2, 3, 3, 1, 1, 1, 4, 5]
def baseStart_1048260 : Nat := 118140960795 + 1048260 * 2 ^ 59
def prefixEnd_1048260 : Nat := 4983230072969 + 3 ^ 40 * 1048260 * 2
def baseEnd_1048260 : Nat := 159484809150273751593821

theorem tailTrace_1048260 : CollatzResearch.WordTrace tailWord_1048260 prefixEnd_1048260 159484809150273751593821 := by
  unfold tailWord_1048260
  simp only [CollatzResearch.WordTrace]
  refine ⟨19116591591170261699959117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25488788788227015599945489 19116591591170261699959117)
  ·
    refine ⟨7168721846688848137484669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19116591591170261699959117 7168721846688848137484669)
    ·
      refine ⟨2688270692508318051556751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7168721846688848137484669 2688270692508318051556751)
      ·
        refine ⟨4032406038762477077335127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688270692508318051556751 4032406038762477077335127)
        ·
          refine ⟨6048609058143715616002691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032406038762477077335127 6048609058143715616002691)
          ·
            refine ⟨9072913587215573424004037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6048609058143715616002691 9072913587215573424004037)
            ·
              refine ⟨1701171297602920017000757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9072913587215573424004037 1701171297602920017000757)
              ·
                refine ⟨159484809150273751593821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1701171297602920017000757 159484809150273751593821)
                ·
                  rfl

theorem cell20_1048260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_1048260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048260 prefixEnd_1048260 := by exact prefixLift 1048260
  have htrace : WordTrace (prefixWord ++ tailWord_1048260) baseStart_1048260 baseEnd_1048260 := by
    simpa [prefixWord, tailWord_1048260, baseEnd_1048260] using wordTrace_append hprefix tailTrace_1048260
  have hstable : (prefixWord ++ tailWord_1048260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048260).length < 2 ^ (prefixWord ++ tailWord_1048260).sum := by decide
  have hdescent : baseEnd_1048260 < baseStart_1048260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048281 : List Nat := [1, 2, 1, 2, 3, 3, 2, 6]
def baseStart_1048281 : Nat := 118140960795 + 1048281 * 2 ^ 59
def prefixEnd_1048281 : Nat := 4983230072969 + 3 ^ 40 * 1048281 * 2
def baseEnd_1048281 : Nat := 159488004141012838360459

theorem tailTrace_1048281 : CollatzResearch.WordTrace tailWord_1048281 prefixEnd_1048281 159488004141012838360459 := by
  unfold tailWord_1048281
  simp only [CollatzResearch.WordTrace]
  refine ⟨38233949115264443986432697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25489299410176295990955131 38233949115264443986432697)
  ·
    refine ⟨28675461836448332989824523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38233949115264443986432697 28675461836448332989824523)
    ·
      refine ⟨43013192754672499484736785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28675461836448332989824523 43013192754672499484736785)
      ·
        refine ⟨32259894566004374613552589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43013192754672499484736785 32259894566004374613552589)
        ·
          refine ⟨12097460462251640480082221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32259894566004374613552589 12097460462251640480082221)
          ·
            refine ⟨4536547673344365180030833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12097460462251640480082221 4536547673344365180030833)
            ·
              refine ⟨3402410755008273885023125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4536547673344365180030833 3402410755008273885023125)
              ·
                refine ⟨159488004141012838360459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3402410755008273885023125 159488004141012838360459)
                ·
                  rfl

theorem cell20_1048281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_1048281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048281 prefixEnd_1048281 := by exact prefixLift 1048281
  have htrace : WordTrace (prefixWord ++ tailWord_1048281) baseStart_1048281 baseEnd_1048281 := by
    simpa [prefixWord, tailWord_1048281, baseEnd_1048281] using wordTrace_append hprefix tailTrace_1048281
  have hstable : (prefixWord ++ tailWord_1048281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048281).length < 2 ^ (prefixWord ++ tailWord_1048281).sum := by decide
  have hdescent : baseEnd_1048281 < baseStart_1048281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048288 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_1048288 : Nat := 118140960795 + 1048288 * 2 ^ 59
def prefixEnd_1048288 : Nat := 4983230072969 + 3 ^ 40 * 1048288 * 2
def baseEnd_1048288 : Nat := 478467207413777601848015

theorem tailTrace_1048288 : CollatzResearch.WordTrace tailWord_1048288 prefixEnd_1048288 478467207413777601848015 := by
  unfold tailWord_1048288
  simp only [CollatzResearch.WordTrace]
  refine ⟨19117102213119542090968759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25489469617492722787958345 19117102213119542090968759)
  ·
    refine ⟨28675653319679313136453139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19117102213119542090968759 28675653319679313136453139)
    ·
      refine ⟨43013479979518969704679709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28675653319679313136453139 43013479979518969704679709)
      ·
        refine ⟨16130054992319613639254891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43013479979518969704679709 16130054992319613639254891)
        ·
          refine ⟨24195082488479420458882337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16130054992319613639254891 24195082488479420458882337)
          ·
            refine ⟨18146311866359565344161753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24195082488479420458882337 18146311866359565344161753)
            ·
              refine ⟨13609733899769674008121315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18146311866359565344161753 13609733899769674008121315)
              ·
                refine ⟨20414600849654511012181973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13609733899769674008121315 20414600849654511012181973)
                ·
                  refine ⟨478467207413777601848015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20414600849654511012181973 478467207413777601848015)
                  ·
                    rfl

theorem cell20_1048288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_1048288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048288 prefixEnd_1048288 := by exact prefixLift 1048288
  have htrace : WordTrace (prefixWord ++ tailWord_1048288) baseStart_1048288 baseEnd_1048288 := by
    simpa [prefixWord, tailWord_1048288, baseEnd_1048288] using wordTrace_append hprefix tailTrace_1048288
  have hstable : (prefixWord ++ tailWord_1048288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048288).length < 2 ^ (prefixWord ++ tailWord_1048288).sum := by decide
  have hdescent : baseEnd_1048288 < baseStart_1048288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048305 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 3]
def baseStart_1048305 : Nat := 118140960795 + 1048305 * 2 ^ 59
def prefixEnd_1048305 : Nat := 4983230072969 + 3 ^ 40 * 1048305 * 2
def baseEnd_1048305 : Nat := 478474966677001098281279

theorem tailTrace_1048305 : CollatzResearch.WordTrace tailWord_1048305 prefixEnd_1048305 478474966677001098281279 := by
  unfold tailWord_1048305
  simp only [CollatzResearch.WordTrace]
  refine ⟨38234824467177496085306369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25489882978118330723537579 38234824467177496085306369)
  ·
    refine ⟨28676118350383122063979777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38234824467177496085306369 28676118350383122063979777)
    ·
      refine ⟨21507088762787341547984833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28676118350383122063979777 21507088762787341547984833)
      ·
        refine ⟨16130316572090506160988625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21507088762787341547984833 16130316572090506160988625)
        ·
          refine ⟨12097737429067879620741469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16130316572090506160988625 12097737429067879620741469)
          ·
            refine ⟨4536651535900454857778051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12097737429067879620741469 4536651535900454857778051)
            ·
              refine ⟨6804977303850682286667077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536651535900454857778051 6804977303850682286667077)
              ·
                refine ⟨1275933244472002928750077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6804977303850682286667077 1275933244472002928750077)
                ·
                  refine ⟨478474966677001098281279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1275933244472002928750077 478474966677001098281279)
                  ·
                    rfl

theorem cell20_1048305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_1048305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048305 prefixEnd_1048305 := by exact prefixLift 1048305
  have htrace : WordTrace (prefixWord ++ tailWord_1048305) baseStart_1048305 baseEnd_1048305 := by
    simpa [prefixWord, tailWord_1048305, baseEnd_1048305] using wordTrace_append hprefix tailTrace_1048305
  have hstable : (prefixWord ++ tailWord_1048305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048305).length < 2 ^ (prefixWord ++ tailWord_1048305).sum := by decide
  have hdescent : baseEnd_1048305 < baseStart_1048305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048319 : List Nat := [1, 1, 2, 2, 1, 3, 5, 5]
def baseStart_1048319 : Nat := 118140960795 + 1048319 * 2 ^ 59
def prefixEnd_1048319 : Nat := 4983230072969 + 3 ^ 40 * 1048319 * 2
def baseEnd_1048319 : Nat := 159493785552826423938185

theorem tailTrace_1048319 : CollatzResearch.WordTrace tailWord_1048319 prefixEnd_1048319 159493785552826423938185 := by
  unfold tailWord_1048319
  simp only [CollatzResearch.WordTrace]
  refine ⟨38235335089126776476316011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25490223392751184317544007 38235335089126776476316011)
  ·
    refine ⟨57353002633690164714474017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38235335089126776476316011 57353002633690164714474017)
    ·
      refine ⟨43014751975267623535855513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57353002633690164714474017 43014751975267623535855513)
      ·
        refine ⟨32261063981450717651891635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43014751975267623535855513 32261063981450717651891635)
        ·
          refine ⟨48391595972176076477837453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32261063981450717651891635 48391595972176076477837453)
          ·
            refine ⟨18146848489566028679189045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48391595972176076477837453 18146848489566028679189045)
            ·
              refine ⟨1701267045896815188673973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18146848489566028679189045 1701267045896815188673973)
              ·
                refine ⟨159493785552826423938185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1701267045896815188673973 159493785552826423938185)
                ·
                  rfl

theorem cell20_1048319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_1048319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048319 prefixEnd_1048319 := by exact prefixLift 1048319
  have htrace : WordTrace (prefixWord ++ tailWord_1048319) baseStart_1048319 baseEnd_1048319 := by
    simpa [prefixWord, tailWord_1048319, baseEnd_1048319] using wordTrace_append hprefix tailTrace_1048319
  have hstable : (prefixWord ++ tailWord_1048319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048319).length < 2 ^ (prefixWord ++ tailWord_1048319).sum := by decide
  have hdescent : baseEnd_1048319 < baseStart_1048319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048322 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1048322 : Nat := 118140960795 + 1048322 * 2 ^ 59
def prefixEnd_1048322 : Nat := 4983230072969 + 3 ^ 40 * 1048322 * 2
def baseEnd_1048322 : Nat := 478482725940224594714543

theorem tailTrace_1048322 : CollatzResearch.WordTrace tailWord_1048322 prefixEnd_1048322 478482725940224594714543 := by
  unfold tailWord_1048322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9558861127028976997168805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25490296338743938659116813 9558861127028976997168805)
  ·
    refine ⟨1792286461317933186969151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9558861127028976997168805 1792286461317933186969151)
    ·
      refine ⟨2688429691976899780453727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1792286461317933186969151 2688429691976899780453727)
      ·
        refine ⟨4032644537965349670680591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688429691976899780453727 4032644537965349670680591)
        ·
          refine ⟨6048966806948024506020887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032644537965349670680591 6048966806948024506020887)
          ·
            refine ⟨9073450210422036759031331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6048966806948024506020887 9073450210422036759031331)
            ·
              refine ⟨13610175315633055138546997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9073450210422036759031331 13610175315633055138546997)
              ·
                refine ⟨1275953935840598919238781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13610175315633055138546997 1275953935840598919238781)
                ·
                  refine ⟨478482725940224594714543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1275953935840598919238781 478482725940224594714543)
                  ·
                    rfl

theorem cell20_1048322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1048322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048322 prefixEnd_1048322 := by exact prefixLift 1048322
  have htrace : WordTrace (prefixWord ++ tailWord_1048322) baseStart_1048322 baseEnd_1048322 := by
    simpa [prefixWord, tailWord_1048322, baseEnd_1048322] using wordTrace_append hprefix tailTrace_1048322
  have hstable : (prefixWord ++ tailWord_1048322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048322).length < 2 ^ (prefixWord ++ tailWord_1048322).sum := by decide
  have hdescent : baseEnd_1048322 < baseStart_1048322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048346 : List Nat := [3, 1, 1, 3, 2, 3, 2, 3, 2]
def baseStart_1048346 : Nat := 118140960795 + 1048346 * 2 ^ 59
def prefixEnd_1048346 : Nat := 4983230072969 + 3 ^ 40 * 1048346 * 2
def baseEnd_1048346 : Nat := 478493680194187177914445

theorem tailTrace_1048346 : CollatzResearch.WordTrace tailWord_1048346 prefixEnd_1048346 478493680194187177914445 := by
  unfold tailWord_1048346
  simp only [CollatzResearch.WordTrace]
  refine ⟨9559079965007240021887223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25490879906685973391699261 9559079965007240021887223)
  ·
    refine ⟨14338619947510860032830835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9559079965007240021887223 14338619947510860032830835)
    ·
      refine ⟨21507929921266290049246253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14338619947510860032830835 21507929921266290049246253)
      ·
        refine ⟨8065473720474858768467345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21507929921266290049246253 8065473720474858768467345)
        ·
          refine ⟨6049105290356144076350509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8065473720474858768467345 6049105290356144076350509)
          ·
            refine ⟨2268414483883554028631441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6049105290356144076350509 2268414483883554028631441)
            ·
              refine ⟨1701310862912665521473581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2268414483883554028631441 1701310862912665521473581)
              ·
                refine ⟨637991573592249570552593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1701310862912665521473581 637991573592249570552593)
                ·
                  refine ⟨478493680194187177914445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 637991573592249570552593 478493680194187177914445)
                  ·
                    rfl

theorem cell20_1048346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_1048346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048346 prefixEnd_1048346 := by exact prefixLift 1048346
  have htrace : WordTrace (prefixWord ++ tailWord_1048346) baseStart_1048346 baseEnd_1048346 := by
    simpa [prefixWord, tailWord_1048346, baseEnd_1048346] using wordTrace_append hprefix tailTrace_1048346
  have hstable : (prefixWord ++ tailWord_1048346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048346).length < 2 ^ (prefixWord ++ tailWord_1048346).sum := by decide
  have hdescent : baseEnd_1048346 < baseStart_1048346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048357 : List Nat := [1, 3, 1, 2, 3, 3, 7]
def baseStart_1048357 : Nat := 118140960795 + 1048357 * 2 ^ 59
def prefixEnd_1048357 : Nat := 4983230072969 + 3 ^ 40 * 1048357 * 2
def baseEnd_1048357 : Nat := 53166522321546669838637

theorem tailTrace_1048357 : CollatzResearch.WordTrace tailWord_1048357 prefixEnd_1048357 53166522321546669838637 := by
  unfold tailWord_1048357
  simp only [CollatzResearch.WordTrace]
  refine ⟨38236721062989108966199325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25491147375326072644132883 38236721062989108966199325)
  ·
    refine ⟨14338770398620915862324747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38236721062989108966199325 14338770398620915862324747)
    ·
      refine ⟨21508155597931373793487121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14338770398620915862324747 21508155597931373793487121)
      ·
        refine ⟨16131116698448530345115341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21508155597931373793487121 16131116698448530345115341)
        ·
          refine ⟨6049168761918198879418253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16131116698448530345115341 6049168761918198879418253)
          ·
            refine ⟨2268438285719324579781845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6049168761918198879418253 2268438285719324579781845)
            ·
              refine ⟨53166522321546669838637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2268438285719324579781845 53166522321546669838637)
              ·
                rfl

theorem cell20_1048357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 7].length) (baseStart_1048357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048357 prefixEnd_1048357 := by exact prefixLift 1048357
  have htrace : WordTrace (prefixWord ++ tailWord_1048357) baseStart_1048357 baseEnd_1048357 := by
    simpa [prefixWord, tailWord_1048357, baseEnd_1048357] using wordTrace_append hprefix tailTrace_1048357
  have hstable : (prefixWord ++ tailWord_1048357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048357).length < 2 ^ (prefixWord ++ tailWord_1048357).sum := by decide
  have hdescent : baseEnd_1048357 < baseStart_1048357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048360 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 3]
def baseStart_1048360 : Nat := 118140960795 + 1048360 * 2 ^ 59
def prefixEnd_1048360 : Nat := 4983230072969 + 3 ^ 40 * 1048360 * 2
def baseEnd_1048360 : Nat := 478500070175665351447721

theorem tailTrace_1048360 : CollatzResearch.WordTrace tailWord_1048360 prefixEnd_1048360 478500070175665351447721 := by
  unfold tailWord_1048360
  simp only [CollatzResearch.WordTrace]
  refine ⟨19118415240989120239279267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25491220321318826985705689 19118415240989120239279267)
  ·
    refine ⟨28677622861483680358918901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19118415240989120239279267 28677622861483680358918901)
    ·
      refine ⟨2688527143264095033648647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28677622861483680358918901 2688527143264095033648647)
      ·
        refine ⟨4032790714896142550472971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688527143264095033648647 4032790714896142550472971)
        ·
          refine ⟨6049186072344213825709457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032790714896142550472971 6049186072344213825709457)
          ·
            refine ⟨4536889554258160369282093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6049186072344213825709457 4536889554258160369282093)
            ·
              refine ⟨1701333582846810138480785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4536889554258160369282093 1701333582846810138480785)
              ·
                refine ⟨1276000187135107603860589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1701333582846810138480785 1276000187135107603860589)
                ·
                  refine ⟨478500070175665351447721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1276000187135107603860589 478500070175665351447721)
                  ·
                    rfl

theorem cell20_1048360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_1048360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048360 prefixEnd_1048360 := by exact prefixLift 1048360
  have htrace : WordTrace (prefixWord ++ tailWord_1048360) baseStart_1048360 baseEnd_1048360 := by
    simpa [prefixWord, tailWord_1048360, baseEnd_1048360] using wordTrace_append hprefix tailTrace_1048360
  have hstable : (prefixWord ++ tailWord_1048360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048360).length < 2 ^ (prefixWord ++ tailWord_1048360).sum := by decide
  have hdescent : baseEnd_1048360 < baseStart_1048360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048433 : List Nat := [1, 2, 2, 2, 1, 3, 4, 5]
def baseStart_1048433 : Nat := 118140960795 + 1048433 * 2 ^ 59
def prefixEnd_1048433 : Nat := 4983230072969 + 3 ^ 40 * 1048433 * 2
def baseEnd_1048433 : Nat := 159511129788267180671363

theorem tailTrace_1048433 : CollatzResearch.WordTrace tailWord_1048433 prefixEnd_1048433 159511129788267180671363 := by
  unfold tailWord_1048433
  simp only [CollatzResearch.WordTrace]
  refine ⟨38239493010713773945965953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25492995340475849297310635 38239493010713773945965953)
  ·
    refine ⟨28679619758035330459474465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38239493010713773945965953 28679619758035330459474465)
    ·
      refine ⟨21509714818526497844605849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28679619758035330459474465 21509714818526497844605849)
      ·
        refine ⟨16132286113894873383454387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21509714818526497844605849 16132286113894873383454387)
        ·
          refine ⟨24198429170842310075181581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16132286113894873383454387 24198429170842310075181581)
          ·
            refine ⟨9074410939065866278193093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24198429170842310075181581 9074410939065866278193093)
            ·
              refine ⟨1701452051074849927161205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9074410939065866278193093 1701452051074849927161205)
              ·
                refine ⟨159511129788267180671363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1701452051074849927161205 159511129788267180671363)
                ·
                  rfl

theorem cell20_1048433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_1048433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048433 prefixEnd_1048433 := by exact prefixLift 1048433
  have htrace : WordTrace (prefixWord ++ tailWord_1048433) baseStart_1048433 baseEnd_1048433 := by
    simpa [prefixWord, tailWord_1048433, baseEnd_1048433] using wordTrace_append hprefix tailTrace_1048433
  have hstable : (prefixWord ++ tailWord_1048433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048433).length < 2 ^ (prefixWord ++ tailWord_1048433).sum := by decide
  have hdescent : baseEnd_1048433 < baseStart_1048433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048447 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_1048447 : Nat := 118140960795 + 1048447 * 2 ^ 59
def prefixEnd_1048447 : Nat := 4983230072969 + 3 ^ 40 * 1048447 * 2
def baseEnd_1048447 : Nat := 478539779346279715547365

theorem tailTrace_1048447 : CollatzResearch.WordTrace tailWord_1048447 prefixEnd_1048447 478539779346279715547365 := by
  unfold tailWord_1048447
  simp only [CollatzResearch.WordTrace]
  refine ⟨38240003632663054336975595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25493335755108702891317063 38240003632663054336975595)
  ·
    refine ⟨57360005448994581505463393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38240003632663054336975595 57360005448994581505463393)
    ·
      refine ⟨43020004086745936129097545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57360005448994581505463393 43020004086745936129097545)
      ·
        refine ⟨32265003065059452096823159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43020004086745936129097545 32265003065059452096823159)
        ·
          refine ⟨48397504597589178145234739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32265003065059452096823159 48397504597589178145234739)
          ·
            refine ⟨72596256896383767217852109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48397504597589178145234739 72596256896383767217852109)
            ·
              refine ⟨27223596336143912706694541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72596256896383767217852109 27223596336143912706694541)
              ·
                refine ⟨10208848626053967265010453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27223596336143912706694541 10208848626053967265010453)
                ·
                  refine ⟨478539779346279715547365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10208848626053967265010453 478539779346279715547365)
                  ·
                    rfl

theorem cell20_1048447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_1048447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048447 prefixEnd_1048447 := by exact prefixLift 1048447
  have htrace : WordTrace (prefixWord ++ tailWord_1048447) baseStart_1048447 baseEnd_1048447 := by
    simpa [prefixWord, tailWord_1048447, baseEnd_1048447] using wordTrace_append hprefix tailTrace_1048447
  have hstable : (prefixWord ++ tailWord_1048447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048447).length < 2 ^ (prefixWord ++ tailWord_1048447).sum := by decide
  have hdescent : baseEnd_1048447 < baseStart_1048447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048474 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_1048474 : Nat := 118140960795 + 1048474 * 2 ^ 59
def prefixEnd_1048474 : Nat := 4983230072969 + 3 ^ 40 * 1048474 * 2
def baseEnd_1048474 : Nat := 478552102881987621647255

theorem tailTrace_1048474 : CollatzResearch.WordTrace tailWord_1048474 prefixEnd_1048474 478552102881987621647255 := by
  unfold tailWord_1048474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9560247100891309487052119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25493992269043491965472317 9560247100891309487052119)
  ·
    refine ⟨14340370651336964230578179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9560247100891309487052119 14340370651336964230578179)
    ·
      refine ⟨21510555977005446345867269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14340370651336964230578179 21510555977005446345867269)
      ·
        refine ⟨4033229245688521189850113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21510555977005446345867269 4033229245688521189850113)
        ·
          refine ⟨3024921934266390892387585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4033229245688521189850113 3024921934266390892387585)
          ·
            refine ⟨2268691450699793169290689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3024921934266390892387585 2268691450699793169290689)
            ·
              refine ⟨1701518588024844876968017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2268691450699793169290689 1701518588024844876968017)
              ·
                refine ⟨1276138941018633657726013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1701518588024844876968017 1276138941018633657726013)
                ·
                  refine ⟨478552102881987621647255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1276138941018633657726013 478552102881987621647255)
                  ·
                    rfl

theorem cell20_1048474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_1048474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048474 prefixEnd_1048474 := by exact prefixLift 1048474
  have htrace : WordTrace (prefixWord ++ tailWord_1048474) baseStart_1048474 baseEnd_1048474 := by
    simpa [prefixWord, tailWord_1048474, baseEnd_1048474] using wordTrace_append hprefix tailTrace_1048474
  have hstable : (prefixWord ++ tailWord_1048474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048474).length < 2 ^ (prefixWord ++ tailWord_1048474).sum := by decide
  have hdescent : baseEnd_1048474 < baseStart_1048474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048477 : List Nat := [1, 4, 2, 1, 2, 4, 2, 2, 2]
def baseStart_1048477 : Nat := 118140960795 + 1048477 * 2 ^ 59
def prefixEnd_1048477 : Nat := 4983230072969 + 3 ^ 40 * 1048477 * 2
def baseEnd_1048477 : Nat := 478553472163732944547243

theorem tailTrace_1048477 : CollatzResearch.WordTrace tailWord_1048477 prefixEnd_1048477 478553472163732944547243 := by
  unfold tailWord_1048477
  simp only [CollatzResearch.WordTrace]
  refine ⟨38241097822554369460567685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25494065215036246307045123 38241097822554369460567685)
  ·
    refine ⟨7170205841728944273856441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38241097822554369460567685 7170205841728944273856441)
    ·
      refine ⟨5377654381296708205392331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7170205841728944273856441 5377654381296708205392331)
      ·
        refine ⟨8066481571945062308088497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5377654381296708205392331 8066481571945062308088497)
        ·
          refine ⟨6049861178958796731066373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8066481571945062308088497 6049861178958796731066373)
          ·
            refine ⟨1134348971054774387074945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6049861178958796731066373 1134348971054774387074945)
            ·
              refine ⟨850761728291080790306209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1134348971054774387074945 850761728291080790306209)
              ·
                refine ⟨638071296218310592729657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850761728291080790306209 638071296218310592729657)
                ·
                  refine ⟨478553472163732944547243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 638071296218310592729657 478553472163732944547243)
                  ·
                    rfl

theorem cell20_1048477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_1048477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048477 prefixEnd_1048477 := by exact prefixLift 1048477
  have htrace : WordTrace (prefixWord ++ tailWord_1048477) baseStart_1048477 baseEnd_1048477 := by
    simpa [prefixWord, tailWord_1048477, baseEnd_1048477] using wordTrace_append hprefix tailTrace_1048477
  have hstable : (prefixWord ++ tailWord_1048477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048477).length < 2 ^ (prefixWord ++ tailWord_1048477).sum := by decide
  have hdescent : baseEnd_1048477 < baseStart_1048477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048485 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_1048485 : Nat := 118140960795 + 1048485 * 2 ^ 59
def prefixEnd_1048485 : Nat := 4983230072969 + 3 ^ 40 * 1048485 * 2
def baseEnd_1048485 : Nat := 478557123581720472280543

theorem tailTrace_1048485 : CollatzResearch.WordTrace tailWord_1048485 prefixEnd_1048485 478557123581720472280543 := by
  unfold tailWord_1048485
  simp only [CollatzResearch.WordTrace]
  refine ⟨38241389606525386826858909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25494259737683591217905939 38241389606525386826858909)
  ·
    refine ⟨14340521102447020060072091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38241389606525386826858909 14340521102447020060072091)
    ·
      refine ⟨21510781653670530090108137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14340521102447020060072091 21510781653670530090108137)
      ·
        refine ⟨16133086240252897567581103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21510781653670530090108137 16133086240252897567581103)
        ·
          refine ⟨24199629360379346351371655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16133086240252897567581103 24199629360379346351371655)
          ·
            refine ⟨36299444040569019527057483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24199629360379346351371655 36299444040569019527057483)
            ·
              refine ⟨54449166060853529290586225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36299444040569019527057483 54449166060853529290586225)
              ·
                refine ⟨40836874545640146967939669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54449166060853529290586225 40836874545640146967939669)
                ·
                  refine ⟨478557123581720472280543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40836874545640146967939669 478557123581720472280543)
                  ·
                    rfl

theorem cell20_1048485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_1048485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048485 prefixEnd_1048485 := by exact prefixLift 1048485
  have htrace : WordTrace (prefixWord ++ tailWord_1048485) baseStart_1048485 baseEnd_1048485 := by
    simpa [prefixWord, tailWord_1048485, baseEnd_1048485] using wordTrace_append hprefix tailTrace_1048485
  have hstable : (prefixWord ++ tailWord_1048485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048485).length < 2 ^ (prefixWord ++ tailWord_1048485).sum := by decide
  have hdescent : baseEnd_1048485 < baseStart_1048485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048523 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_1048523 : Nat := 118140960795 + 1048523 * 2 ^ 59
def prefixEnd_1048523 : Nat := 4983230072969 + 3 ^ 40 * 1048523 * 2
def baseEnd_1048523 : Nat := 478574467817161229013721

theorem tailTrace_1048523 : CollatzResearch.WordTrace tailWord_1048523 prefixEnd_1048523 478574467817161229013721 := by
  unfold tailWord_1048523
  simp only [CollatzResearch.WordTrace]
  refine ⟨38242775580387719316742223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25495183720258479544494815 38242775580387719316742223)
  ·
    refine ⟨57364163370581578975113335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38242775580387719316742223 57364163370581578975113335)
    ·
      refine ⟨86046245055872368462670003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57364163370581578975113335 86046245055872368462670003)
      ·
        refine ⟨129069367583808552694005005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86046245055872368462670003 129069367583808552694005005)
        ·
          refine ⟨48401012843928207260251877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129069367583808552694005005 48401012843928207260251877)
          ·
            refine ⟨9075189908236538861297227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48401012843928207260251877 9075189908236538861297227)
            ·
              refine ⟨13612784862354808291945841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9075189908236538861297227 13612784862354808291945841)
              ·
                refine ⟨10209588646766106218959381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13612784862354808291945841 10209588646766106218959381)
                ·
                  refine ⟨478574467817161229013721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10209588646766106218959381 478574467817161229013721)
                  ·
                    rfl

theorem cell20_1048523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_1048523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048523 prefixEnd_1048523 := by exact prefixLift 1048523
  have htrace : WordTrace (prefixWord ++ tailWord_1048523) baseStart_1048523 baseEnd_1048523 := by
    simpa [prefixWord, tailWord_1048523, baseEnd_1048523] using wordTrace_append hprefix tailTrace_1048523
  have hstable : (prefixWord ++ tailWord_1048523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048523).length < 2 ^ (prefixWord ++ tailWord_1048523).sum := by decide
  have hdescent : baseEnd_1048523 < baseStart_1048523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048533 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 5]
def baseStart_1048533 : Nat := 118140960795 + 1048533 * 2 ^ 59
def prefixEnd_1048533 : Nat := 4983230072969 + 3 ^ 40 * 1048533 * 2
def baseEnd_1048533 : Nat := 478579032089645638680347

theorem tailTrace_1048533 : CollatzResearch.WordTrace tailWord_1048533 prefixEnd_1048533 478579032089645638680347 := by
  unfold tailWord_1048533
  simp only [CollatzResearch.WordTrace]
  refine ⟨38243140310351491024606253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25495426873567660683070835 38243140310351491024606253)
  ·
    refine ⟨14341177616381809134227345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38243140310351491024606253 14341177616381809134227345)
    ·
      refine ⟨10755883212286356850670509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14341177616381809134227345 10755883212286356850670509)
      ·
        refine ⟨4033456204607383819001441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10755883212286356850670509 4033456204607383819001441)
        ·
          refine ⟨3025092153455537864251081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4033456204607383819001441 3025092153455537864251081)
          ·
            refine ⟨2268819115091653398188311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3025092153455537864251081 2268819115091653398188311)
            ·
              refine ⟨3403228672637480097282467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2268819115091653398188311 3403228672637480097282467)
              ·
                refine ⟨5104843008956220145923701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3403228672637480097282467 5104843008956220145923701)
                ·
                  refine ⟨478579032089645638680347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5104843008956220145923701 478579032089645638680347)
                  ·
                    rfl

theorem cell20_1048533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_1048533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048533 prefixEnd_1048533 := by exact prefixLift 1048533
  have htrace : WordTrace (prefixWord ++ tailWord_1048533) baseStart_1048533 baseEnd_1048533 := by
    simpa [prefixWord, tailWord_1048533, baseEnd_1048533] using wordTrace_append hprefix tailTrace_1048533
  have hstable : (prefixWord ++ tailWord_1048533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048533).length < 2 ^ (prefixWord ++ tailWord_1048533).sum := by decide
  have hdescent : baseEnd_1048533 < baseStart_1048533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048546 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_1048546 : Nat := 118140960795 + 1048546 * 2 ^ 59
def prefixEnd_1048546 : Nat := 4983230072969 + 3 ^ 40 * 1048546 * 2
def baseEnd_1048546 : Nat := 478584965643875371246961

theorem tailTrace_1048546 : CollatzResearch.WordTrace tailWord_1048546 prefixEnd_1048546 478584965643875371246961 := by
  unfold tailWord_1048546
  simp only [CollatzResearch.WordTrace]
  refine ⟨9560903614826098561207373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25495742972869596163219661 9560903614826098561207373)
  ·
    refine ⟨3585338855559786960452765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9560903614826098561207373 3585338855559786960452765)
    ·
      refine ⟨1344502070834920110169787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3585338855559786960452765 1344502070834920110169787)
      ·
        refine ⟨2016753106252380165254681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344502070834920110169787 2016753106252380165254681)
        ·
          refine ⟨1512564829689285123941011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2016753106252380165254681 1512564829689285123941011)
          ·
            refine ⟨2268847244533927685911517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512564829689285123941011 2268847244533927685911517)
            ·
              refine ⟨850817716700222882216819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2268847244533927685911517 850817716700222882216819)
              ·
                refine ⟨1276226575050334323325229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850817716700222882216819 1276226575050334323325229)
                ·
                  refine ⟨478584965643875371246961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1276226575050334323325229 478584965643875371246961)
                  ·
                    rfl

theorem cell20_1048546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_1048546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1048546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1048546 prefixEnd_1048546 := by exact prefixLift 1048546
  have htrace : WordTrace (prefixWord ++ tailWord_1048546) baseStart_1048546 baseEnd_1048546 := by
    simpa [prefixWord, tailWord_1048546, baseEnd_1048546] using wordTrace_append hprefix tailTrace_1048546
  have hstable : (prefixWord ++ tailWord_1048546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048546).length < 2 ^ (prefixWord ++ tailWord_1048546).sum := by decide
  have hdescent : baseEnd_1048546 < baseStart_1048546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
